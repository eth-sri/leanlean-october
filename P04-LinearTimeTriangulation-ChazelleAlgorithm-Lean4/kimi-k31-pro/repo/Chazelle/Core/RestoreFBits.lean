module

public import Chazelle.Core.RestoreFEnd
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics

/-!
# WP-E, the search on the RAM (`FindOK`), part 11: bit logic

Bits in registers (`BitIs`): `side3 r i j k` (`r := if [i] then [j] ∧ [k] else [j] ∨ [k]`, the
cyclic interval test from three comparisons), `eqor r i j` (`r := [r] ∨ (¬[i] ∧ ¬[j])`, adding
the equality case), `xnorR r i j` (`r := ([i] ↔ [j])`), `andR r i j` (`r := [i] ∧ [j]`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)

variable {E : FEnv} {c₀ c : Config}

theorem sideInArc_iff' (a b x : ℝ) :
    sideInArc a b x ↔ (a < b ∧ (a < x ∧ x < b)) ∨ (¬ a < b ∧ (a < x ∨ x < b)) := by
  unfold sideInArc; split_ifs with h <;> simp [h]

/-- `r := if [i] then [j] ∧ [k] else [j] ∨ [k]`. -/
def side3 (r i j k : ℕ) : Stmt :=
  .seq (Stmt.block [.constN r 0])
    (.ifLtN 81011 i (.ifLtN 81011 j (.ifLtN 81011 k (Stmt.block [.constN r 1]) .skip) .skip)
      (.ifLtN 81011 j (Stmt.block [.constN r 1])
        (.ifLtN 81011 k (Stmt.block [.constN r 1]) .skip)))

/-- A bit routine's frame. -/
def BitFr (r : ℕ) (c c' : Config) : Prop := ∀ q, q ≠ r → c'.nreg q = c.nreg q

theorem k0_of (hE : FGood E c₀) (hI : FInv E.W c₀ c) : c.nreg 81011 = 0 := by
  rw [hI.hin _ (by ufo FFix), hE.k0]

theorem side3_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r i j k : ℕ} (hr : SReg r) (hri : r ≠ i) (hrj : r ≠ j) (hrk : r ≠ k) (_hr11 : r ≠ 81011)
    {p q s : Prop} (hi : BitIs c i p) (hj : BitIs c j q) (hk : BitIs c k s) :
    FRS B E.P E.W c₀ (side3 r i j k) c 8 (fun c' =>
      BitIs c' r ((p ∧ (q ∧ s)) ∨ (¬ p ∧ (q ∨ s))) ∧ BitFr r c c') := by
  have hW1 : 1 ≤ E.W := by have := hE.hWh; ufo hostWords at this
  refine (FRS.seq (K₂ := 7) (setR_fs hB hI hr (Nat.zero_le _)) (fun c₁ hI₁ _ ⟨v₁, f₁⟩ => ?_)).mono
    (by omega) (fun _ => id)
  have k0 := k0_of hE hI₁
  have bi  := hi.of_eq (f₁ i (Ne.symm hri))
  have bj  := hj.of_eq (f₁ j (Ne.symm hrj))
  have bk  := hk.of_eq (f₁ k (Ne.symm hrk))
  have nil : ¬ ((p ∧ (q ∧ s)) ∨ (¬ p ∧ (q ∨ s))) →
      FRS B E.P E.W c₀ .skip c₁ 0 (fun c' => BitIs c' r ((p ∧ (q ∧ s)) ∨ (¬ p ∧ (q ∨ s))) ∧
        BitFr r c c') := fun hn => FRS.skip hI₁ ⟨BitIs.const_zero v₁ hn, f₁⟩
  have one : ((p ∧ (q ∧ s)) ∨ (¬ p ∧ (q ∨ s))) →
      FRS B E.P E.W c₀ (Stmt.block [.constN r 1]) c₁ 1 (fun c' =>
        BitIs c' r ((p ∧ (q ∧ s)) ∨ (¬ p ∧ (q ∨ s))) ∧ BitFr r c c') := fun hy =>
    (setR_fs hB hI₁ hr hW1).mono le_rfl (fun c' ⟨v, f⟩ =>
      ⟨BitIs.const_one v hy, fun x hx => (f x hx).trans (f₁ x hx)⟩)
  have b1 : ∀ {x : ℕ} {P : Prop}, BitIs c₁ x P → (c₁.nreg 81011 < c₁.nreg x ↔ P) :=
    fun h => by rw [k0]; exact ⟨fun h' => h.2.1 (by have := h.1; omega),
      fun h' => by rwo [h.2.2 h']⟩
  by_cases a1 : c₁.nreg 81011 < c₁.nreg i
  · have hp := (b1 bi).1 a1
    refine (FRS.ifT a1 ?_).mono (K := 7) le_rfl (fun _ => id)
    by_cases a2 : c₁.nreg 81011 < c₁.nreg j
    · have hq := (b1 bj).1 a2
      refine (FRS.ifT a2 ?_).mono (K := 5) (by omega) (fun _ => id)
      by_cases a3 : c₁.nreg 81011 < c₁.nreg k
      · exact (FRS.ifT a3 (one (Or.inl ⟨hp, hq, (b1 bk).1 a3⟩))).mono (by omega) (fun _ => id)
      · exact (FRS.ifF a3 (nil (fun h => by
          rcases h with h | h
          · exact a3 ((b1 bk).2 h.2.2)
          · exact h.1 hp))).mono (by omega) (fun _ => id)
    · exact (FRS.ifF a2 (nil (fun h => by
        rcases h with h | h
        · exact a2 ((b1 bj).2 h.2.1)
        · exact h.1 hp))).mono (by omega) (fun _ => id)
  · have hp : ¬ p := fun h => a1 ((b1 bi).2 h)
    refine (FRS.ifF a1 ?_).mono (K := 7) le_rfl (fun _ => id)
    by_cases a2 : c₁.nreg 81011 < c₁.nreg j
    · exact (FRS.ifT a2 (one (Or.inr ⟨hp, Or.inl ((b1 bj).1 a2)⟩))).mono (by omega)
        (fun _ => id)
    refine (FRS.ifF a2 ?_).mono (K := 5) le_rfl (fun _ => id)
    by_cases a3 : c₁.nreg 81011 < c₁.nreg k
    · exact (FRS.ifT a3 (one (Or.inr ⟨hp, Or.inr ((b1 bk).1 a3)⟩))).mono (by omega)
        (fun _ => id)
    · exact (FRS.ifF a3 (nil (fun h => by
        rcases h with h | ⟨-, h | h⟩
        · exact hp h.1
        · exact a2 ((b1 bj).2 h)
        · exact a3 ((b1 bk).2 h)))).mono (by omega) (fun _ => id)

/-- `r := [r] ∨ (¬[i] ∧ ¬[j])`. -/
def eqor (r i j : ℕ) : Stmt := .ifLtN 81011 i .skip (.ifLtN 81011 j .skip (Stmt.block [.constN r 1]))

theorem eqor_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r i j : ℕ} (hr : SReg r) {p q s : Prop} (hrr : BitIs c r s) (hi : BitIs c i p)
    (hj : BitIs c j q) :
    FRS B E.P E.W c₀ (eqor r i j) c 5 (fun c' => BitIs c' r (s ∨ (¬ p ∧ ¬ q)) ∧ BitFr r c c') := by
  have hW1 : 1 ≤ E.W := by have := hE.hWh; ufo hostWords at this
  have k0 := k0_of hE hI
  have b1 : ∀ {x : ℕ} {P : Prop}, BitIs c x P → (c.nreg 81011 < c.nreg x ↔ P) :=
    fun h => by rw [k0]; exact ⟨fun h' => h.2.1 (by have := h.1; omega),
      fun h' => by rwo [h.2.2 h']⟩
  by_cases a1 : c.nreg 81011 < c.nreg i
  · exact (FRS.ifT a1 (FRS.skip (K := 0) hI ⟨hrr.congr ⟨Or.inl, fun h => h.resolve_right
      (fun h' => h'.1 ((b1 hi).1 a1))⟩, fun _ _ => rfl⟩)).mono (by omega) (fun _ => id)
  refine (FRS.ifF a1 ?_).mono (K := 5) le_rfl (fun _ => id)
  by_cases a2 : c.nreg 81011 < c.nreg j
  · exact (FRS.ifT a2 (FRS.skip (K := 0) hI ⟨hrr.congr ⟨Or.inl, fun h => h.resolve_right
      (fun h' => h'.2 ((b1 hj).1 a2))⟩, fun _ _ => rfl⟩)).mono (by omega) (fun _ => id)
  · exact (FRS.ifF a2 ((setR_fs hB hI hr hW1).mono le_rfl (fun c' ⟨v, f⟩ =>
      ⟨BitIs.const_one v (Or.inr ⟨fun h => a1 ((b1 hi).2 h), fun h => a2 ((b1 hj).2 h)⟩), f⟩))).mono
      (by omega) (fun _ => id)

/-- `r := ([i] ↔ [j])`. -/
def xnorR (r i j : ℕ) : Stmt :=
  .seq (Stmt.block [.constN r 0])
    (.ifLtN 81011 i (.ifLtN 81011 j (Stmt.block [.constN r 1]) .skip)
      (.ifLtN 81011 j .skip (Stmt.block [.constN r 1])))

theorem xnorR_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r i j : ℕ} (hr : SReg r) (hri : r ≠ i) (hrj : r ≠ j) {p q : Prop} (hi : BitIs c i p)
    (hj : BitIs c j q) :
    FRS B E.P E.W c₀ (xnorR r i j) c 6 (fun c' => BitIs c' r (p ↔ q) ∧ BitFr r c c') := by
  have hW1 : 1 ≤ E.W := by have := hE.hWh; ufo hostWords at this
  refine (FRS.seq (K₂ := 5) (setR_fs hB hI hr (Nat.zero_le _)) (fun c₁ hI₁ _ ⟨v₁, f₁⟩ => ?_)).mono
    (by omega) (fun _ => id)
  have k0 := k0_of hE hI₁
  have bi  := hi.of_eq (f₁ i (Ne.symm hri))
  have bj  := hj.of_eq (f₁ j (Ne.symm hrj))
  have b1 : ∀ {x : ℕ} {P : Prop}, BitIs c₁ x P → (c₁.nreg 81011 < c₁.nreg x ↔ P) :=
    fun h => by rw [k0]; exact ⟨fun h' => h.2.1 (by have := h.1; omega),
      fun h' => by rwo [h.2.2 h']⟩
  have one : (p ↔ q) → FRS B E.P E.W c₀ (Stmt.block [.constN r 1]) c₁ 1 (fun c' =>
      BitIs c' r (p ↔ q) ∧ BitFr r c c') := fun hy =>
    (setR_fs hB hI₁ hr hW1).mono le_rfl (fun c' ⟨v, f⟩ =>
      ⟨BitIs.const_one v hy, fun x hx => (f x hx).trans (f₁ x hx)⟩)
  have nil : ¬ (p ↔ q) → FRS B E.P E.W c₀ .skip c₁ 0 (fun c' => BitIs c' r (p ↔ q) ∧
      BitFr r c c') := fun hn => FRS.skip hI₁ ⟨BitIs.const_zero v₁ hn, f₁⟩
  by_cases a1 : c₁.nreg 81011 < c₁.nreg i
  · have hp := (b1 bi).1 a1
    refine (FRS.ifT a1 ?_).mono (K := 5) le_rfl (fun _ => id)
    by_cases a2 : c₁.nreg 81011 < c₁.nreg j
    · exact (FRS.ifT a2 (one ⟨fun _ => (b1 bj).1 a2, fun _ => hp⟩)).mono (by omega)
        (fun _ => id)
    · exact (FRS.ifF a2 (nil (fun h => a2 ((b1 bj).2 (h.1 hp))))).mono (by omega) (fun _ => id)
  · have hp : ¬ p := fun h => a1 ((b1 bi).2 h)
    refine (FRS.ifF a1 ?_).mono (K := 5) le_rfl (fun _ => id)
    by_cases a2 : c₁.nreg 81011 < c₁.nreg j
    · exact (FRS.ifT a2 (nil (fun h => hp (h.2 ((b1 bj).1 a2))))).mono (by omega) (fun _ => id)
    · exact (FRS.ifF a2 (one ⟨fun h => absurd h hp, fun h => absurd ((b1 bj).2 h) a2⟩)).mono
        (by omega) (fun _ => id)

/-- `r := [i] ∧ [j]`. -/
def andR (r i j : ℕ) : Stmt :=
  .seq (Stmt.block [.constN r 0])
    (.ifLtN 81011 i (.ifLtN 81011 j (Stmt.block [.constN r 1]) .skip) .skip)

theorem andR_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r i j : ℕ} (hr : SReg r) (hri : r ≠ i) (hrj : r ≠ j) {p q : Prop} (hi : BitIs c i p)
    (hj : BitIs c j q) :
    FRS B E.P E.W c₀ (andR r i j) c 6 (fun c' => BitIs c' r (p ∧ q) ∧ BitFr r c c') := by
  have hW1 : 1 ≤ E.W := by have := hE.hWh; ufo hostWords at this
  refine (FRS.seq (K₂ := 5) (setR_fs hB hI hr (Nat.zero_le _)) (fun c₁ hI₁ _ ⟨v₁, f₁⟩ => ?_)).mono
    (by omega) (fun _ => id)
  have k0 := k0_of hE hI₁
  have bi  := hi.of_eq (f₁ i (Ne.symm hri))
  have bj  := hj.of_eq (f₁ j (Ne.symm hrj))
  have b1 : ∀ {x : ℕ} {P : Prop}, BitIs c₁ x P → (c₁.nreg 81011 < c₁.nreg x ↔ P) :=
    fun h => by rw [k0]; exact ⟨fun h' => h.2.1 (by have := h.1; omega),
      fun h' => by rwo [h.2.2 h']⟩
  have nil : ¬ (p ∧ q) → FRS B E.P E.W c₀ .skip c₁ 0 (fun c' => BitIs c' r (p ∧ q) ∧
      BitFr r c c') := fun hn => FRS.skip hI₁ ⟨BitIs.const_zero v₁ hn, f₁⟩
  by_cases a1 : c₁.nreg 81011 < c₁.nreg i
  · refine (FRS.ifT a1 ?_).mono (K := 5) le_rfl (fun _ => id)
    by_cases a2 : c₁.nreg 81011 < c₁.nreg j
    · exact (FRS.ifT a2 ((setR_fs hB hI₁ hr hW1).mono le_rfl (fun c' ⟨v, f⟩ =>
        ⟨BitIs.const_one v ⟨(b1 bi).1 a1, (b1 bj).1 a2⟩, fun x hx => (f x hx).trans
          (f₁ x hx)⟩))).mono (by omega) (fun _ => id)
    · exact (FRS.ifF a2 (nil (fun h => a2 ((b1 bj).2 h.2)))).mono (by omega) (fun _ => id)
  · exact (FRS.ifF a1 (nil (fun h => a1 ((b1 bi).2 h.1)))).mono (by omega) (fun _ => id)

end

end Restore

end Chazelle.Core
