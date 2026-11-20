module

public import Chazelle.Core.RestoreFEnd

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
  rw [hI.hin _ (by unfold FFix; omega), hE.k0]

/-- Run a register comparison as a case split on the proposition represented by the bit. -/
private theorem bitBranch {B : Finset ℕ} {i kt kf : ℕ} {p : Prop} {t f : Stmt} {Q : Config → Prop}
    (hz : c.nreg 81011 = 0) (hi : BitIs c i p)
    (ht : p → FRS B E.P E.W c₀ t c kt Q) (hf : ¬ p → FRS B E.P E.W c₀ f c kf Q) :
    FRS B E.P E.W c₀ (.ifLtN 81011 i t f) c (max (kt + 2) (kf + 2)) Q := by
  have hbit : c.nreg 81011 < c.nreg i ↔ p := by
    rw [hz, ← hi.2]
    have := hi.1
    omega
  by_cases h : c.nreg 81011 < c.nreg i
  · exact (FRS.ifT h (ht (hbit.mp h))).budget (le_max_left ..)
  · exact (FRS.ifF h (hf (fun hp => h (hbit.mpr hp)))).budget (le_max_right ..)

/-- After initialization, paths producing a true bit write one; false paths do nothing. -/
private theorem initGate {B : Finset ℕ} {r k : ℕ} {s : Stmt} {p : Prop}
    (hE : FGood E c₀) (hB : dBands ⊆ B) (hI : FInv E.W c₀ c) (hr : SReg r)
    (run : ∀ d, FInv E.W c₀ d → BitFr r c d →
      (p → FRS B E.P E.W c₀ (Stmt.block [.constN r 1]) d 1 (fun e => BitIs e r p ∧ BitFr r c e)) →
      (¬ p → FRS B E.P E.W c₀ .skip d 0 (fun e => BitIs e r p ∧ BitFr r c e)) →
      FRS B E.P E.W c₀ s d k (fun e => BitIs e r p ∧ BitFr r c e)) :
    FRS B E.P E.W c₀ (.seq (Stmt.block [.constN r 0]) s) c (1 + k)
      (fun e => BitIs e r p ∧ BitFr r c e) := by
  have hW : 1 ≤ E.W := by have := hE.hWh; reg_omega
  refine FRS.seq (setR_fs hB hI hr (Nat.zero_le _)) (fun d hd _ ⟨zero, frame⟩ => run d hd frame ?_ ?_)
  · intro hp
    exact (setR_fs hB hd hr hW).mono le_rfl (fun e ⟨one, hf⟩ =>
      ⟨BitIs.const_one one hp, fun x hx => (hf x hx).trans (frame x hx)⟩)
  · exact fun hn => FRS.skip hd ⟨BitIs.const_zero zero hn, frame⟩

section

variable (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)

include hE hB hI in
theorem side3_fs
    {r i j k : ℕ} (hr : SReg r) (hri : r ≠ i) (hrj : r ≠ j) (hrk : r ≠ k) (_hr11 : r ≠ 81011)
    {p q s : Prop} (hi : BitIs c i p) (hj : BitIs c j q) (hk : BitIs c k s) :
    FRS B E.P E.W c₀ (side3 r i j k) c 8 (fun c' =>
      BitIs c' r ((p ∧ (q ∧ s)) ∨ (¬ p ∧ (q ∨ s))) ∧ BitFr r c c') := by
  refine initGate (k := 7) hE hB hI hr (fun d hd F one nil => ?_)
  have z := k0_of hE hd
  have bi := hi.of_eq (F i hri.symm)
  have bj := hj.of_eq (F j hrj.symm)
  have bk := hk.of_eq (F k hrk.symm)
  exact bitBranch z bi
    (fun hp => bitBranch z bj
      (fun hq => bitBranch z bk (fun hs => one (by tauto)) (fun hs => nil (by tauto)))
      (fun hq => nil (by tauto)))
    (fun hp => bitBranch z bj (fun hq => one (by tauto))
      (fun hq => bitBranch z bk (fun hs => one (by tauto)) (fun hs => nil (by tauto))))

/-- `r := [r] ∨ (¬[i] ∧ ¬[j])`. -/
def eqor (r i j : ℕ) : Stmt := .ifLtN 81011 i .skip (.ifLtN 81011 j .skip (Stmt.block [.constN r 1]))

include hE hB hI in
theorem eqor_fs
    {r i j : ℕ} (hr : SReg r) {p q s : Prop} (hrr : BitIs c r s) (hi : BitIs c i p)
    (hj : BitIs c j q) :
    FRS B E.P E.W c₀ (eqor r i j) c 5 (fun c' => BitIs c' r (s ∨ (¬ p ∧ ¬ q)) ∧ BitFr r c c') := by
  have z := k0_of hE hI
  have hW : 1 ≤ E.W := by have := hE.hWh; reg_omega
  have stay (hs : s ↔ s ∨ (¬ p ∧ ¬ q)) :
      FRS B E.P E.W c₀ .skip c 0 (fun e => BitIs e r (s ∨ (¬ p ∧ ¬ q)) ∧ BitFr r c e) :=
    FRS.skip hI ⟨hrr.congr hs, fun _ _ => rfl⟩
  exact bitBranch z hi (fun hp => stay (by tauto)) fun hp =>
    bitBranch z hj (fun hq => stay (by tauto)) fun hq =>
      (setR_fs hB hI hr hW).mono le_rfl (fun e ⟨one, f⟩ => ⟨BitIs.const_one one (by tauto), f⟩)

/-- `r := ([i] ↔ [j])`. -/
def xnorR (r i j : ℕ) : Stmt :=
  .seq (Stmt.block [.constN r 0])
    (.ifLtN 81011 i (.ifLtN 81011 j (Stmt.block [.constN r 1]) .skip)
      (.ifLtN 81011 j .skip (Stmt.block [.constN r 1])))

include hE hB hI in
theorem xnorR_fs
    {r i j : ℕ} (hr : SReg r) (hri : r ≠ i) (hrj : r ≠ j) {p q : Prop} (hi : BitIs c i p)
    (hj : BitIs c j q) :
    FRS B E.P E.W c₀ (xnorR r i j) c 6 (fun c' => BitIs c' r (p ↔ q) ∧ BitFr r c c') := by
  refine initGate (k := 5) hE hB hI hr (fun d hd F one nil => ?_)
  have z := k0_of hE hd
  have bj := hj.of_eq (F j hrj.symm)
  exact bitBranch z (hi.of_eq (F i hri.symm))
    (fun hp => bitBranch z bj (fun hq => one (by tauto)) (fun hq => nil (by tauto)))
    (fun hp => bitBranch z bj (fun hq => nil (by tauto)) (fun hq => one (by tauto)))

/-- `r := [i] ∧ [j]`. -/
def andR (r i j : ℕ) : Stmt :=
  .seq (Stmt.block [.constN r 0])
    (.ifLtN 81011 i (.ifLtN 81011 j (Stmt.block [.constN r 1]) .skip) .skip)

include hE hB hI in
theorem andR_fs
    {r i j : ℕ} (hr : SReg r) (hri : r ≠ i) (hrj : r ≠ j) {p q : Prop} (hi : BitIs c i p)
    (hj : BitIs c j q) :
    FRS B E.P E.W c₀ (andR r i j) c 6 (fun c' => BitIs c' r (p ∧ q) ∧ BitFr r c c') := by
  refine initGate (k := 5) hE hB hI hr (fun d hd F one nil => ?_)
  have z := k0_of hE hd
  exact bitBranch z (hi.of_eq (F i hri.symm))
    (fun hp => bitBranch z (hj.of_eq (F j hrj.symm))
      (fun hq => one ⟨hp, hq⟩) (fun hq => nil (by tauto)))
    (fun hp => nil (by tauto))

end

end

end Restore

end Chazelle.Core
