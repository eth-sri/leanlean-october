module

public import Chazelle.Core.RestoreFBits
public import Chazelle.Core.RestoreFEndT
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics

/-!
# WP-E, the search on the RAM (`FindOK`), part 12: the side bit of an end

`endSd s`: when the first test at the end was valid (`s + 5`), `s + 6 := [aⱼ = kE ∨ aⱼ ∈ (kE, kF)]`
for the host keys `kE` of the end `(s + 1, s + 2)`, `kF` of the far position `(s + 3, s + 4)`
and `aⱼ` of the start `(81140, 81141)` of the target arc (`81190 … 81195` scratch).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)

variable {E : FEnv} {c₀ c : Config}

/-- A host position the comparisons accept: in range, proper, and not a box vertex. -/
theorem posG_of_vlo (hE : FGood E c₀) (hI : FInv E.W c₀ c) {e h : ℕ} (he : e < E.M.W.n)
    (hp : ProperPos E.M (Qof E.P) E.P.n ⟨e, h⟩) (hv : 0 < h ∨ c.nreg 81021 ≤ e) :
    PosG E.M (Qof E.P) E.P.n ⟨e, h⟩ := by
  refine ⟨he, hp, fun C hM h0 => ?_⟩
  have := hE.vlo6 C hM
  rw [hI.hin _ (by ufo FFix)] at hv
  simp at h0
  show 6 ≤ e
  omega

/-- The comparisons of the side bit. -/
def endSdC (s : ℕ) : Stmt :=
  .seq (cmpM 81190 (s + 1) (s + 2) (s + 3) (s + 4)) (.seq (cmpM 81192 (s + 1) (s + 2) 81140 81141)
    (.seq (cmpM 81194 81140 81141 (s + 3) (s + 4)) (.seq (side3 (s + 6) 81190 81192 81194)
      (eqor (s + 6) 81192 81193))))

/-- **The side bit of an end.** -/
def endSd (s : ℕ) : Stmt :=
  .seq (Stmt.block [.constN (s + 6) 0])
    (.ifLtN 81011 (s + 5) (.ifLtN 81011 81141 (endSdC s) (.ifLtN 81140 81021 .skip (endSdC s)))
      .skip)

/-- The registers `endSd` writes. -/
def SdW (s q : ℕ) : Prop := KeyW q ∨ q = s + 6 ∨ (81190 ≤ q ∧ q ≤ 81195)

theorem endSdC_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s : ℕ} (hs : 81150 ≤ s ∧ s + 9 < 81190)
    (hxE : PosG E.M (Qof E.P) E.P.n ⟨c.nreg (s + 1), c.nreg (s + 2)⟩)
    (hxF : PosG E.M (Qof E.P) E.P.n ⟨c.nreg (s + 3), c.nreg (s + 4)⟩)
    (hxJ : PosG E.M (Qof E.P) E.P.n ⟨c.nreg 81140, c.nreg 81141⟩)
    (hroom : c.nreg ALLOC + 33080 ≤ E.W) :
    FRS B E.P E.W c₀ (endSdC s) c 33080 (fun c' =>
      BitIs c' (s + 6) (E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩ =
          E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩ ∨
        sideInArc (E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩)
          (E.M.key (Qof E.P) ⟨c.nreg (s + 3), c.nreg (s + 4)⟩)
          (E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩)) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ SdW s q → c'.nreg q = c.nreg q) := by
  obtain ⟨hs1, hs2⟩ := hs
  set kE := E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩
  set kF := E.M.key (Qof E.P) ⟨c.nreg (s + 3), c.nreg (s + 4)⟩
  set kJ := E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩
  have nk : ∀ q, 81100 ≤ q → q < 82000 → ¬ KeyW q := fun q h1 h2 h => by ufo KeyW at h
  have ir : ∀ q, 81100 ≤ q → q < 82000 → InR q := fun q h1 h2 => ⟨by omega, by omega⟩
  refine (FRS.seq (K₂ := 22058) (cmpM_fs hE hB hI (r := 81190) ⟨by norm_num, by norm_num⟩
    (ir _ (by omega) (by omega)) (ir _ (by omega) (by omega)) (ir _ (by omega) (by omega))
    (ir _ (by omega) (by omega)) (nk _ (by omega) (by omega)) (nk _ (by omega) (by omega))
    (nk _ (by omega) (by omega)) (nk _ (by omega) (by omega)) hxE hxF (by omega))
    (fun c₁ hI₁ hA₁ ⟨b0, b1, f₁⟩ => ?_)).mono (by omega) (fun _ => id)
  have g₁ : ∀ q, 81100 ≤ q → q < 81190 → c₁.nreg q = c.nreg q := fun q h1 h2 =>
    f₁ q (by omega) (by omega) (nk q h1 (by omega)) (by omega) (by omega)
  have j₁ : ∀ q, q = 81140 ∨ q = 81141 → c₁.nreg q = c.nreg q := fun q h =>
    g₁ q (by omega) (by omega)
  refine (FRS.seq (K₂ := 11036) (cmpM_fs hE hB hI₁ (r := 81192) ⟨by norm_num, by norm_num⟩
    (ir _ (by omega) (by omega)) (ir _ (by omega) (by omega)) (ir _ (by omega) (by omega))
    (ir _ (by omega) (by omega)) (nk _ (by omega) (by omega)) (nk _ (by omega) (by omega))
    (nk _ (by omega) (by omega)) (nk _ (by omega) (by omega))
    (by rwx [g₁ _ (by omega) (by omega), g₁ _ (by omega) (by omega)])
    (by rwx [j₁ _ (Or.inl rfl), j₁ _ (Or.inr rfl)]) (by omega))
    (fun c₂ hI₂ hA₂ ⟨b2, b3, f₂⟩ => ?_)).mono (by omega) (fun _ => id)
  rw [g₁ (s + 1) (by omega) (by omega), g₁ (s + 2) (by omega) (by omega), j₁ 81140 (Or.inl rfl),
    j₁ 81141 (Or.inr rfl)] at b2 b3
  have g₂ : ∀ q, 81100 ≤ q → q < 81190 → c₂.nreg q = c.nreg q := fun q h1 h2 => by
    rw [f₂ q (by omega) (by omega) (nk q h1 (by omega)) (by omega) (by omega), g₁ q h1 h2]
  refine (FRS.seq (K₂ := 14) (cmpM_fs hE hB hI₂ (r := 81194) ⟨by norm_num, by norm_num⟩
    (ir _ (by omega) (by omega)) (ir _ (by omega) (by omega)) (ir _ (by omega) (by omega))
    (ir _ (by omega) (by omega)) (nk _ (by omega) (by omega)) (nk _ (by omega) (by omega))
    (nk _ (by omega) (by omega)) (nk _ (by omega) (by omega))
    (by rwx [g₂ _ (by omega) (by omega), g₂ _ (by omega) (by omega)])
    (by rwx [g₂ _ (by omega) (by omega), g₂ _ (by omega) (by omega)]) (by omega))
    (fun c₃ hI₃ hA₃ ⟨b4, b5, f₃⟩ => ?_)).mono (by omega) (fun _ => id)
  rw [g₂ 81140 (by omega) (by omega), g₂ 81141 (by omega) (by omega),
    g₂ (s + 3) (by omega) (by omega), g₂ (s + 4) (by omega) (by omega)] at b4 b5
  have p3 : ∀ q, 81190 ≤ q → q ≤ 81193 → c₃.nreg q = c₂.nreg q := fun q h1 h2 =>
    f₃ q (by omega) (by omega) (nk q (by omega) (by omega)) (by omega) (by omega)
  have b0' : BitIs c₃ 81190 (kE < kF) := b0.of_eq (by
    rw [p3 _ (by norm_num) (by norm_num), f₂ _ (by norm_num) (by norm_num)
      (nk _ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)])
  have b2' : BitIs c₃ 81192 (kE < kJ) := b2.of_eq (p3 _ (by norm_num) (by norm_num))
  have b3' : BitIs c₃ 81193 (kJ < kE) := b3.of_eq (p3 _ (by norm_num) (by norm_num))
  refine (FRS.seq (K₂ := 5) (side3_fs hE hB hI₃ (r := s + 6) ⟨by omega, by omega⟩ (by omega)
    (by omega) (by omega) (by omega) b0' b2' b4) (fun c₄ hI₄ hA₄ ⟨b6, f₄⟩ => ?_)).mono
    (by omega) (fun _ => id)
  refine (eqor_fs hE hB hI₄ (r := s + 6) ⟨by omega, by omega⟩ b6
    (b2'.of_eq (f₄ _ (by omega))) (b3'.of_eq (f₄ _ (by omega)))).mono le_rfl
    (fun c₅ ⟨b7, f₅⟩ => ⟨b7.congr ?_, fun q h1 h2 hq => ?_⟩)
  · rw [sideInArc_iff']
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inr h
      · exact Or.inl (le_antisymm (not_lt.1 h1) (not_lt.1 h2))
    · rintro (h | h)
      · exact Or.inr ⟨by rw [h]; exact lt_irrefl _, by rw [h]; exact lt_irrefl _⟩
      · exact Or.inl h
  · have hk : ¬ KeyW q := fun h => hq (Or.inl h)
    have h6 : q ≠ s + 6 := fun h => hq (Or.inr (Or.inl h))
    have h9 : ¬ (81190 ≤ q ∧ q ≤ 81195) := fun h => hq (Or.inr (Or.inr h))
    rw [f₅ q h6, f₄ q h6, f₃ q h1 h2 hk (by omega) (by omega),
      f₂ q h1 h2 hk (by omega) (by omega), f₁ q h1 h2 hk (by omega) (by omega)]

/-- **The side bit of an end** as a run step (guarded by the validity bit and a check that the
target arc's start is a position the comparisons accept). -/
theorem endSd_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s : ℕ} (hs : 81150 ≤ s ∧ s + 9 < 81190) (h5 : c.nreg (s + 5) ≤ 1)
    (hxE : c.nreg (s + 5) = 1 → PosG E.M (Qof E.P) E.P.n ⟨c.nreg (s + 1), c.nreg (s + 2)⟩)
    (hxF : c.nreg (s + 5) = 1 → PosG E.M (Qof E.P) E.P.n ⟨c.nreg (s + 3), c.nreg (s + 4)⟩)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M (Qof E.P) E.P.n ⟨c.nreg 81140, c.nreg 81141⟩)
    (hroom : c.nreg ALLOC + 33087 ≤ E.W) :
    FRS B E.P E.W c₀ (endSd s) c 33087 (fun c' => c'.nreg (s + 6) ≤ 1 ∧
      (c.nreg (s + 5) = 1 → (0 < c.nreg 81141 ∨ c.nreg 81021 ≤ c.nreg 81140) →
        (c'.nreg (s + 6) = 1 ↔ (E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩ =
          E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩ ∨
        sideInArc (E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩)
          (E.M.key (Qof E.P) ⟨c.nreg (s + 3), c.nreg (s + 4)⟩)
          (E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩)))) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ SdW s q → c'.nreg q = c.nreg q) := by
  obtain ⟨hs1, hs2⟩ := hs
  refine (FRS.seq (K₂ := 33086) (setR_fs hB hI (r := s + 6) ⟨by omega, by omega⟩ (Nat.zero_le _))
    (fun c₁ hI₁ hA₁ ⟨v₁, f₁⟩ => ?_)).mono (by omega) (fun _ => id)
  have k0 := k0_of hE hI₁
  have g  := f₁
  have fin : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → ¬ SdW s q → c'.nreg q = c₁.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ SdW s q → c'.nreg q = c.nreg q :=
    fun c' h q h1 h2 h3 => by rw [h q h1 h2 h3, g q (fun e => h3 (Or.inr (Or.inl e)))]
  have run : c.nreg (s + 5) = 1 → (0 < c.nreg 81141 ∨ c.nreg 81021 ≤ c.nreg 81140) →
      FRS B E.P E.W c₀ (endSdC s) c₁ 33080 (fun c' => c'.nreg (s + 6) ≤ 1 ∧
      (c.nreg (s + 5) = 1 → (0 < c.nreg 81141 ∨ c.nreg 81021 ≤ c.nreg 81140) →
        (c'.nreg (s + 6) = 1 ↔ (E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩ =
          E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩ ∨
        sideInArc (E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩)
          (E.M.key (Qof E.P) ⟨c.nreg (s + 3), c.nreg (s + 4)⟩)
          (E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩)))) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ SdW s q → c'.nreg q = c.nreg q) := by
    intro h5' hv
    have r1 := g (s + 1) (by omega)
    have r2 := g (s + 2) (by omega)
    have r3 := g (s + 3) (by omega)
    have r4 := g (s + 4) (by omega)
    have r40 := g 81140 (by omega)
    have r41 := g 81141 (by omega)
    have hJ'  := posG_of_vlo hE hI hJ.1 hJ.2 hv
    refine (endSdC_fs hE hB hI₁ ⟨by omega, hs2⟩ (by rw [r1, r2]; exact hxE h5')
      (by rw [r3, r4]; exact hxF h5') (by rwx [r40, r41])
      (by omega)).mono le_rfl
      (fun c' ⟨b, f⟩ => ⟨b.1, fun _ _ => by rw [← r1, ← r2, ← r3, ← r4, ← r40, ← r41]; exact b.2,
        fin c' f⟩)
  have skip0 : ¬ (c.nreg (s + 5) = 1 ∧ (0 < c.nreg 81141 ∨ c.nreg 81021 ≤ c.nreg 81140)) →
      FRS B E.P E.W c₀ .skip c₁ 0 (fun c' => c'.nreg (s + 6) ≤ 1 ∧
      (c.nreg (s + 5) = 1 → (0 < c.nreg 81141 ∨ c.nreg 81021 ≤ c.nreg 81140) →
        (c'.nreg (s + 6) = 1 ↔ (E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩ =
          E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩ ∨
        sideInArc (E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩)
          (E.M.key (Qof E.P) ⟨c.nreg (s + 3), c.nreg (s + 4)⟩)
          (E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩)))) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ SdW s q → c'.nreg q = c.nreg q) := fun hn =>
    FRS.skip hI₁ ⟨by omega, fun a b => absurd ⟨a, b⟩ hn, fin c₁ (fun _ _ _ _ => rfl)⟩
  have q5 := g (s + 5) (by omega)
  have q40 := g 81140 (by omega)
  have q41 := g 81141 (by omega)
  have q21 : c₁.nreg 81021 = c.nreg 81021 := g 81021 (by omega)
  by_cases a1 : c₁.nreg 81011 < c₁.nreg (s + 5)
  · have h51 : c.nreg (s + 5) = 1 := by rwo [k0, q5] at a1
    refine (FRS.ifT a1 ?_).mono (K := 33086) le_rfl (fun _ => id)
    by_cases a2 : c₁.nreg 81011 < c₁.nreg 81141
    · exact (FRS.ifT a2 (run h51 (Or.inl (by rw [k0, q41] at a2; exact a2)))).mono (by omega)
        (fun _ => id)
    refine (FRS.ifF a2 ?_).mono (K := 33084) (by omega) (fun _ => id)
    by_cases a3 : c₁.nreg 81140 < c₁.nreg 81021
    · exact (FRS.ifT a3 (skip0 (fun ⟨_, h⟩ => by
        rw [k0, q41] at a2; rwo [q40, q21] at a3))).mono (by omega) (fun _ => id)
    · exact (FRS.ifF a3 (run h51 (Or.inr (by rwo [q40, q21] at a3)))).mono (by omega)
        (fun _ => id)
  · exact (FRS.ifF a1 (skip0 (fun ⟨h, _⟩ => by rwo [k0, q5] at a1))).mono (by omega)
      (fun _ => id)

end

end Restore

end Chazelle.Core
