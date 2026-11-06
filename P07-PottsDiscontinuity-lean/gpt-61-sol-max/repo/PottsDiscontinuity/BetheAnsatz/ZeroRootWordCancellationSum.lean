module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordCancellation

/-!
# Cancellation on a fixed zero-root slot

For a fixed word and a fixed slot occupied by the perturbed root, every ML edge
disjoint from that slot pairs the constrained permutation sum with its negative.
-/

@[expose] public section



namespace PottsDiscontinuity.BetheAnsatz

/-- Permutations which place the distinguished label at a fixed slot. -/
abbrev RootSlotPerm {n : ℕ} (l r : Fin (n + 1)) :=
  {σ : Equiv.Perm (Fin (n + 1)) // σ r = l}

/-- A transposition away from the root slot preserves the constrained
permutation fiber and is an involution on it. -/
theorem sum_fixedAmplitudeWordTerm_eq_zero_of_ML_away {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (hn : 0 < n)
    (p q : Fin (n + 1) → ℝ)
    (x : Fin (n + 1) → ℤ) (l r a : Fin (n + 1))
    (w : Fin (n + 1) → Bool)
    (hBE : BetheEquations N (anisotropy c) p)
    (hAgree : ∀ k, k ≠ l → q k = p k)
    (hNotOne : ∀ k, k ≠ l → z (p k) ≠ 1)
    (ha : w a = false) (hb : w (finRotate (n + 1) a) = true)
    (hra : r ≠ a) (hrb : r ≠ finRotate (n + 1) a) :
     ∑ σ : RootSlotPerm l r,
      fixedAmplitudeWordTerm (N := N) c x p q σ.1 w  = 0 := by
  
  let b := finRotate (n + 1) a
  have hswapRoot (σ : RootSlotPerm l r) : (σ.1 * Equiv.swap a b) r = l := by
    aesop
  let e : RootSlotPerm l r ≃ RootSlotPerm l r := {
    toFun := fun σ => ⟨σ.1 * Equiv.swap a b, hswapRoot σ⟩
    invFun := fun σ => ⟨σ.1 * Equiv.swap a b, hswapRoot σ⟩
    left_inv := by
      intro σ
      
      
      simp
    right_inv := by
      intro σ
      
      
      simp }
  have hslot (σ : RootSlotPerm l r) (k : Fin (n + 1)) (hk : k ≠ r) :
      σ.1 k ≠ l := by
    aesop
  have hcancel (σ : RootSlotPerm l r) :
      fixedAmplitudeWordTerm (N := N) c x p q (e σ).1 w =
        -fixedAmplitudeWordTerm (N := N) c x p q σ.1 w := by
    have hσa := hslot σ a hra.symm
    have hσb := hslot σ b hrb.symm
    have hqa  := hAgree _ hσa
    have hqb  := hAgree _ hσb
    by_cases hseam : a = Fin.last n
    · subst a
      have hlast : b = 0 := by simp [b]
      have hha  := ha
      
      have hσ0  := hslot σ 0 (by
        simpa  using hrb.symm)
      
      have hleft := fixedAmplitudeWordTerm_seam_swap hc p q x hBE σ.1 w hn
        hha (by simpa [finRotate_last] using hb) hqa (hAgree _ hσ0) (hNotOne _ hσa) (hNotOne _ hσ0)
      simpa [e, hlast] using hleft
    · obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hseam
      
      have hb' : b = j.succ := by
        aesop
      
      
      
      
      
      
      have hleft := fixedAmplitudeWordTerm_adjacent_swap (N := N) hc p q x σ.1 w j
        (by simpa [hj] using ha) (by
               rw [← hb']
               exact hb) (by
                   simpa [hj] using hqa) (by
                        simpa [hb'] using hqb) (by
                             simpa [hj] using hNotOne _ hσa) (by
                                  simpa [hb'] using hNotOne _ hσb)
      change fixedAmplitudeWordTerm (N := N) c x p q
        (σ.1 * Equiv.swap a b) w = _
      rw [← hj, hb']
      exact hleft
  let f : RootSlotPerm l r → ℂ := fun σ =>
    fixedAmplitudeWordTerm (N := N) c x p q σ.1 w
  have hEq  := (Equiv.sum_comp e f).symm
  dsimp only [f] at hEq
  simp_rw [hcancel] at hEq
  rw [Finset.sum_neg_distrib] at hEq
  linear_combination  1 / 2  * hEq

end PottsDiscontinuity.BetheAnsatz
