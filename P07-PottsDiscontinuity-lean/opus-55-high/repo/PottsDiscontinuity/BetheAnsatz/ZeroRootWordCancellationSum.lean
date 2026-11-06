module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordCancellation

/-!
# Cancellation on a fixed zero-root slot

For a fixed word and a fixed slot occupied by the perturbed root, every ML edge
disjoint from that slot pairs the constrained permutation sum with its negative.
-/

public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Permutations which place the distinguished label at a fixed slot. -/
abbrev RootSlotPerm {n : ℕ} (l r : Fin (n + 1)) :=
  {σ : Equiv.Perm (Fin (n + 1)) // σ r = l}

/-- A transposition away from the root slot preserves the constrained
permutation fiber and is an involution on it. -/
theorem sum_fixedAmplitudeWordTerm_eq_zero_of_ML_away {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (hn : 0 < n)
    (p : Fin (n + 1) → ℝ) (q : Fin (n + 1) → ℝ)
    (x : Fin (n + 1) → ℤ) (l r a : Fin (n + 1))
    (w : Fin (n + 1) → Bool)
    (hBE : BetheEquations N (anisotropy c) p)
    (hAgree : ∀ k, k ≠ l → q k = p k)
    (hNotOne : ∀ k, k ≠ l → z (p k) ≠ 1)
    (ha : w a = false) (hb : w (finRotate (n + 1) a) = true)
    (hra : r ≠ a) (hrb : r ≠ finRotate (n + 1) a) :
    (∑ σ : RootSlotPerm l r,
      fixedAmplitudeWordTerm (N := N) c x p q σ.1 w) = 0 := by
  let b := finRotate (n + 1) a
  have hswapRoot (σ : RootSlotPerm l r) : (σ.1 * Equiv.swap a b) r = l := by aesop
  let e : RootSlotPerm l r ≃ RootSlotPerm l r :=
    ⟨fun σ => ⟨_, hswapRoot σ⟩, fun σ => ⟨_, hswapRoot σ⟩, fun σ => by simp, fun σ => by simp⟩
  have hcancel (σ : RootSlotPerm l r) :
      fixedAmplitudeWordTerm (N := N) c x p q (e σ).1 w =
        -fixedAmplitudeWordTerm (N := N) c x p q σ.1 w := by
    have hσa : σ.1 a ≠ l := by aesop
    have hσb : σ.1 b ≠ l := by aesop
    by_cases hseam : a = Fin.last n
    · subst a
      have hlast : b = 0 := by simp [b]
      have hσ0 : σ.1 0 ≠ l := by grind
      simpa [e, hlast] using fixedAmplitudeWordTerm_seam_swap hc p q x hBE σ.1 w hn
        ha (by grind) (hAgree _ hσa) (hAgree _ hσ0) (hNotOne _ hσa) (hNotOne _ hσ0)
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hseam
      have hb' : b = j.succ := finRotate_of_lt j.isLt
      rw [hb'] at hσb
      simpa [e, hb'] using fixedAmplitudeWordTerm_adjacent_swap hc p q x σ.1 w j
        ha (by grind) (hAgree _ hσa) (hAgree _ hσb) (hNotOne _ hσa) (hNotOne _ hσb)
  have hEq := (Equiv.sum_comp e fun σ => fixedAmplitudeWordTerm (N := N) c x p q σ.1 w).symm
  simp only [hcancel, Finset.sum_neg_distrib] at hEq
  linear_combination (1 / 2 : ℂ) * hEq

end PottsDiscontinuity.BetheAnsatz
