module

public import PottsDiscontinuity.Bethe.DiscreteJacobian

/-! # Explicit coordinates on the symmetric root subspace -/

@[expose] public section

open scoped BigOperators

namespace PottsDiscontinuity.Bethe

section
variable (n : ℕ)
/-- Linear extension of the first-half coordinates in the source basis. -/
noncomputable def discreteSymLift  : (Fin (n / 2) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun q := ∑ j, q j • discreteSymBasis n j
  map_add' q r := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c q := by simp [mul_smul, Finset.smul_sum]

@[simp]
theorem discreteSymLift_half (q : Fin (n / 2) → ℝ) (i : Fin (n / 2)) :
    discreteSymLift n q (discreteHalfIndex n i) = q i := by
  simp [discreteSymLift, Finset.sum_apply, discreteSymBasis_at_half]

@[simp]
theorem discreteSymLift_single (i : Fin (n / 2)) :
    discreteSymLift n (Pi.single i 1) = discreteSymBasis n i := by
  simp [discreteSymLift, Pi.single_apply, ite_smul, Finset.sum_ite_eq']

theorem discreteSymLift_mem (q : Fin (n / 2) → ℝ) :
    discreteSymLift n q ∈ R_n_sym n := by
  change (∑ j, q j • discreteSymBasis n j) ∈ R_n_sym n
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (discreteSymBasis_mem_R_n_sym j)
end

section
variable {n : ℕ}
/-- First-half coordinates determine a symmetric vector, including its middle
coordinate when the number of roots is odd. -/
theorem discreteSym_ext {p q : Fin n → ℝ}
    (hp : p ∈ R_n_sym n) (hq : q ∈ R_n_sym n)
    (h : ∀ i : Fin (n / 2), p (discreteHalfIndex n i) = q (discreteHalfIndex n i)) :
    p = q := by
  funext j
  by_cases hj : j.val < n / 2
  · exact h ⟨j.val, hj⟩
  · by_cases hr : (Fin.rev j).val < n / 2
    · have he := h ⟨(Fin.rev j).val, hr⟩
      change p (Fin.rev j) = q (Fin.rev j) at he
      rw [hp j, hq j] at he
      linarith
    · have hpj := hp j
      have hqj := hq j
      grind

@[simp]
theorem discreteSymLift_coordinates (p : Fin n → ℝ) (hp : p ∈ R_n_sym n) :
    discreteSymLift n (fun i => p (discreteHalfIndex n i)) = p := by
  apply discreteSym_ext (discreteSymLift_mem _ _) hp
  intro i
  exact discreteSymLift_half _ _ _
end

end PottsDiscontinuity.Bethe
