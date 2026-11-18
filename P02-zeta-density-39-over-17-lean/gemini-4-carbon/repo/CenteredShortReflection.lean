module
public import RationalDyadicDifference
public import GuthMaynard.Improvement.ReflectionKernelBridge
public import GuthMaynard.Improvement.ReflectionNear

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

/-- The density-library phase uses exactly the same real logarithm. -/
theorem density_phase_eq (x v : ℝ) :
    MathCollab.Density.dirichletPhase x v = phase x v := by
  unfold MathCollab.Density.dirichletPhase phase
  congr 1
  push_cast
  ring

/-- Every pair occurs in at most three of the actual local reflection sets.
This permits the global short-range theorem to be used without imposing a
cardinality threshold on each local subset. -/
theorem reflection_local_pair_le_three {H : ℝ} (hH : 0 < H)
    (M : ℕ) (W : Finset ℝ) :
    (∑' j : ℤ, MathCollab.Density.completePairEnergy M
      (MathCollab.Density.localSet W H j)) ≤
      3*MathCollab.Density.completePairEnergy M W := by
  classical
  open MathCollab.Density in
  rw [tsum_completePairEnergy_localSet hH]
  have he (j : ℤ) : completePairEnergy M (localSet W H j) =
      ∑ t ∈ W, ∑ u ∈ W, if t ∈ localSet W H j ∧ u ∈ localSet W H j then
        ‖dyadicPolynomial M (t-u)‖^2 else 0 :=
    (sum_pairs_indicator (filter_subset _ _) _).symm
  simp_rw [he]
  simp_rw [sum_comm (s := localIndices W H) (t := W)]
  unfold completePairEnergy
  rw [mul_sum]
  apply sum_le_sum
  intro t ht
  rw [mul_sum]
  apply sum_le_sum
  intro u _
  calc
    _ ≤ ∑ j ∈ localIndices W H, if t ∈ localSet W H j then
        ‖dyadicPolynomial M (t-u)‖^2 else 0 := by
      apply sum_le_sum
      intro j _
      by_cases htj : t ∈ localSet W H j
      · simp only [htj,true_and,ite_true]
        split_ifs <;> first | exact le_rfl | exact sq_nonneg _
      · simp only [htj,false_and,ite_false,le_refl]
    _ = 3*‖dyadicPolynomial M (t-u)‖^2 := by
      rw [← sum_filter,localIndices_filter_point hH ht]
      simp

end Montgomery.RationalMoment
