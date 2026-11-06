module
public import MathCollab.Density.Stronger.WeightedTwelfth

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Outside the physical interval, every sample in [T,2T] is at distance at
least T; its physical ordinate is controlled by three times that distance. -/
theorem physical_tail_geometry {T u t : ℝ} (hT : 1 ≤ T) (hu : u ∈ Icc T (2*T))
    (ht : t ∉ Icc 0 (3*T)) : T ≤ |t-u| ∧ |t| ≤ 3*|t-u| := by
  have hTp : 0 < T := by linarith
  have hdist : T ≤ |t-u| := by
    rcases not_and_or.mp ht with hneg | hpos
    · have ht' : t < 0 := not_le.mp hneg
      rw [abs_of_neg (by linarith [hu.1] : t-u < 0)]
      linarith [hu.1]
    · have ht' : 3*T < t := not_le.mp hpos
      rw [abs_of_pos (by linarith [hu.2] : 0 < t-u)]
      linarith [hu.2]
  refine ⟨hdist,?_⟩
  have hab := abs_add_le (t-u) u
  rw [sub_add_cancel,abs_of_pos (by linarith [hu.1] : 0 < u)] at hab
  linarith [hu.2]




