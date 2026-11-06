module
public import MathCollab.Density.DensitySlabBound
public import MathCollab.Density.DensityDyadicSummation

@[expose] public section

open Real Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density



/-- The original count is empty to the right of the open critical strip. -/
theorem zetaDensityCount_eq_zero_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) (T : ℝ) :
    zetaDensityCount σ T = 0 := by
  have he : zetaZeroFinset σ (-T) T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    have hh := mem_zetaZeroFinset.mp hρ
    linarith [hh.1.2.2,hh.2.1]
  simp [zetaDensityCount,zetaSlabCount,he]


