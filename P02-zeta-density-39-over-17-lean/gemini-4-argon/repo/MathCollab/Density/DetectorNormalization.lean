module
public import MathCollab.Density.DetectorPoweredPieces

@[expose] public section

open Real Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density


/-- The logarithmic ambient enlargement is eventually below T squared. -/
theorem densityAmbient_eventually_le_sq :
    ∀ᶠ T : ℝ in atTop, densityAmbient T ≤ T^2 := by
  have hl := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1/32 by norm_num))] with T hT hlog
  have hh := (div_lt_iff₀ (by linarith : 0 < T)).mp hlog
  unfold densityAmbient
  nlinarith





