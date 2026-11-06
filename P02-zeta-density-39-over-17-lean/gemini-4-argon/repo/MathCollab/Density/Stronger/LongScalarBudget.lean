module
public import MathCollab.Density.Stronger.Parameters
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

theorem log_pow_eventually_le_rpow (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, (Real.log T)^n ≤ T^η := by
  have hl := (isLittleO_log_rpow_rpow_atTop (n : ℝ) hη).tendsto_div_nhds_zero
  simp only [Real.rpow_natCast] at hl
  filter_upwards [eventually_gt_atTop (0:ℝ),
    hl.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with T hT hh
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hT η)).mp hh).le.trans_eq (one_mul _)



