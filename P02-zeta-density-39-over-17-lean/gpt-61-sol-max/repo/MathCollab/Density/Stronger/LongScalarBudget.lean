module
import Mathlib
public import MathCollab.Density.Stronger.Parameters
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter
open scoped Topology

namespace MathCollab.Density.Stronger

theorem log_pow_eventually_le_rpow (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, (Real.log T)^n ≤ T^η := by
  have hl := (isLittleO_log_rpow_rpow_atTop (n : ℝ) hη).tendsto_div_nhds_zero
  simp only [Real.rpow_natCast] at hl
  filter_upwards [eventually_gt_atTop (0:ℝ),
    hl.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with T hT hh
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hT η)).mp hh).le.trans_eq (one_mul _)

/-- Exact exponent, before the logarithmic and moment losses are budgeted. -/
theorem long_count_scale_identity {σ δ ε T : ℝ} (hT : 0 < T) :
    (detectorX δ T)^6*T^(2+ε)/(detectorY σ T)^(6*σ-3) =
      T^(2+6*δ+ε+(6-12*σ)*smoothingExponent σ/2) := by
  rw [detectorX,detectorY,← Real.rpow_mul_natCast hT.le,← Real.rpow_mul hT.le,
    ← Real.rpow_add hT,← Real.rpow_sub hT]
  ring

/-- A quarter of the original exponent margin remains after a moment loss
at most one eighth of the margin and any fixed logarithmic power. -/
theorem long_count_scalar_log_eventually (n : ℕ) {σ δ ε : ℝ}
    (hσ : 3/4 < σ) (hδ : δ < (1-smoothingExponent σ)/12)
    (hε : ε ≤ (1-smoothingExponent σ)/8) :
    ∀ᶠ T : ℝ in atTop,
      (detectorX δ T)^6*(Real.log T)^n*T^(2+ε)/(detectorY σ T)^(6*σ-3) ≤
        T^(densityExponent σ-(1-smoothingExponent σ)/4) := by
  have hm : 0 < 1-smoothingExponent σ := sub_pos.mpr (smoothingExponent_lt_one hσ)
  have hsaving := long_exponent_saving hσ hδ
  filter_upwards [eventually_ge_atTop (1:ℝ),
    log_pow_eventually_le_rpow n (show 0 < (1-smoothingExponent σ)/8 by positivity)]
    with T hT hlog
  have hTp : 0 < T := by linarith
  calc
    _ = (Real.log T)^n*((detectorX δ T)^6*T^(2+ε)/(detectorY σ T)^(6*σ-3)) := by ring
    _ = (Real.log T)^n*T^(2+6*δ+ε+(6-12*σ)*smoothingExponent σ/2) := by
      rw [long_count_scale_identity hTp]
    _ ≤ T^((1-smoothingExponent σ)/8)*T^(2+6*δ+ε+(6-12*σ)*smoothingExponent σ/2) :=
      mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hTp.le _)
    _ = T^((1-smoothingExponent σ)/8+(2+6*δ+ε+(6-12*σ)*smoothingExponent σ/2)) := by
      rw [← Real.rpow_add hTp]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith)


