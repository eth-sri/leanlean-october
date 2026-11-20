module

public import NearlyMinimax.GaussianSeparatedCharacteristic

@[expose] public section

/-! Exact absolute first moments of actual standard Gaussian projections. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def gaussianAbsoluteMean : ℝ := ∫ z, |z| ∂standardGaussianLine

theorem gaussianAbsoluteMean_pos : 0 < gaussianAbsoluteMean := by
  by_contra h
  have hz  := le_antisymm (not_lt.mp h) (integral_nonneg (fun _ => abs_nonneg _))
  have hid : id =ᵐ[standardGaussianLine] (fun _ => 0) := by
    filter_upwards [((integral_eq_zero_iff_of_nonneg (fun z => abs_nonneg z) ((IsGaussian.integrable_id (μ := standardGaussianLine)).norm)).mp hz)] with z hz
    exact abs_eq_zero.mp hz
  have hv := variance_congr hid
  rw [variance_id_gaussianReal] at hv
  change 1 = Var[0; standardGaussianLine] at hv
  simp_all

variable {d : ℕ} (v : Covariate d)

theorem euclideanNorm_eq_toLp_norm :
    euclideanNorm v = ‖WithLp.toLp 2 v‖ := by
  simp only [euclideanNorm, EuclideanSpace.norm_eq, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs]

theorem gaussianPhase_map_eq_scaled_gaussian :
    (standardGaussianPi d).map (gaussianPhase v) =
      standardGaussianLine.map (fun z => euclideanNorm v * z) := by
  let L  := innerSL ℝ (WithLp.toLp 2 v)
  have hfun : gaussianPhase v = L ∘ (WithLp.toLp 2) := by
    funext Z
    exact (by simp only [gaussianPhase, PiLp.inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial, mul_comm] : gaussianPhase v Z = ⟪WithLp.toLp 2 v, WithLp.toLp 2 Z⟫)
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    map_pi_eq_stdGaussian, IsGaussian.map_eq_gaussianReal L,
    integral_strongDual_stdGaussian, variance_dual_stdGaussian, gaussianReal_map_const_mul]
  simp
  congr 1
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  simp only [L, innerSL_apply_norm, ← euclideanNorm_eq_toLp_norm]
  rfl

theorem gaussianPhase_abs_integral :
    (∫ Z, |gaussianPhase v Z| ∂standardGaussianPi d) =
      gaussianAbsoluteMean * euclideanNorm v := by
  have hphase : Measurable (gaussianPhase v) := by unfold gaussianPhase; fun_prop
  rw [← integral_map hphase.aemeasurable ((by fun_prop : Measurable (fun z => |z|)).aestronglyMeasurable), gaussianPhase_map_eq_scaled_gaussian v,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (show 0 ≤ euclideanNorm v by unfold euclideanNorm; positivity)]
  rw [integral_const_mul]
  exact mul_comm _ _

end NearlyMinimax
