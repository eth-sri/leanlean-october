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

def gaussianAbsoluteMean  := ∫ z : ℝ, |z| ∂standardGaussianLine

theorem standardGaussianLine_abs_integrable :
    Integrable (fun z  => |z|) standardGaussianLine := by
  simpa only [Real.norm_eq_abs, id_eq] using
    (IsGaussian.integrable_id (μ := standardGaussianLine)).norm

theorem gaussianAbsoluteMean_pos : 0 < gaussianAbsoluteMean := by
  have hn : 0 ≤ gaussianAbsoluteMean := integral_nonneg (fun _ => abs_nonneg _)
  by_contra h
  have hz  := le_antisymm (not_lt.mp h) hn
  have habs  :=
    (integral_eq_zero_iff_of_nonneg (fun z => abs_nonneg z) standardGaussianLine_abs_integrable).mp hz
  have hid : id =ᵐ[standardGaussianLine] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [habs] with z hz
    exact abs_eq_zero.mp hz
  have hv := variance_congr hid
  rw [variance_id_gaussianReal] at hv
  change (1 : ℝ) = Var[(0 : ℝ → ℝ); standardGaussianLine] at hv
  rw [variance_zero] at hv
  exact one_ne_zero hv

section
variable {d : ℕ}

theorem euclideanNorm_eq_toLp_norm  (v : Covariate d) :
    euclideanNorm v = ‖WithLp.toLp 2 v‖ := by
  simp only [euclideanNorm, EuclideanSpace.norm_eq, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs]

theorem gaussianPhase_eq_inner  (v Z : Covariate d) :
    gaussianPhase v Z = inner ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 Z) := by
  simp only [gaussianPhase, PiLp.inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply,
    conj_trivial, mul_comm]

theorem gaussianPhase_map_eq_scaled_gaussian  v :
    (standardGaussianPi d).map (gaussianPhase v) =
      standardGaussianLine.map (fun z  => euclideanNorm v * z) := by
  let L  := innerSL ℝ (WithLp.toLp 2 v)
  have hfun : gaussianPhase v = L ∘ (WithLp.toLp 2) := by
    funext Z
    exact gaussianPhase_eq_inner v Z
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    map_pi_eq_stdGaussian, IsGaussian.map_eq_gaussianReal L,
    integral_strongDual_stdGaussian, variance_dual_stdGaussian, gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  congr 1
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  simp only [L, innerSL_apply_norm, ← euclideanNorm_eq_toLp_norm]
  rfl

theorem gaussianPhase_abs_integral  v :
    (∫ Z, |gaussianPhase v Z| ∂standardGaussianPi d) =
      gaussianAbsoluteMean * euclideanNorm v := by
  have hphase : Measurable (gaussianPhase v) := by unfold gaussianPhase; fun_prop
  have habs : AEStronglyMeasurable (fun z : ℝ => |z|)
      ((standardGaussianPi d).map (gaussianPhase v)) := (by fun_prop : Measurable (fun z : ℝ => |z|)).aestronglyMeasurable
  rw [← integral_map hphase.aemeasurable habs, gaussianPhase_map_eq_scaled_gaussian v,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (show 0 ≤ euclideanNorm v by unfold euclideanNorm; positivity)]
  rw [integral_const_mul]
  exact mul_comm _ _
end


end NearlyMinimax
