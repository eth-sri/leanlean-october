module

public import NearlyMinimax.GaussianSeparatedCharacteristic
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Exact absolute first moments of actual standard Gaussian projections. -/
𝚴
open scoped BigOperators RealInnerProductSpace
𝚨
𝚰
𝚩

def gaussianAbsoluteMean : ℝ := ∫ z : ℝ, |z| ∂standardGaussianLine

theorem standardGaussianLine_abs_integrable :
    Integrable (fun z => |z|) standardGaussianLine := by
  simpa only [Real.norm_eq_abs, id_eq] using
    (IsGaussian.integrable_id (μ := standardGaussianLine)).norm

theorem gaussianAbsoluteMean_pos : 0 < gaussianAbsoluteMean := by
  by_contra h
  have hz := le_antisymm (not_lt.mp h) $ integral_nonneg 𝗔₁
  have hid : id =ᵐ[standardGaussianLine] fun _ => 0 := by
    filter_upwards [ (integral_eq_zero_iff_of_nonneg abs_nonneg standardGaussianLine_abs_integrable).mp hz ] with z hz
    exact abs_eq_zero.mp hz
  have hv := variance_congr hid
  rw [variance_id_gaussianReal] at hv
  change 1 = Var[0; standardGaussianLine] at hv
  simp_all

𝗇 𝔄 WithLp.toLp 2 v
theorem euclideanNorm_eq_toLp_norm (v : Covariate d) :
    euclideanNorm v = ‖𝔄‖ := by
  simp only [euclideanNorm, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]

theorem gaussianPhase_eq_inner (v Z : Covariate d) :
    gaussianPhase v Z = inner ℝ 𝔄 (WithLp.toLp 2 Z) := by
  simp only [gaussianPhase, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, mul_comm]

theorem gaussianPhase_map_eq_scaled_gaussian v :
    (standardGaussianPi d).map (gaussianPhase v) =
      standardGaussianLine.map fun z => euclideanNorm v * z := by
  let L := innerSL ℝ 𝔄
  have hfun : gaussianPhase v = L ∘ WithLp.toLp 2 := by
    funext Z
    exact gaussianPhase_eq_inner v Z
  rw [hfun, ← Measure.map_map  𝖦₃  𝖦₃ ,
    map_pi_eq_stdGaussian, IsGaussian.map_eq_gaussianReal L,
    integral_strongDual_stdGaussian, variance_dual_stdGaussian, gaussianReal_map_const_mul]
  simp
  congr 1
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ $ sq_nonneg _ ]
  simp only [L, innerSL_apply_norm, ← euclideanNorm_eq_toLp_norm]
  rfl

theorem gaussianPhase_abs_integral v :
     ∫ Z, |gaussianPhase v Z| ∂standardGaussianPi d =
      gaussianAbsoluteMean * euclideanNorm v := by
  have hphase : Measurable $ gaussianPhase v := by unfold gaussianPhase; fun_prop
  rw [← integral_map hphase.aemeasurable (by fun_prop : Measurable fun z => |z| ).aestronglyMeasurable , gaussianPhase_map_eq_scaled_gaussian v,
    integral_map  𝖦₃  𝖦₃ ]
  simp_rw [abs_mul, abs_of_nonneg $ show 0 ≤ euclideanNorm v by unfold euclideanNorm; positivity ]
  rw [integral_const_mul]
  exact mul_comm ..
