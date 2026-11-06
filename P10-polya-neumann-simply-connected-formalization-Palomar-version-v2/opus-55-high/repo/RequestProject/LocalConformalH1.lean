module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.RingTheory.Complex
public import Mathlib.Tactic
public import RequestProject.ConformalSmoothTests

/-!
# H¹ pullback from local conformal disk coordinates

Composition on smooth restrictions is bounded in the actual H¹ norm by
the conformal Jacobian formula and invariance of gradient energy. Dense
extension constructs its continuous action on H¹. The coordinate map is
only required on a neighbourhood of the closed disk; no homeomorphism of
the entire plane is an input.

This module concerns a given smooth conformal coordinate map. Existence
and closed-boundary regularity of that map remain separate theorems.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Real ContDiff ComplexConjugate Topology ENNReal

variable {U : Set ℂ} (A : ℂ →L[ℝ] ℂ) (c : ℂ) {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))

private theorem abs_det_complex_deriv (c : ℂ) :
    |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det| =
      ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

theorem localConformal_integral_image (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U) (a : ℂ → ℝ) :
    (∫ w in F '' U, a w) = ∫ z in U, ‖deriv F z‖ ^ 2 * a (F z) := by
  have hfd : ∀ z ∈ U, HasFDerivWithinAt F
      ((ContinuousLinearMap.smulRight 1 (deriv F z)).restrictScalars ℝ) U z :=
    fun z hz => ((hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ).hasFDerivWithinAt
  simp [integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet hfd hinj a, abs_det_complex_deriv]

theorem localConformal_integrable_weight (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U) {a : ℂ → ℝ}
    (ha : IntegrableOn a (F '' U)) :
    IntegrableOn (fun z => ‖deriv F z‖ ^ 2 * a (F z)) U := by
  have hfd : ∀ z ∈ U, HasFDerivWithinAt F
      ((ContinuousLinearMap.smulRight 1 (deriv F z)).restrictScalars ℝ) U z :=
    fun z hz => ((hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ).hasFDerivWithinAt
  simpa only [abs_det_complex_deriv, smul_eq_mul] using (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    hU.measurableSet hfd hinj a).1 ha

private theorem realCLM_apply_complex (w : ℂ) :
    A w = (w.re : ℂ) * A 1 + (w.im : ℂ) * A Complex.I := by
  calc
    A w = A (w.re • (1 : ℂ) + w.im • Complex.I) := by
      norm_num
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

private theorem realCLM_conformal_energy :
    ‖A c‖ ^ 2 + ‖A (c * Complex.I)‖ ^ 2 =
      ‖c‖ ^ 2 * (‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2) := by
  rw [realCLM_apply_complex A c, realCLM_apply_complex A (c * Complex.I)]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem gradSq_smoothDiskComposition (hhol : DifferentiableOn ℂ F (ball 0 1)) (f : smoothTraceTests)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    gradSq (smoothDiskCompositionLin hR F hFs f) z =
      ‖deriv F z‖ ^ 2 * gradSq f (F z) := by
  have hfd : ∀ v : ℂ, fderiv ℝ F z v = deriv F z * v := by
    intro v
    rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
    exact fderiv_eq_deriv_mul
  unfold gradSq
  rw [fderiv_smoothDiskCompositionLin hR F hFs f (ball_subset_closedBall hz)]
  simp only [ContinuousLinearMap.comp_apply, hfd, mul_one]
  exact realCLM_conformal_energy _ _

theorem integral_gradSq_smoothDiskComposition (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (f : smoothTraceTests) :
    (∫ z in ball 0 1, gradSq (smoothDiskCompositionLin hR F hFs f) z) =
      ∫ w in F '' ball 0 1, gradSq f w := by
  rw [localConformal_integral_image isOpen_ball hhol hinj]
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  exact gradSq_smoothDiskComposition hR F hFs hhol f hz

theorem integral_valueSq_smoothDiskComposition_le (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) {C : ℝ}
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (f : smoothTraceTests) :
    (∫ z in ball 0 1, ‖smoothDiskCompositionLin hR F hFs f z‖ ^ 2) ≤
      C * ∫ w in F '' ball 0 1, ‖f w‖ ^ 2 := by
  rw [localConformal_integral_image isOpen_ball hhol hinj, ← integral_const_mul]
  apply integral_mono_ae ((smoothTraceTests_memLp (ball 0 1)
    (smoothDiskCompositionLin hR F hFs f)).integrable_norm_pow (by decide)) ((localConformal_integrable_weight isOpen_ball hhol hinj ((smoothTraceTests_memLp (F '' ball 0 1) f).integrable_norm_pow
    (by decide))).const_mul C)
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  rw [smoothDiskCompositionLin_eq_closedDisk hR F hFs f (ball_subset_closedBall hz)]
  have h := mul_le_mul_of_nonneg_right (hC z hz) (sq_nonneg ‖f (F z)‖)
  linarith

theorem norm_smoothDiskCompositionH1_le (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) {C : ℝ}
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (f : smoothTraceTests) :
    ‖smoothTraceH1 (ball 0 1) (smoothDiskCompositionLin hR F hFs f)‖ ≤
      Real.sqrt (max C 1) * ‖smoothTraceH1 (F '' ball 0 1) f‖ := by
  have hv := integral_valueSq_smoothDiskComposition_le hR F hFs hhol hinj hC f
  have hg := integral_gradSq_smoothDiskComposition hR F hFs hhol hinj f
  have hval : 0 ≤ ∫ w in F '' ball 0 1, ‖f w‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hgrad : 0 ≤ ∫ w in F '' ball 0 1, gradSq f w :=
    integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hsq := Real.sq_sqrt (show 0 ≤ max C 1 by positivity)
  have ht := norm_sq_smoothTraceH1 (ball 0 1) (smoothDiskCompositionLin hR F hFs f)
  have hs := norm_sq_smoothTraceH1 (F '' ball 0 1) f
  have hv' := mul_le_mul_of_nonneg_right (le_max_left C 1) hval
  have hg' := mul_le_mul_of_nonneg_right (le_max_right C 1) hgrad
  have hn : 0 ≤ Real.sqrt (max C 1) * ‖smoothTraceH1 (F '' ball 0 1) f‖ := by
    positivity
  nlinarith 

end PolyaNeumann

end
