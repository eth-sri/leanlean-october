module

public import RequestProject.DiskCoordinates

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.RingTheory.Complex
public import Mathlib.Tactic
public import RequestProject.ConformalSmoothTests
public import RequestProject.PlanarNotation

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

section

variable (A : ℂ →L[ℝ] ℂ) (c : ℂ)

private theorem abs_det_complex_deriv :
    |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det| =
      ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

theorem localConformal_integral_image {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U) (a : ℂ → ℝ) :
    (∫ w in F '' U, a w) = ∫ z in U, ‖deriv F z‖ ^ 2 * a (F z) := by
  have hfd : ∀ z ∈ U, HasFDerivWithinAt F
      ((ContinuousLinearMap.smulRight 1 (deriv F z)).restrictScalars ℝ) U z :=
    fun z hz => ((hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ).hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet hfd hinj a]
  simp [abs_det_complex_deriv]

theorem localConformal_integrable_weight {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U) {a : ℂ → ℝ}
    (ha : IntegrableOn a (F '' U)) :
    IntegrableOn (fun z => ‖deriv F z‖ ^ 2 * a (F z)) U := by
  have hfd : ∀ z ∈ U, HasFDerivWithinAt F
      ((ContinuousLinearMap.smulRight 1 (deriv F z)).restrictScalars ℝ) U z :=
    fun z hz => ((hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ).hasFDerivWithinAt
  
  simpa [abs_det_complex_deriv] using (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    hU.measurableSet hfd hinj a).1 ha

theorem realCLM_apply_complex (w : ℂ) :
    A w = (w.re : ℂ) * A 1 + (w.im : ℂ) * A Complex.I := calc
    _ = A (w.re • 1 + w.im • Complex.I) := by
      aesop
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

private theorem realCLM_conformal_energy :
    ‖A c‖ ^ 2 + ‖A (c * Complex.I)‖ ^ 2 =
      ‖c‖ ^ 2 * (‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2) := by
  rw [realCLM_apply_complex A c, realCLM_apply_complex A (c * Complex.I)]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

end

section

variable (Φ : SmoothDiskMap) (hhol : DifferentiableOn ℂ Φ.map unitDisk)
    (hinj : InjOn Φ.map unitDisk) (f : smoothTraceTests)
include hhol

theorem gradSq_smoothDiskComposition {z : ℂ} (hz : z ∈ unitDisk) :
    gradSq (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f : ℂ → ℂ) z =
      ‖deriv Φ.map z‖ ^ 2 * gradSq (f : ℂ → ℂ) (Φ.map z) := by
  have hfd : ∀ v : ℂ, fderiv ℝ Φ.map z v = deriv Φ.map z * v := by
    intro v
    rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
    exact fderiv_eq_deriv_mul
  unfold gradSq
  rw [fderiv_smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f (ball_subset_closedBall hz)]
  simp only [ContinuousLinearMap.comp_apply, hfd, mul_one]
  exact realCLM_conformal_energy _ _

include hinj in
theorem integral_gradSq_smoothDiskComposition :
    (∫ z in unitDisk, gradSq (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f : ℂ → ℂ) z) =
      ∫ w in Φ.domain, gradSq (f : ℂ → ℂ) w := by
  rw [localConformal_integral_image isOpen_ball hhol hinj]
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  exact gradSq_smoothDiskComposition Φ hhol f hz

include hinj in
theorem integral_valueSq_smoothDiskComposition_le {C : ℝ}
    (hC : ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv Φ.map z‖ ^ 2) (f : smoothTraceTests) :
    (∫ z in unitDisk, ‖smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f z‖ ^ 2) ≤
      C * ∫ w in Φ.domain, ‖f w‖ ^ 2 := by
  have hint := (smoothTraceTests_memLp Φ.domain f).integrable_norm_pow
    (by decide : 2 ≠ 0)
  
  have hdisk := (smoothTraceTests_memLp unitDisk
    (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f)).integrable_norm_pow (by decide : 2 ≠ 0)
  rw [localConformal_integral_image isOpen_ball hhol hinj, ← integral_const_mul]
  apply integral_mono_ae hdisk ((localConformal_integrable_weight isOpen_ball hhol hinj hint).const_mul C)
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  rw [smoothDiskCompositionLin_eq_closedDisk Φ.one_lt_radius Φ.map Φ.smooth f (ball_subset_closedBall hz)]
  
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right (hC z hz) (sq_nonneg ‖f (Φ.map z)‖)

include hinj in
theorem norm_smoothDiskCompositionH1_le {C : ℝ}
    (hC : ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv Φ.map z‖ ^ 2) (f : smoothTraceTests) :
    ‖smoothTraceH1 unitDisk (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f)‖ ≤
      Real.sqrt (max C 1) * ‖smoothTraceH1 Φ.domain f‖ := by
  have hv := integral_valueSq_smoothDiskComposition_le Φ hhol hinj hC f
  have hg := integral_gradSq_smoothDiskComposition Φ hhol hinj f
  have hval : 0 ≤ ∫ w in Φ.domain, ‖f w‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hgrad : 0 ≤ ∫ w in Φ.domain, gradSq f w :=
    integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hsq := Real.sq_sqrt (show 0 ≤ max C 1 by positivity)
  have ht := norm_sq_smoothTraceH1 unitDisk (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f)
  have hs := norm_sq_smoothTraceH1 Φ.domain f
  have hv' := mul_le_mul_of_nonneg_right (le_max_left C 1) hval
  have hg' := mul_le_mul_of_nonneg_right (le_max_right C 1) hgrad
  
  have hn : 0 ≤ Real.sqrt (max C 1) * ‖smoothTraceH1 Φ.domain f‖ := by
    positivity
  nlinarith [norm_nonneg (smoothTraceH1 unitDisk
    (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f))]

end

end PolyaNeumann

end
