module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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



namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Real ContDiff ComplexConjugate Topology ENNReal

private theorem abs_det_complex_deriv c :
    |((ContinuousLinearMap.smulRight (1 : ComplexEnd ℂ) c).restrictScalars ℝ).det| =
      ‖c‖ ^ 2 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars]
  simp [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

section
variable {U } (hU : IsOpen U) {F : PlaneMap} (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
include U hU F hF hinj

theorem localConformal_integral_image (a : ℂ → ℝ) :
    (∫ w in F '' U, a w) = ∫ z in U, ‖deriv F z‖ ^ 2 * a (F z) := by
  have hfd : ∀ z ∈ U, HasFDerivWithinAt F
      ((ContinuousLinearMap.smulRight (1 : ComplexEnd ℂ) (deriv F z)).restrictScalars ℝ) U z :=
    fun z hz => ((hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ).hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet hfd hinj a]
  simp_all [abs_det_complex_deriv]

theorem localConformal_integrable_weight 
    (ha : IntegrableOn a (F '' U)) :
    IntegrableOn (fun z => ‖deriv F z‖ ^ 2 * a (F z)) U := by
  have hfd : ∀ z ∈ U, HasFDerivWithinAt F
      ((ContinuousLinearMap.smulRight (1 : ComplexEnd ℂ) (deriv F z)).restrictScalars ℝ) U z :=
    fun z hz => ((hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ).hasFDerivWithinAt
  have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    hU.measurableSet hfd hinj a).1 ha
  simp_all [abs_det_complex_deriv]

end

theorem common_realCLM_apply_complex (A : ℂ →L[ℝ] ℂ) w :
    A w = (w.re : ℂ) * A 1 + (w.im : ℂ) * A Complex.I := by
  calc
    A w = A (w.re • 1 + w.im • Complex.I) := by
      simp_all
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

private theorem realCLM_conformal_energy (A : ℂ →L[ℝ] ℂ) c :
    ‖A c‖ ^ 2 + ‖A (c * Complex.I)‖ ^ 2 =
      ‖c‖ ^ 2 * (‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2) := by
  rw [common_realCLM_apply_complex A c, common_realCLM_apply_complex A (c * Complex.I)]
  simp  [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R) (hhol : DifferentiableOn ℂ F unitDisk)
local notation "smoothDiskCompositionLinFixed" => smoothDiskCompositionLin hR F hFs

include R hR F hFs hhol

theorem gradSq_smoothDiskComposition f
     (hz : z ∈ unitDisk) :
    gradSq (smoothDiskCompositionLinFixed f : PlaneMap) z =
      ‖deriv F z‖ ^ 2 * gradSq (f : PlaneMap) (F z) := by
  have hfd : ∀ v : ℂ, fderiv ℝ F z v = deriv F z * v := by
    intro v
    rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
    exact fderiv_eq_deriv_mul
  unfold gradSq
  rw [fderiv_smoothDiskCompositionLin hR F hFs f (ball_subset_closedBall hz)]
  simp_all [realCLM_conformal_energy]

theorem integral_gradSq_smoothDiskComposition
    (hinj : InjOn F unitDisk) f :
    (∫ z in unitDisk, gradSq (smoothDiskCompositionLinFixed f : PlaneMap) z) =
      ∫ w in F '' unitDisk, gradSq (f : PlaneMap) w := by
  rw [localConformal_integral_image isOpen_ball hhol hinj]
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  grind only [gradSq_smoothDiskComposition, PolyaNeumann.smoothTraceTests]

section
variable (hinj : InjOn F unitDisk) {C } (hC : DiskInverseJacobianBound F C) (f : smoothTraceTests)
include hinj C hC f

theorem integral_valueSq_smoothDiskComposition_le :
    (∫ z in unitDisk, ‖smoothDiskCompositionLinFixed f z‖ ^ 2) ≤
      C * ∫ w in F '' unitDisk, ‖f w‖ ^ 2 := by
  have hint := (smoothTraceTests_memLp (F '' ball 0 1) f).integrable_norm_pow
    (by decide)
  have hweight := localConformal_integrable_weight isOpen_ball hhol hinj hint
  have hdisk := (smoothTraceTests_memLp (ball 0 1)
    (smoothDiskCompositionLinFixed f)).integrable_norm_pow (by decide)
  rw [localConformal_integral_image isOpen_ball hhol hinj, ← integral_const_mul]
  apply integral_mono_ae hdisk (hweight.const_mul C)
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  rw [smoothDiskCompositionLin_eq_closedDisk hR F hFs f (ball_subset_closedBall hz)]
  have h := mul_le_mul_of_nonneg_right (hC z hz) (sq_nonneg ‖f (F z)‖)
  simpa  [mul_assoc] using h

theorem norm_smoothDiskCompositionH1_le :
    ‖smoothTraceH1 unitDisk (smoothDiskCompositionLinFixed f)‖ ≤
      Real.sqrt (max C 1) * ‖smoothTraceH1 (F '' unitDisk) f‖ := by
  have hv := integral_valueSq_smoothDiskComposition_le hR F hFs hhol hinj hC f
  have hg := integral_gradSq_smoothDiskComposition hR F hFs hhol hinj f
  have hval : 0 ≤ ∫ w in F '' unitDisk, ‖f w‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hgrad : 0 ≤ ∫ w in F '' unitDisk, gradSq (f : PlaneMap) w :=
    integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hsq := Real.sq_sqrt (show 0 ≤ max C 1 by positivity)
  have ht := norm_sq_smoothTraceH1 (ball 0 1) (smoothDiskCompositionLinFixed f)
  have hs := norm_sq_smoothTraceH1 (F '' ball 0 1) f
  have hv' := mul_le_mul_of_nonneg_right (le_max_left C 1) hval
  have hg' := mul_le_mul_of_nonneg_right (le_max_right C 1) hgrad
  have hbound : ‖smoothTraceH1 unitDisk (smoothDiskCompositionLinFixed f)‖ ^ 2 ≤
      (Real.sqrt (max C 1) * ‖smoothTraceH1 (F '' unitDisk) f‖) ^ 2 := by
    nlinarith
  have hn : 0 ≤ Real.sqrt (max C 1) * ‖smoothTraceH1 (F '' unitDisk) f‖ := by
    positivity
  nlinarith

end


end


end PolyaNeumann
