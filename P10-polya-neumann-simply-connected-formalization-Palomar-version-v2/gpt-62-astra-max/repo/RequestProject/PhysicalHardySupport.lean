module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.HardyAntiderivative
public import RequestProject.Driven
public import RequestProject.CutFourier
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic
public import RequestProject.PlanarNotation

/-!
# Hardy support of an actual disk boundary trace

For a given map holomorphic in the open unit disk and continuous on its closure,
Cauchy--Goursat proves that its actual circle trace has no negative Fourier
coefficients.  With real C¹ regularity of that trace, integration by parts proves
the derivative coefficient identity and its zero mean.  Conjugation therefore
gives strictly negative support for the actual conjugated boundary derivative.

All Fourier coefficients use the averaged convention on `[0,2π]`.  Real smoothness
near the closed disk is sufficient for the C¹ corollary; holomorphicity outside the
open disk is never required.  This file does not construct the initial conformal
map, an arc-length reparametrization, or an `IsBoundaryParam` instance for the circle
trace.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped ComplexConjugate

section

variable (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F unitDisk) (m : ℕ) (θ : ℝ)

include F θ in
/-- The actual given map restricted to the unit circle in its usual angular parameter. -/
def physicalCircleTrace : ℂ := F (unitCirclePt θ)

/-- Boundary trace of the smooth disk map in the standard angular coordinate. -/
abbrev SmoothDiskMap.boundary (φ : SmoothDiskMap) := physicalCircleTrace φ.map

theorem physicalCircleTrace_periodic :
    Function.Periodic (physicalCircleTrace F) anglePeriod := by
  intro θ
  exact congrArg F ((periodic_circleMap 0 1) θ)

theorem fourier_natCast_eq_pow :
    fourier  (m : ℤ) (θ : ParamCircle) =
      (unitCirclePt θ) ^ m := by
  rw [fourier_coe_apply, circleMap_zero_pow]
  simp only [one_pow, circleMap_zero, Complex.ofReal_one, one_mul]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

include hF in
/-- A Cauchy--Goursat integral is the ordinary angular integral selecting a
negative Fourier coefficient, with its genuine circle differential. -/
theorem physicalCircleTrace_negative_moment_eq_zero :
    (∫ₚ θ,
      fourier  ((m + 1 : ℕ) : ℤ)
        (θ : ParamCircle) * physicalCircleTrace F θ) = 0 := by
  have hpoly : DiffContOnCl ℂ (fun z => F z * z ^ m) unitDisk :=
    ⟨hF.differentiableOn.mul (differentiableOn_id.pow m),
      hF.continuousOn.mul (continuousOn_id.pow m)⟩
  have hzero  :=
    DiffContOnCl.circleIntegral_eq_zero (by norm_num) hpoly
  have heq : circleIntegral (fun z => F z * z ^ m) 0 1 =
      Complex.I * (∫ₚ θ,
        fourier  ((m + 1 : ℕ) : ℤ)
          (θ : ParamCircle) * physicalCircleTrace F θ) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [deriv_circleMap, smul_eq_mul, physicalCircleTrace]
    rw [fourier_natCast_eq_pow, pow_succ]
    ring
  rw [heq] at hzero
  aesop

include hF in
/-- Every strictly negative averaged Fourier coefficient of the actual circle
trace vanishes, derived solely from disk holomorphicity and closure continuity. -/
theorem physicalCircleTrace_fourierCoeffOn_eq_zero_of_neg
    {n : ℤ} (hn : n < 0) :
    angleCoeff (physicalCircleTrace F) n = 0 := by
  cases n with
  | ofNat m =>
      grind
  | negSucc m =>
      have hi : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := by
        rfl
      have hmoment := physicalCircleTrace_negative_moment_eq_zero F hF m
      simp only [fourier_coe_apply] at hmoment
      rw [hi, fourierCoeffOn_eq_integral]
      simp only [fourier_coe_apply, sub_zero, neg_neg, smul_eq_mul]
      rw [hmoment, smul_zero]

end

section

variable (F : ℂ → ℂ) (g : ℝ → ℂ) (φ : SmoothDiskMap) (hF : DiffContOnCl ℂ F unitDisk)
    (hγ : ContDiff ℝ 1 (physicalCircleTrace F)) (n : ℤ)

include hγ in
/-- Integration by parts for the actual derivative of a C¹ circle trace. -/
theorem physicalCircleTrace_deriv_fourierCoeffOn :
    angleCoeff (deriv (physicalCircleTrace F)) n =
      (Complex.I * (n : ℂ)) *
        angleCoeff (physicalCircleTrace F) n := by
  apply fourierCoeffOn_deriv
    (fun θ => (hγ.differentiable_one θ).hasDerivAt) hγ.continuous_deriv_one
  simpa using ((physicalCircleTrace_periodic F) 0).symm

theorem fourierCoeffOn_conj_volume :
    angleCoeff (fun θ => conj (g θ)) n =
      conj (angleCoeff g (-n)) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [sub_zero, Complex.real_smul, map_mul, Complex.conj_ofReal]
  congr 1
  rw [← intervalIntegral_conj]
  simp

include hF hγ in
/-- The actual conjugated boundary derivative has strictly negative Fourier support. -/
theorem physicalCircleTrace_conj_deriv_strictNegative :
    IsStrictNegativeFourierSupport
      (angleCoeff (fun θ => conj (deriv (physicalCircleTrace F) θ))) := by
  intro n hn
  rw [fourierCoeffOn_conj_volume, physicalCircleTrace_deriv_fourierCoeffOn F hγ]
  by_cases hn0 : n = 0
  · simp [*]
  · 
    rw [physicalCircleTrace_fourierCoeffOn_eq_zero_of_neg F hF (by omega), mul_zero, map_zero]

/-- Real regularity on a neighborhood of the closed disk gives the same regularity
of the actual angular circle trace.  This assertion uses no exterior holomorphicity. -/
theorem contDiff_physicalCircleTrace_of_neighborhood
    {n : WithTop ℕ∞} {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ n F (ball (0 : ℂ) R)) :
    ContDiff ℝ n (physicalCircleTrace F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  
  exact (hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR (circleMap_mem_closedBall 0 (by norm_num) θ)))).comp θ
    (contDiff_circleMap 0 1).contDiffAt

/-- Basic regularity and periodicity of the angular coordinate. -/
theorem SmoothDiskMap.boundaryC1 : ContDiff ℝ 1 φ.boundary :=
  contDiff_physicalCircleTrace_of_neighborhood φ.one_lt_radius φ.map (φ.smooth.of_le (by simp))

theorem SmoothDiskMap.boundaryC4 : ContDiff ℝ 4 φ.boundary :=
  contDiff_physicalCircleTrace_of_neighborhood φ.one_lt_radius φ.map (φ.smooth.of_le (by simp))

theorem SmoothDiskMap.periodic_boundary :
    Function.Periodic φ.boundary anglePeriod := physicalCircleTrace_periodic φ.map

end

/-- Strict negative support follows from the standard supplied coordinate data:
real C¹ smoothness near the closure and holomorphicity only in the open disk. -/
theorem physicalCircleTrace_conj_deriv_strictNegative_of_neighborhood
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ 1 F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F unitDisk) :
    IsStrictNegativeFourierSupport
      (angleCoeff (fun θ => conj (deriv (physicalCircleTrace F) θ))) := by
  apply physicalCircleTrace_conj_deriv_strictNegative F
    (DiffContOnCl.mk_ball hhol (hFs.continuousOn.mono (closedBall_subset_ball hR)))
    (contDiff_physicalCircleTrace_of_neighborhood hR F hFs)

end PolyaNeumann

end
