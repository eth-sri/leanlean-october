module

public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.HardyAntiderivative
public import RequestProject.Driven
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic

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

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped ComplexConjugate



/-- The actual given map restricted to the unit circle in its usual angular parameter. -/
def physicalCircleTrace (F : PlaneMap) θ  := F (unitCircleMap θ)

theorem physicalCircleTrace_periodic F :
    Function.Periodic (physicalCircleTrace F) circlePeriod := (fun θ => congrArg F (periodic_circleMap 0 1 θ))

theorem common_physicalHardy_fourier_natCast (m : ℕ) (θ : ℝ) :
    fourier (T := 2 * Real.pi) (m : ℤ) (θ : AddCircle circlePeriod) =
      (unitCircleMap θ) ^ m := by
  rw [fourier_coe_apply, circleMap_zero_pow]
  simp  [circleMap_zero]
  field_simp

section
variable (F : PlaneMap) (hF : DiffContOnCl ℂ F unitDisk)

include F hF in
/-- A Cauchy--Goursat integral is the ordinary angular integral selecting a
negative Fourier coefficient, with its genuine circle differential. -/
theorem physicalCircleTrace_negative_moment_eq_zero m :
    (∫ θ in (0 : ℝ)..circlePeriod,
      fourier (T := 2 * Real.pi) ((m + 1 : ℕ) : ℤ)
        (θ : AddCircle circlePeriod) * physicalCircleTrace F θ) = 0 := by
  have hpoly : DiffContOnCl ℂ (fun z => F z * z ^ m) unitDisk :=
    ⟨hF.differentiableOn.mul (differentiableOn_id.pow m),
      hF.continuousOn.mul (continuousOn_id.pow m)⟩
  have hzero  :=
    DiffContOnCl.circleIntegral_eq_zero (by norm_num) hpoly
  have heq : circleIntegral (fun z => F z * z ^ m) 0 1 =
      Complex.I * (∫ θ in (0 : ℝ)..circlePeriod,
        fourier (T := 2 * Real.pi) ((m + 1 : ℕ) : ℤ)
          (θ : AddCircle circlePeriod) * physicalCircleTrace F θ) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [deriv_circleMap, physicalCircleTrace]
    rw [common_physicalHardy_fourier_natCast, pow_succ]
    ring
  simp_all

include F hF in
/-- Every strictly negative averaged Fourier coefficient of the actual circle
trace vanishes, derived solely from disk holomorphicity and closure continuity. -/
theorem physicalCircleTrace_fourierCoeffOn_eq_zero_of_neg
     (hn : n < 0) :
    fourierCoeffOn Real.two_pi_pos (physicalCircleTrace F) n = 0 := by
  cases n with
  | ofNat m =>
      grind
  | negSucc m =>
      have hi : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := by
        rfl
      have hmoment := physicalCircleTrace_negative_moment_eq_zero F hF m
      rw [hi, fourierCoeffOn_eq_integral]
      simp_all

private theorem physicalHardy_fourierCoeffOn_derivative
     (hd : ∀ θ, HasDerivAt γ (b θ) θ) (hb : Continuous b)
    (hper : γ 0 = γ circlePeriod) n :
    fourierCoeffOn Real.two_pi_pos b n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos γ n := by
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul, Int.cast_zero, mul_zero, zero_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
      (hb.intervalIntegrable _ _), ← hper, sub_self, smul_zero]
  · rw [fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn (fun θ _ => hd θ)
      (hb.intervalIntegrable _ _), ← hper, sub_self, mul_zero, zero_sub]
    have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hpi  := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
    ring

/-- Integration by parts for the actual derivative of a C¹ circle trace. -/
theorem physicalCircleTrace_deriv_fourierCoeffOn
    F (hγ : ContDiff ℝ 1 (physicalCircleTrace F)) n :
    fourierCoeffOn Real.two_pi_pos (deriv (physicalCircleTrace F)) n =
      (Complex.I * (n : ℂ)) *
        fourierCoeffOn Real.two_pi_pos (physicalCircleTrace F) n := by
  apply physicalHardy_fourierCoeffOn_derivative
    (fun θ => (hγ.differentiable_one θ).hasDerivAt) hγ.continuous_deriv_one
  simpa   using ((physicalCircleTrace_periodic F) 0).symm



theorem common_physicalHardy_fourierCoeffOn_conj (g : ComplexCurve) n :
    fourierCoeffOn Real.two_pi_pos (fun θ => conj (g θ)) n =
      conj (fourierCoeffOn Real.two_pi_pos g (-n)) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  rw [← intervalIntegral_conj]
  simp_all

include F hF in
/-- The actual conjugated boundary derivative has strictly negative Fourier support. -/
theorem physicalCircleTrace_conj_deriv_strictNegative
    (hγ : ContDiff ℝ 1 (physicalCircleTrace F)) :
    IsStrictNegativeFourierSupport
      (fourierCoeffOn Real.two_pi_pos (fun θ => conj (deriv (physicalCircleTrace F) θ))) := by
  intro n hn
  rw [common_physicalHardy_fourierCoeffOn_conj, physicalCircleTrace_deriv_fourierCoeffOn F hγ]
  by_cases hn0 : n = 0
  · simp_all
  · have hneg : -n < 0 := by omega
    simp_all [physicalCircleTrace_fourierCoeffOn_eq_zero_of_neg]

end


section
variable {R : ℝ} (hR : 1 < R) (F : PlaneMap) (hFs : ContDiffOn ℝ 1 F (ball (0 : ℂ) R))
include R hR F hFs

/-- Real C¹ regularity on a neighborhood of the closed disk gives C¹ regularity
of the actual angular circle trace.  This assertion uses no exterior holomorphicity. -/
theorem contDiff_physicalCircleTrace_of_neighborhood :
    ContDiff ℝ 1 (physicalCircleTrace F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hz  :=
    closedBall_subset_ball hR (circleMap_mem_closedBall 0 (by norm_num) θ)
  exact (hFs.contDiffAt (isOpen_ball.mem_nhds hz)).comp θ
    (contDiff_circleMap 0 1).contDiffAt

/-- Strict negative support follows from the standard supplied coordinate data:
real C¹ smoothness near the closure and holomorphicity only in the open disk. -/
theorem physicalCircleTrace_conj_deriv_strictNegative_of_neighborhood
    (hhol : DifferentiableOn ℂ F unitDisk) :
    IsStrictNegativeFourierSupport
      (fourierCoeffOn Real.two_pi_pos (fun θ => conj (deriv (physicalCircleTrace F) θ))) := by
  apply physicalCircleTrace_conj_deriv_strictNegative F
    (DiffContOnCl.mk_ball hhol (hFs.continuousOn.mono (closedBall_subset_ball hR)))
    (contDiff_physicalCircleTrace_of_neighborhood hR F hFs)

end


end PolyaNeumann

end
