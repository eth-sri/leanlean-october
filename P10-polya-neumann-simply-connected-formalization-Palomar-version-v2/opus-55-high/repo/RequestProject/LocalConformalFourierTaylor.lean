module

public import RequestProject.LocalConformalFourierCollar
public import RequestProject.PhysicalHardySupport
public import RequestProject.CutFourier
public import RequestProject.ArcLength
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Averaged circle coefficients, genuine Taylor data, and a smooth Fourier collar

The coefficients below are the averaged Haar Fourier coefficients of the actual
circle trace.  There is no orthonormal `sqrt (2 * pi)` factor.  Disk holomorphicity
and closure continuity identify them with the Cauchy coefficients; all orders of
real smoothness of the circle trace imply the summability required by the actual
collar construction.  No complex holomorphicity outside the disk is used.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology ComplexConjugate


/-- The actual averaged, rather than orthonormal, nonnegative circle coefficients. -/
def localConformalFourierTaylorCoefficients (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  fourierCoeffOn Real.two_pi_pos (physicalCircleTrace F) (n : ℤ)

variable {f : ℝ → ℂ} (F : ℂ → ℂ) (n : ℕ) (θ : ℝ)

theorem periodic_iteratedDeriv_two_pi (hp : Function.Periodic f (2 * Real.pi)) (k : ℕ) :
    Function.Periodic (iteratedDeriv k f) (2 * Real.pi) := by
  induction k with
  | zero => assumption
  | succ k ih =>
      simpa only [iteratedDeriv_succ] using deriv_periodic ih

theorem contDiff_infty_iteratedDeriv_real (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv k f) := by
  rw [iteratedDeriv_eq_iterate]
  fun_prop

theorem contDiff_infty_hasDerivAt_iteratedDeriv_real (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (θ : ℝ) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f θ) θ := by
  simpa only [iteratedDeriv_succ] using (((contDiff_infty_iteratedDeriv_real hf k).of_le
      (WithTop.coe_le_coe.mpr le_top)).differentiable_one θ).hasDerivAt

/-- Genuine repeated periodic integration by parts, including frequency zero. -/
theorem periodic_contDiff_infty_fourierCoeffOn_iteratedDeriv (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2 * Real.pi)) (k : ℕ) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (iteratedDeriv k f) n =
      (Complex.I * n) ^ k * fourierCoeffOn Real.two_pi_pos f n := by
  induction k with
  | zero => simp 
  | succ k ih =>
      rw [fourierCoeffOn_deriv
        (contDiff_infty_hasDerivAt_iteratedDeriv_real hf k)
        (contDiff_infty_iteratedDeriv_real hf (k + 1)).continuous (by
        simpa only [zero_add] using (periodic_iteratedDeriv_two_pi hp k 0).symm), ih]
      ring

theorem periodic_contDiff_infty_norm_fourierCoeffOn_iteratedDeriv (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2 * Real.pi)) (k : ℕ) (n : ℤ) :
    ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv k f) n‖ =
      |(n : ℝ)| ^ k * ‖fourierCoeffOn Real.two_pi_pos f n‖ := by
  simp [periodic_contDiff_infty_fourierCoeffOn_iteratedDeriv hf hp k n]

/-- Absolute summability is obtained from three actual derivatives, applied
at every derivative order, rather than from a Fourier decay premise. -/
theorem periodic_contDiff_infty_summable_derivative_coefficients (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2 * Real.pi)) (k : ℕ) :
    Summable (fun n  =>
      ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv (k + 1) f) n‖) := by
  apply summable_norm_fourierCoeffOn_deriv
    (contDiff_infty_hasDerivAt_iteratedDeriv_real hf k)
    (contDiff_infty_hasDerivAt_iteratedDeriv_real hf (k + 1))
    (contDiff_infty_hasDerivAt_iteratedDeriv_real hf (k + 1 + 1))
    (contDiff_infty_iteratedDeriv_real hf (k + 1 + 1 + 1)).continuous
  · simpa only [zero_add] using (periodic_iteratedDeriv_two_pi hp k 0).symm
  · simpa only [zero_add] using (periodic_iteratedDeriv_two_pi hp (k + 1) 0).symm
  · simpa only [zero_add] using (periodic_iteratedDeriv_two_pi hp (k + 1 + 1) 0).symm

/-- Every polynomially weighted positive tail of the genuine averaged
Fourier coefficients is summable.  The zeroth mode is not discarded. -/
theorem periodic_contDiff_infty_hasRapidFourierDecay (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2 * Real.pi)) :
    HasRapidFourierDecay (fun n  => fourierCoeffOn Real.two_pi_pos f n) := by
  intro k
  have hi : Function.Injective (fun n : ℕ => (n + 1 : ℤ)) := by
    intro m n h
    linarith
  have hs' : Summable (fun n  =>
      ‖fourierCoeffOn Real.two_pi_pos f (n + 1 : ℕ)‖ *
        (n + 1 : ℕ) ^ (k + 1)) := by
    refine ((periodic_contDiff_infty_summable_derivative_coefficients hf hp k).comp_injective hi).congr fun n => ?_
    change ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv (k + 1) f)
      (n + 1 : ℕ)‖ = _
    rw [periodic_contDiff_infty_norm_fourierCoeffOn_iteratedDeriv hf hp (k + 1)]
    simp only [Int.cast_natCast, abs_of_nonneg
      (show (0 : ℝ) ≤ (n + 1 : ℕ) from Nat.cast_nonneg _)]
    ring
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _)
    (pow_nonneg (Nat.cast_nonneg _) _)) (fun n => ?_) hs'
  have hbase : (1 : ℝ) ≤ (n + 1 : ℕ) := by
    norm_num
  simpa only [mul_one, pow_succ, mul_assoc] using
    mul_le_mul_of_nonneg_left hbase (mul_nonneg (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))

theorem localConformalFourierTaylorCoefficients_hasRapidFourierDecay
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace F)) :
    HasRapidFourierDecay (localConformalFourierTaylorCoefficients F) :=
  periodic_contDiff_infty_hasRapidFourierDecay hΓ (physicalCircleTrace_periodic F)

private theorem fourierTaylor_fourier_natCast :
    fourier (T := 2 * Real.pi) (n : ℤ) (θ : AddCircle (2 * Real.pi)) =
      (circleMap 0 1 θ) ^ n := by
  rw [fourier_coe_apply, circleMap_zero_pow]
  simp only [one_pow, circleMap_zero, Complex.ofReal_one, one_mul]
  congr 1
  push_cast
  field_simp

private theorem fourierTaylor_fourier_neg_natCast :
    fourier (T := 2 * Real.pi) (-(n : ℤ)) (θ : AddCircle (2 * Real.pi)) =
      (circleMap 0 1 θ)⁻¹ ^ n := by
  rw [fourier_neg, fourierTaylor_fourier_natCast, map_pow,
    ← Complex.inv_eq_conj (z := circleMap 0 1 θ)
      (by norm_num)]

/-- The Cauchy coefficient is exactly the averaged angular coefficient.
This calculation does not require any holomorphicity hypothesis. -/
theorem cauchyPowerSeries_unitDisk_coefficient_eq_fourier
    (F : ℂ → ℂ) (n : ℕ) :
    cauchyPowerSeries F 0 1 n (fun _ => 1) =
      localConformalFourierTaylorCoefficients F n := by
  have hcircle : circleIntegral (fun z  => z⁻¹ ^ n * (z⁻¹ * F z)) 0 1 =
      Complex.I * (∫ θ in 0..(2 * Real.pi),
        fourier (T := 2 * Real.pi) (-n)
          θ * physicalCircleTrace F θ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    change deriv (circleMap 0 1) θ •
      ((circleMap 0 1 θ)⁻¹ ^ n * ((circleMap 0 1 θ)⁻¹ * F (circleMap 0 1 θ))) =
      Complex.I * (fourier  (-n)
        θ * physicalCircleTrace F θ)
    rw [fourierTaylor_fourier_neg_natCast]
    simp only [deriv_circleMap, smul_eq_mul, physicalCircleTrace]
    field_simp 
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
    Fin.prod_const, one_pow, sub_zero, smul_eq_mul]
  rw [hcircle, localConformalFourierTaylorCoefficients, fourierCoeffOn_eq_integral]
  simp only [smul_eq_mul, Complex.real_smul]
  rw [sub_zero]
  push_cast
  field_simp 

theorem cauchyPowerSeries_unitDisk_apply_eq_fourier
    (z : ℂ) :
    cauchyPowerSeries F 0 1 n (fun _ => z) =
      localConformalFourierTaylorCoefficients F n * z ^ n := by
  have hcoef := cauchyPowerSeries_unitDisk_coefficient_eq_fourier F n
  simp  at hcoef ⊢
  grind

/-- Interior Taylor matching follows from the actual Cauchy representation
on the open disk, with the coefficients already identified above. -/
theorem localConformalFourierTaylor_hasSum_on_openDisk
    (hF : DiffContOnCl ℂ F (ball 0 1))
    {z : ℂ} (hz : z ∈ ball 0 1) :
    HasSum (fun n  => localConformalFourierTaylorCoefficients F n * z ^ n) (F z) := by
  simpa only [sub_zero, NNReal.coe_one, cauchyPowerSeries_unitDisk_apply_eq_fourier] using (hF.hasFPowerSeriesOnBall (R := 1) (by norm_num)).hasSum_sub (by
    simpa only [Metric.eball_coe, NNReal.coe_one] using hz)

/-- Closure matching uses continuity of the genuinely constructed collar
and the original map, so no boundary power-series identity is a premise. -/
theorem localConformalFourierTaylor_eq_on_closedDisk
    (hF : DiffContOnCl ℂ F (ball 0 1))
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace F))
    {z : ℂ} (hz : z ∈ closedBall 0 1) :
    F z = localConformalFourierTaylorCoefficients F 0 +
      ∑' n : ℕ, localConformalFourierTaylorCoefficients F (n + 1) * z ^ (n + 1) := by
  let a := localConformalFourierTaylorCoefficients F
  have hEq : EqOn (fourierCollarExtension a) F (ball 0 1) := by
    intro w hw
    have hs := localConformalFourierTaylor_hasSum_on_openDisk F hF hw
    calc
      fourierCollarExtension a w = a 0 + ∑' n : ℕ, a (n + 1) * w ^ (n + 1) :=
        fourierCollarExtension_eq_taylor_on_closedDisk a (ball_subset_closedBall hw)
      _ = ∑' n : ℕ, a n * w ^ n := by
        simpa only [pow_zero, mul_one] using hs.summable.tsum_eq_zero_add.symm
      _ = F w := hs.tsum_eq
  exact (hEq.of_subset_closure (fourierCollarExtension_contDiff (localConformalFourierTaylorCoefficients_hasRapidFourierDecay F hΓ)).continuous.continuousOn
      hF.continuousOn_ball ball_subset_closedBall (by
        simp [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]) hz).symm.trans (fourierCollarExtension_eq_taylor_on_closedDisk a hz)

/-- Actual smooth circle data now supplies both genuine rapid decay and
the closed-disk Taylor identity needed by the Fourier collar construction. -/
theorem localConformalFourierTaylor_data
    (hF : DiffContOnCl ℂ F (ball 0 1))
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace F)) :
    HasRapidFourierDecay (localConformalFourierTaylorCoefficients F) ∧
      ∀ z ∈ closedBall 0 1,
        F z = localConformalFourierTaylorCoefficients F 0 +
          ∑' n : ℕ, localConformalFourierTaylorCoefficients F (n + 1) * z ^ (n + 1) :=
  ⟨localConformalFourierTaylorCoefficients_hasRapidFourierDecay F hΓ,
    fun _ hz => localConformalFourierTaylor_eq_on_closedDisk F hF hΓ hz⟩

/-- A real-smooth global extension from the actual smooth circle trace.
It agrees on the whole closed disk and remains complex holomorphic inside. -/
theorem exists_smooth_holomorphic_fourier_collar_of_circleTrace
    (hF : DiffContOnCl ℂ F (ball 0 1))
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace F)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧
      EqOn G F (closedBall 0 1) ∧ DifferentiableOn ℂ G (ball 0 1) := by
  obtain ⟨ha, hTaylor⟩ := localConformalFourierTaylor_data F hF hΓ
  exact exists_smooth_holomorphic_fourier_collar_of_taylor ha hF.differentiableOn hTaylor

end PolyaNeumann
