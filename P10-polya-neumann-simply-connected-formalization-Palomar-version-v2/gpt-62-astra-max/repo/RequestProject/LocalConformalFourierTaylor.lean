module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.LocalConformalFourierCollar
public import RequestProject.PhysicalHardySupport
public import RequestProject.CutFourier
public import RequestProject.ArcLength
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology ComplexConjugate

section

variable (F : ℂ → ℂ) (n : ℕ) (hF : DiffContOnCl ℂ F unitDisk)
    (hΓ : ContDiff ℝ ∞ (physicalCircleTrace F))

include F n in
/-- The actual averaged, rather than orthonormal, nonnegative circle coefficients. -/
def localConformalFourierTaylorCoefficients : ℂ :=
  angleCoeff (physicalCircleTrace F) (n : ℤ)

theorem periodic_iteratedDeriv_two_pi {f : ℝ → ℂ}
    (hp : Function.Periodic f anglePeriod) (k : ℕ) :
    Function.Periodic (iteratedDeriv k f) anglePeriod := by
  induction k with
  | zero => exact hp
  | succ k ih =>
      simpa [iteratedDeriv_succ] using deriv_periodic ih

theorem contDiff_infty_iteratedDeriv_real {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  rw [iteratedDeriv_eq_iterate]
  fun_prop

theorem contDiff_infty_hasDerivAt_iteratedDeriv_real {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (k : ℕ) (θ : ℝ) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f θ) θ := by
  have hk  :=
    (contDiff_infty_iteratedDeriv_real hf k).of_le
      (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top)
  simpa [iteratedDeriv_succ] using (hk.differentiable_one θ).hasDerivAt

/-- Genuine repeated periodic integration by parts, including frequency zero. -/
theorem periodic_contDiff_infty_fourierCoeffOn_iteratedDeriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f anglePeriod) (k : ℕ) (n : ℤ) :
    angleCoeff (iteratedDeriv k f) n =
      (Complex.I * (n : ℂ)) ^ k * angleCoeff f n := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hend : iteratedDeriv k f 0 = iteratedDeriv k f anglePeriod := by
        simpa only [zero_add] using (periodic_iteratedDeriv_two_pi hp k 0).symm
      rw [fourierCoeffOn_deriv
        (contDiff_infty_hasDerivAt_iteratedDeriv_real hf k)
        (contDiff_infty_iteratedDeriv_real hf (k + 1)).continuous hend, ih,
        pow_succ']
      ring

theorem periodic_contDiff_infty_norm_fourierCoeffOn_iteratedDeriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f anglePeriod) (k : ℕ) (n : ℤ) :
    ‖angleCoeff (iteratedDeriv k f) n‖ =
      |(n : ℝ)| ^ k * ‖angleCoeff f n‖ := by
  rw [periodic_contDiff_infty_fourierCoeffOn_iteratedDeriv hf hp k n,
    norm_mul, norm_pow, norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul]

/-- Absolute summability is obtained from three actual derivatives, applied
at every derivative order, rather than from a Fourier decay premise. -/
theorem periodic_contDiff_infty_summable_derivative_coefficients {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f anglePeriod) (k : ℕ) :
    Summable (fun n : ℤ =>
      ‖angleCoeff (iteratedDeriv (k + 1) f) n‖) := by
  apply summable_norm_fourierCoeffOn_deriv
    (contDiff_infty_hasDerivAt_iteratedDeriv_real hf k)
    (contDiff_infty_hasDerivAt_iteratedDeriv_real hf (k + 1))
    (contDiff_infty_hasDerivAt_iteratedDeriv_real hf (k + 1 + 1))
    (contDiff_infty_iteratedDeriv_real hf (k + 1 + 1 + 1)).continuous
  · simpa using (periodic_iteratedDeriv_two_pi hp k 0).symm
  · simpa using (periodic_iteratedDeriv_two_pi hp (k + 1) 0).symm
  · simpa using (periodic_iteratedDeriv_two_pi hp (k + 1 + 1) 0).symm

/-- Every polynomially weighted positive tail of the genuine averaged
Fourier coefficients is summable.  The zeroth mode is not discarded. -/
theorem periodic_contDiff_infty_hasRapidFourierDecay {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f anglePeriod) :
    HasRapidFourierDecay (fun n : ℕ => angleCoeff f (n : ℤ)) := by
  intro k
  have hi : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℤ)) := by
    intro m n h
    exact Nat.add_right_cancel (Int.ofNat_injective h)
  have hs := (periodic_contDiff_infty_summable_derivative_coefficients hf hp k).comp_injective hi
  have hs' : Summable (fun n : ℕ =>
      ‖fourierCoeffOn Real.two_pi_pos f ((n + 1 : ℕ) : ℤ)‖ *
        ((n + 1 : ℕ) : ℝ) ^ (k + 1)) := by
    refine hs.congr fun n => ?_
    change ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv (k + 1) f)
      ((n + 1 : ℕ) : ℤ)‖ = _
    rw [periodic_contDiff_infty_norm_fourierCoeffOn_iteratedDeriv hf hp (k + 1)]
    simp only [Int.cast_natCast, abs_of_nonneg
      (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
    ring
  refine Summable.of_nonneg_of_le (fun n => (by positivity)) (fun n => ?_) hs'
  have hbase : 1 ≤ ((n + 1 : ℕ) : ℝ) := by
    simp
  bound

include hΓ in
theorem localConformalFourierTaylorCoefficients_hasRapidFourierDecay :
    HasRapidFourierDecay (localConformalFourierTaylorCoefficients F) :=
  periodic_contDiff_infty_hasRapidFourierDecay hΓ (physicalCircleTrace_periodic F)

private theorem fourierTaylor_fourier_neg_natCast (θ : ℝ) :
    fourier  (-(n : ℤ)) (θ : ParamCircle) =
      (unitCirclePt θ)⁻¹ ^ n := by
  rw [fourier_neg, fourier_natCast_eq_pow, map_pow,
    ← Complex.inv_eq_conj 
      (by simp)]

/-- The Cauchy coefficient is exactly the averaged angular coefficient.
This calculation does not require any holomorphicity hypothesis. -/
theorem cauchyPowerSeries_unitDisk_coefficient_eq_fourier :
    cauchyPowerSeries F 0 1 n (fun _ => (1 : ℂ)) =
      localConformalFourierTaylorCoefficients F n := by
  have hcircle : circleIntegral (fun z : ℂ => z⁻¹ ^ n * (z⁻¹ * F z)) 0 1 =
      Complex.I * (∫ θ in 0..anglePeriod,
        fourier  (-n)
          (θ : ParamCircle) * physicalCircleTrace F θ) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    have hz : unitCirclePt θ ≠ 0 := by
      simp
    change deriv unitCirclePt θ •
      ((unitCirclePt θ)⁻¹ ^ n * ((unitCirclePt θ)⁻¹ * F (unitCirclePt θ))) =
      Complex.I * (fourier (T := anglePeriod) (-(n : ℤ))
        (θ : ParamCircle) * physicalCircleTrace F θ)
    rw [fourierTaylor_fourier_neg_natCast]
    simp only [deriv_circleMap, smul_eq_mul, physicalCircleTrace]
    field_simp [hz]
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
    Fin.prod_const, one_pow, sub_zero, smul_eq_mul]
  rw [hcircle, localConformalFourierTaylorCoefficients, fourierCoeffOn_eq_integral]
  simp only [sub_zero, smul_eq_mul, Complex.real_smul]
  rw [sub_zero]
  have hπ  := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp [hπ, Complex.I_ne_zero]

theorem cauchyPowerSeries_unitDisk_apply_eq_fourier (z : ℂ) :
    cauchyPowerSeries F 0 1 n (fun _ => z) =
      localConformalFourierTaylorCoefficients F n * z ^ n := by
  have hcoef := cauchyPowerSeries_unitDisk_coefficient_eq_fourier F n
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
    Fin.prod_const, one_pow, one_smul] at hcoef ⊢
  rw [hcoef]
  exact mul_comm (z ^ n) (localConformalFourierTaylorCoefficients F n)

include hF in
/-- Interior Taylor matching follows from the actual Cauchy representation
on the open disk, with the coefficients already identified above. -/
theorem localConformalFourierTaylor_hasSum_on_openDisk
    {z : ℂ} (hz : z ∈ unitDisk) :
    HasSum (fun n : ℕ => localConformalFourierTaylorCoefficients F n * z ^ n) (F z) := by
  have hp := hF.hasFPowerSeriesOnBall (R := (1 : NNReal)) (by norm_num)
  have hz' : z ∈ eball (0 : ℂ) ((1 : NNReal) : ENNReal) := by
    simpa only [Metric.eball_coe, NNReal.coe_one] using hz
  
  simpa only [sub_zero, NNReal.coe_one, cauchyPowerSeries_unitDisk_apply_eq_fourier] using hp.hasSum_sub hz'

include hF hΓ in
/-- Closure matching uses continuity of the genuinely constructed collar
and the original map, so no boundary power-series identity is a premise. -/
theorem localConformalFourierTaylor_eq_on_closedDisk
    {z : ℂ} (hz : z ∈ closedDisk) :
    F z = localConformalFourierTaylorCoefficients F 0 +
      ∑' n : ℕ, localConformalFourierTaylorCoefficients F (n + 1) * z ^ (n + 1) := by
  let a := localConformalFourierTaylorCoefficients F
  
  have hEq : EqOn (fourierCollarExtension a) F unitDisk := by
    intro w hw
    have hs := localConformalFourierTaylor_hasSum_on_openDisk F hF hw
    calc
      _ = _ :=
        fourierCollarExtension_eq_taylor_on_closedDisk a (ball_subset_closedBall hw)
      _ = ∑' n : ℕ, a n * w ^ n := by
        simpa only [pow_zero, mul_one] using hs.summable.tsum_eq_zero_add.symm
      _ = _ := hs.tsum_eq
  have hEqCl  :=
    hEq.of_subset_closure (fourierCollarExtension_contDiff (localConformalFourierTaylorCoefficients_hasRapidFourierDecay F hΓ)).continuous.continuousOn
      hF.continuousOn_ball ball_subset_closedBall (by
        simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
          (Subset.rfl : closedDisk ⊆ closedDisk))
  exact (hEqCl hz).symm.trans (fourierCollarExtension_eq_taylor_on_closedDisk a hz)

include hF hΓ in
/-- Actual smooth circle data now supplies both genuine rapid decay and
the closed-disk Taylor identity needed by the Fourier collar construction. -/
theorem localConformalFourierTaylor_data :
    HasRapidFourierDecay (localConformalFourierTaylorCoefficients F) ∧
      ∀ z ∈ closedDisk,
        F z = localConformalFourierTaylorCoefficients F 0 +
          ∑' n : ℕ, localConformalFourierTaylorCoefficients F (n + 1) * z ^ (n + 1) :=
  ⟨localConformalFourierTaylorCoefficients_hasRapidFourierDecay F hΓ,
    fun _ hz => localConformalFourierTaylor_eq_on_closedDisk F hF hΓ hz⟩

include hF hΓ in
/-- A real-smooth global extension from the actual smooth circle trace.
It agrees on the whole closed disk and remains complex holomorphic inside. -/
theorem exists_smooth_holomorphic_fourier_collar_of_circleTrace :
    ∃ G : ℂ → ℂ, ContDiff ℝ ∞ G ∧
      EqOn G F closedDisk ∧ DifferentiableOn ℂ G unitDisk := by
  obtain ⟨ha, hTaylor⟩ := localConformalFourierTaylor_data F hF hΓ
  exact exists_smooth_holomorphic_fourier_collar_of_taylor ha hF.differentiableOn hTaylor

end

end PolyaNeumann
