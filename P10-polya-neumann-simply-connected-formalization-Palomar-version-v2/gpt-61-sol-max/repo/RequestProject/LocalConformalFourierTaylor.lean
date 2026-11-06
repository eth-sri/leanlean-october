module

public import RequestProject.PlanarTypes
public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

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

open scoped ContDiff

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric



/-- The actual averaged, rather than orthonormal, nonnegative circle coefficients. -/
def localConformalFourierTaylorCoefficients F (n : ℕ)  :=
  fourierCoeffOn Real.two_pi_pos (physicalCircleTrace F) (n : ℤ)

theorem periodic_iteratedDeriv_two_pi {f : ComplexCurve}
    (hp : Function.Periodic f circlePeriod) k :
    Function.Periodic (iteratedDeriv k f) circlePeriod := by
  induction k with
  | zero => simpa   using hp
  | succ k ih =>
      simpa  [iteratedDeriv_succ] using deriv_periodic ih

section
variable {f : ComplexCurve} (hf : RealSmooth f) (k : ℕ)
include f hf k

theorem contDiff_infty_iteratedDeriv_real :
    RealSmooth (iteratedDeriv k f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv k hf

theorem contDiff_infty_hasDerivAt_iteratedDeriv_real θ :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f θ) θ := by
  have hk  :=
    (contDiff_infty_iteratedDeriv_real hf k).of_le
      (show (1 : WithTop ℕ∞) ≤ ∞ from
        WithTop.coe_le_coe.mpr le_top)
  simpa  [iteratedDeriv_succ] using (hk.differentiable_one θ).hasDerivAt

end


section
variable {f : ComplexCurve} (hf : RealSmooth f) (hp : Function.Periodic f circlePeriod)
include f hf hp

/-- Genuine repeated periodic integration by parts, including frequency zero. -/
theorem periodic_contDiff_infty_fourierCoeffOn_iteratedDeriv k n :
    fourierCoeffOn Real.two_pi_pos (iteratedDeriv k f) n =
      (Complex.I * (n : ℂ)) ^ k * fourierCoeffOn Real.two_pi_pos f n := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hend : iteratedDeriv k f 0 = iteratedDeriv k f circlePeriod := by
        simpa   using (periodic_iteratedDeriv_two_pi hp k 0).symm
      rw [fourierCoeffOn_deriv
        (contDiff_infty_hasDerivAt_iteratedDeriv_real hf k)
        (contDiff_infty_iteratedDeriv_real hf (k + 1)).continuous hend, ih,
        pow_succ']
      ring

theorem periodic_contDiff_infty_norm_fourierCoeffOn_iteratedDeriv k n :
    ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv k f) n‖ =
      |(n : ℝ)| ^ k * ‖fourierCoeffOn Real.two_pi_pos f n‖ := by
  rw [periodic_contDiff_infty_fourierCoeffOn_iteratedDeriv hf hp k n,
    norm_mul, norm_pow, norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul]

/-- Absolute summability is obtained from three actual derivatives, applied
at every derivative order, rather than from a Fourier decay premise. -/
theorem periodic_contDiff_infty_summable_derivative_coefficients k :
    Summable (fun n : ℤ =>
      ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv (k + 1) f) n‖) := by
  apply summable_norm_fourierCoeffOn_deriv
    (contDiff_infty_hasDerivAt_iteratedDeriv_real hf k)
    (contDiff_infty_hasDerivAt_iteratedDeriv_real hf (k + 1))
    (contDiff_infty_hasDerivAt_iteratedDeriv_real hf (k + 1 + 1))
    (contDiff_infty_iteratedDeriv_real hf (k + 1 + 1 + 1)).continuous
  · simpa   using (periodic_iteratedDeriv_two_pi hp k 0).symm
  · simpa   using (periodic_iteratedDeriv_two_pi hp (k + 1) 0).symm
  · simpa   using (periodic_iteratedDeriv_two_pi hp (k + 1 + 1) 0).symm

/-- Every polynomially weighted positive tail of the genuine averaged
Fourier coefficients is summable.  The zeroth mode is not discarded. -/
theorem periodic_contDiff_infty_hasRapidFourierDecay :
    HasRapidFourierDecay (fun n : ℕ => fourierCoeffOn Real.two_pi_pos f (n : ℤ)) := by
  intro k
  have hi : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℤ)) := by
    simp_all [Function.Injective]
  have hs := (periodic_contDiff_infty_summable_derivative_coefficients hf hp k).comp_injective hi
  have hs' : Summable (fun n : ℕ =>
      ‖fourierCoeffOn Real.two_pi_pos f ((n + 1 : ℕ) : ℤ)‖ *
        ((n + 1 : ℕ) : ℝ) ^ (k + 1)) := by
    refine hs.congr fun n => ?_
    change ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv (k + 1) f)
      ((n + 1 : ℕ))‖ = _
    rw [periodic_contDiff_infty_norm_fourierCoeffOn_iteratedDeriv hf hp (k + 1)]
    simp only [Int.cast_natCast, abs_of_nonneg
      (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
    ring
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _)
    (pow_nonneg (Nat.cast_nonneg _) _)) (fun n => ?_) hs'
  have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    norm_num
  have hnonneg : (0 : ℝ) ≤
      ‖fourierCoeffOn Real.two_pi_pos f ((n + 1 : ℕ) : ℤ)‖ *
        ((n + 1 : ℕ) : ℝ) ^ k :=
    mul_nonneg (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  simpa only [mul_one, pow_succ, mul_assoc] using
    mul_le_mul_of_nonneg_left hbase hnonneg

end


theorem localConformalFourierTaylorCoefficients_hasRapidFourierDecay
    F (hΓ : RealSmooth (physicalCircleTrace F)) :
    HasRapidFourierDecay (localConformalFourierTaylorCoefficients F) :=
  periodic_contDiff_infty_hasRapidFourierDecay hΓ (physicalCircleTrace_periodic F)

private theorem fourierTaylor_fourier_neg_natCast (n : ℕ) (θ : ℝ) :
    fourier (T := 2 * Real.pi) (-(n : ℤ)) (θ : AddCircle circlePeriod) =
      (unitCircleMap θ)⁻¹ ^ n := by
  rw [fourier_neg, common_physicalHardy_fourier_natCast, map_pow,
    ← Complex.inv_eq_conj (z := unitCircleMap θ)
      (by simp  )]

/-- The Cauchy coefficient is exactly the averaged angular coefficient.
This calculation does not require any holomorphicity hypothesis. -/
theorem cauchyPowerSeries_unitDisk_coefficient_eq_fourier
    F n :
    cauchyPowerSeries F 0 1 n (fun _ => (1 : ℂ)) =
      localConformalFourierTaylorCoefficients F n := by
  have hcircle : circleIntegral (fun z : ℂ => z⁻¹ ^ n * (z⁻¹ * F z)) 0 1 =
      Complex.I * (∫ θ in (0 : ℝ)..circlePeriod,
        fourier (T := 2 * Real.pi) (-(n : ℤ))
          (θ : AddCircle circlePeriod) * physicalCircleTrace F θ) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    have hz : unitCircleMap θ ≠ 0 := by
      simp_all
    change deriv unitCircleMap θ •
      ((unitCircleMap θ)⁻¹ ^ n * ((unitCircleMap θ)⁻¹ * F (unitCircleMap θ))) =
      Complex.I * (fourier (T := 2 * Real.pi) (-n)
        θ * physicalCircleTrace F θ)
    rw [fourierTaylor_fourier_neg_natCast]
    simp  [physicalCircleTrace]
    field_simp
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
    Fin.prod_const, one_pow, sub_zero, smul_eq_mul]
  rw [hcircle, localConformalFourierTaylorCoefficients, fourierCoeffOn_eq_integral]
  simp only [sub_zero, smul_eq_mul, Complex.real_smul]
  rw [sub_zero]
  have hπ  := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp [hπ, Complex.I_ne_zero]

theorem cauchyPowerSeries_unitDisk_apply_eq_fourier
    F n z :
    cauchyPowerSeries F 0 1 n (fun _ => z) =
      localConformalFourierTaylorCoefficients F n * z ^ n := by
  have hcoef := cauchyPowerSeries_unitDisk_coefficient_eq_fourier F n
  simp_all  <;> ring

/-- Interior Taylor matching follows from the actual Cauchy representation
on the open disk, with the coefficients already identified above. -/
theorem localConformalFourierTaylor_hasSum_on_openDisk
    F (hF : DiffContOnCl ℂ F unitDisk)
     (hz : z ∈ unitDisk) :
    HasSum (fun n : ℕ => localConformalFourierTaylorCoefficients F n * z ^ n) (F z) := by
  have hp := hF.hasFPowerSeriesOnBall (R := 1) (by norm_num)
  have hz' : z ∈ eball (0 : ℂ) ((1 : NNReal) : ENNReal) := by
    tauto
  have hs := hp.hasSum_sub hz'
  simpa only [sub_zero, NNReal.coe_one, cauchyPowerSeries_unitDisk_apply_eq_fourier] using hs

section
variable (F ) (hF : DiffContOnCl ℂ F unitDisk) (hΓ : RealSmooth (physicalCircleTrace F))
include F hF hΓ

/-- Closure matching uses continuity of the genuinely constructed collar
and the original map, so no boundary power-series identity is a premise. -/
theorem localConformalFourierTaylor_eq_on_closedDisk
     (hz : z ∈ closedUnitDisk) :
    F z = localConformalFourierTaylorCoefficients F 0 +
      ∑' n : ℕ, localConformalFourierTaylorCoefficients F (n + 1) * z ^ (n + 1) := by
  let a := localConformalFourierTaylorCoefficients F
  have ha  :=
    localConformalFourierTaylorCoefficients_hasRapidFourierDecay F hΓ
  have hEq : EqOn (fourierCollarExtension a) F unitDisk := by
    intro w hw
    have hs := localConformalFourierTaylor_hasSum_on_openDisk F hF hw
    calc
      fourierCollarExtension a w = a 0 + ∑' n : ℕ, a (n + 1) * w ^ (n + 1) :=
        fourierCollarExtension_eq_taylor_on_closedDisk a (ball_subset_closedBall hw)
      _ = ∑' n : ℕ, a n * w ^ n := by
        simpa   using hs.summable.tsum_eq_zero_add.symm
      _ = F w := hs.tsum_eq
  have hEqCl  :=
    hEq.of_subset_closure (fourierCollarExtension_contDiff ha).continuous.continuousOn
      hF.continuousOn_ball ball_subset_closedBall (by
        simpa  [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
          Subset.rfl)
  exact (hEqCl hz).symm.trans (fourierCollarExtension_eq_taylor_on_closedDisk a hz)

/-- Actual smooth circle data now supplies both genuine rapid decay and
the closed-disk Taylor identity needed by the Fourier collar construction. -/
theorem localConformalFourierTaylor_data :
    HasRapidFourierDecay (localConformalFourierTaylorCoefficients F) ∧
      ∀ z ∈ closedUnitDisk,
        F z = localConformalFourierTaylorCoefficients F 0 +
          ∑' n : ℕ, localConformalFourierTaylorCoefficients F (n + 1) * z ^ (n + 1) :=
  ⟨localConformalFourierTaylorCoefficients_hasRapidFourierDecay F hΓ,
    fun _ hz => localConformalFourierTaylor_eq_on_closedDisk F hF hΓ hz⟩

/-- A real-smooth global extension from the actual smooth circle trace.
It agrees on the whole closed disk and remains complex holomorphic inside. -/
theorem exists_smooth_holomorphic_fourier_collar_of_circleTrace :
    ∃ G : PlaneMap, RealSmooth G ∧
      EqOn G F closedUnitDisk ∧ DifferentiableOn ℂ G unitDisk := by
  obtain ⟨ha, hTaylor⟩ := localConformalFourierTaylor_data F hF hΓ
  exact exists_smooth_holomorphic_fourier_collar_of_taylor ha hF.differentiableOn hTaylor

end


end PolyaNeumann
