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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology ComplexConjugate ContDiff


variable {f : ℝ → ℂ}

/-- The actual averaged, rather than orthonormal, nonnegative circle coefficients. -/
def localConformalFourierTaylorCoefficients (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  fourierCoeffOn Real.two_pi_pos (physicalCircleTrace F) (n : ℤ)

theorem periodic_iteratedDeriv_two_pi 
    (hp : Function.Periodic f (2 * Real.pi)) k :
    Function.Periodic (iteratedDeriv k f) (2 * Real.pi) := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
      simpa [iteratedDeriv_succ] using deriv_periodic ih

theorem contDiff_infty_iteratedDeriv_real 
    (hf : ContDiff ℝ ∞ f) k :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv k hf

theorem contDiff_infty_hasDerivAt_iteratedDeriv_real 
    (hf : ContDiff ℝ ∞ f) k θ :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f θ) θ := by
  simpa [iteratedDeriv_succ] using (((contDiff_infty_iteratedDeriv_real hf k).of_le (WithTop.coe_le_coe.mpr le_top)).differentiable_one θ).hasDerivAt

theorem periodic_contDiff_infty_norm_fourierCoeffOn_iteratedDeriv 
    (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (2 * Real.pi)) k n :
    ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv k f) n‖ =
      |(n : ℝ)| ^ k * ‖fourierCoeffOn Real.two_pi_pos f n‖ := by
  rw [show fourierCoeffOn Real.two_pi_pos (iteratedDeriv k f) n = (Complex.I * (n : ℂ)) ^ k * fourierCoeffOn Real.two_pi_pos f n by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [fourierCoeffOn_deriv
          (contDiff_infty_hasDerivAt_iteratedDeriv_real hf k)
          (contDiff_infty_iteratedDeriv_real hf (k + 1)).continuous (by
            simpa using (periodic_iteratedDeriv_two_pi hp k 0).symm), ih,
          pow_succ']
        ring,
    norm_mul, norm_pow, norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul]

/-- Every polynomially weighted positive tail of the genuine averaged
Fourier coefficients is summable.  The zeroth mode is not discarded. -/
theorem periodic_contDiff_infty_hasRapidFourierDecay 
    (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (2 * Real.pi)) :
    HasRapidFourierDecay (fun n => fourierCoeffOn Real.two_pi_pos f (n : ℤ)) := by
  intro k
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _)
    (pow_nonneg (Nat.cast_nonneg _) _)) (fun n => ?_) (show Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos f ((n + 1 : ℕ) : ℤ)‖ * (n + 1 : ℕ) ^ (k + 1)) by
      refine ((show Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv (k + 1) f) n‖) by
        apply summable_norm_fourierCoeffOn_deriv
          (contDiff_infty_hasDerivAt_iteratedDeriv_real hf k)
          (contDiff_infty_hasDerivAt_iteratedDeriv_real hf (k + 1))
          (contDiff_infty_hasDerivAt_iteratedDeriv_real hf (k + 1 + 1))
          (contDiff_infty_iteratedDeriv_real hf (k + 1 + 1 + 1)).continuous
        · simpa using (periodic_iteratedDeriv_two_pi hp k 0).symm
        · simpa using (periodic_iteratedDeriv_two_pi hp (k + 1) 0).symm
        · simpa using (periodic_iteratedDeriv_two_pi hp (k + 1 + 1) 0).symm).comp_injective (show Function.Injective (fun n => ((n + 1 : ℕ) : ℤ)) by
            intro m n h
            exact Nat.add_right_cancel (Int.ofNat_injective h))).congr fun n => ?_
      change ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv (k + 1) f)
        (n + 1 : ℕ)‖ = _
      rw [periodic_contDiff_infty_norm_fourierCoeffOn_iteratedDeriv hf hp (k + 1)]
      simp only [Int.cast_natCast, abs_of_nonneg
        (show 0 ≤ ((n + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
      ring)
  simpa only [mul_one, pow_succ, mul_assoc] using
    mul_le_mul_of_nonneg_left (show 1 ≤ ((n + 1 : ℕ) : ℝ) by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (mul_nonneg (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))

theorem localConformalFourierTaylorCoefficients_hasRapidFourierDecay
    F (hΓ : ContDiff ℝ ∞ (physicalCircleTrace F)) :
    HasRapidFourierDecay (localConformalFourierTaylorCoefficients F) :=
  periodic_contDiff_infty_hasRapidFourierDecay hΓ (physicalCircleTrace_periodic F)

local notation "Φ0" => circleMap 0 1

private theorem fourierTaylor_fourier_natCast (n : ℕ) (θ : ℝ) :
    fourier (T := 2 * Real.pi) (n : ℤ) (θ : AddCircle (2 * Real.pi)) =
      (Φ0 θ) ^ n := by
  rw [fourier_coe_apply, circleMap_zero_pow]
  simp [circleMap_zero]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

private theorem fourierTaylor_fourier_neg_natCast (n : ℕ) (θ : ℝ) :
    fourier (T := 2 * Real.pi) (-(n : ℤ)) (θ : AddCircle (2 * Real.pi)) =
      (Φ0 θ)⁻¹ ^ n := by
  rw [fourier_neg, fourierTaylor_fourier_natCast, map_pow,
    ← Complex.inv_eq_conj (z := Φ0 θ)
      (by simp)]

theorem cauchyPowerSeries_unitDisk_apply_eq_fourier
    F n z :
    cauchyPowerSeries F 0 1 n (fun _ => z) =
      localConformalFourierTaylorCoefficients F n * z ^ n := by
  have hcoef : cauchyPowerSeries F 0 1 n (fun _ => 1) = localConformalFourierTaylorCoefficients F n := by
    simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
      Fin.prod_const, one_pow, sub_zero, smul_eq_mul]
    rw [show circleIntegral (fun z => z⁻¹ ^ n * (z⁻¹ * F z)) 0 1 = Complex.I * (∫ θ in 0..(2 * Real.pi), fourier (T := 2 * Real.pi) (-n) (θ : AddCircle (2 * Real.pi)) * physicalCircleTrace F θ) by
      rw [circleIntegral, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      change deriv (Φ0) θ •
        ((Φ0 θ)⁻¹ ^ n * ((Φ0 θ)⁻¹ * F (Φ0 θ))) =
        Complex.I * (fourier (T := 2 * Real.pi) (-n)
          (θ : AddCircle (2 * Real.pi)) * physicalCircleTrace F θ)
      rw [fourierTaylor_fourier_neg_natCast]
      simp [physicalCircleTrace]
      field_simp [show Φ0 θ ≠ 0 by
        intro h
        have hh := norm_circleMap_zero 1 θ
        simp only [h, norm_zero, abs_one] at hh
        exact zero_ne_one hh], localConformalFourierTaylorCoefficients, fourierCoeffOn_eq_integral]
    simp only [sub_zero, smul_eq_mul, Complex.real_smul]
    rw [sub_zero]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
    Fin.prod_const, one_pow, one_smul] at hcoef ⊢
  rw [hcoef]
  exact mul_comm (z ^ n) (localConformalFourierTaylorCoefficients F n)

/-- Interior Taylor matching follows from the actual Cauchy representation
on the open disk, with the coefficients already identified above. -/
local notation "Φ1" => ball 0 1

theorem localConformalFourierTaylor_hasSum_on_openDisk
    F (hF : DiffContOnCl ℂ F (Φ1))
     (hz : z ∈ Φ1) :
    HasSum (fun n => localConformalFourierTaylorCoefficients F n * z ^ n) (F z) := by
  have hs := (hF.hasFPowerSeriesOnBall (R := 1) (by norm_num)).hasSum_sub (by
    simpa only [Metric.eball_coe, NNReal.coe_one] using hz)
  simpa only [sub_zero, NNReal.coe_one, cauchyPowerSeries_unitDisk_apply_eq_fourier] using hs

/-- Closure matching uses continuity of the genuinely constructed collar
and the original map, so no boundary power-series identity is a premise. -/
theorem localConformalFourierTaylor_eq_on_closedDisk
    F (hF : DiffContOnCl ℂ F (Φ1))
    (hΓ : ContDiff ℝ ∞ (physicalCircleTrace F))
     (hz : z ∈ closedBall 0 1) :
    F z = localConformalFourierTaylorCoefficients F 0 +
      ∑' n : ℕ, localConformalFourierTaylorCoefficients F (n + 1) * z ^ (n + 1) := by
  let a := localConformalFourierTaylorCoefficients F
  have hEqCl :=
    (show EqOn (fourierCollarExtension a) F (Φ1) by
      intro w hw
      have hs := localConformalFourierTaylor_hasSum_on_openDisk F hF hw
      calc
        _ = _ :=
          fourierCollarExtension_eq_taylor_on_closedDisk a (ball_subset_closedBall hw)
        _ = _ := by
          simpa using hs.summable.tsum_eq_zero_add.symm
        _ = _ := hs.tsum_eq).of_subset_closure (fourierCollarExtension_contDiff (localConformalFourierTaylorCoefficients_hasRapidFourierDecay F hΓ)).continuous.continuousOn
      hF.continuousOn_ball ball_subset_closedBall (by
        simpa [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
          (Subset.rfl : closedBall (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1))
  exact (hEqCl hz).symm.trans (fourierCollarExtension_eq_taylor_on_closedDisk a hz)

/-- A real-smooth global extension from the actual smooth circle trace.
It agrees on the whole closed disk and remains complex holomorphic inside. -/
theorem exists_smooth_holomorphic_fourier_collar_of_circleTrace
    F (hF : DiffContOnCl ℂ F (Φ1))
    (hΓ : ContDiff ℝ ∞ (physicalCircleTrace F)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ ∞ G ∧
      EqOn G F (closedBall 0 1) ∧ DifferentiableOn ℂ G (Φ1) := by
  obtain ⟨ha, hTaylor⟩ := (⟨localConformalFourierTaylorCoefficients_hasRapidFourierDecay F hΓ, fun _ hz => localConformalFourierTaylor_eq_on_closedDisk F hF hΓ hz⟩ : HasRapidFourierDecay (localConformalFourierTaylorCoefficients F) ∧ ∀ z ∈ closedBall 0 1, F z = localConformalFourierTaylorCoefficients F 0 + ∑' n : ℕ, localConformalFourierTaylorCoefficients F (n + 1) * z ^ (n + 1))
  exact exists_smooth_holomorphic_fourier_collar_of_taylor ha hF.differentiableOn hTaylor

end PolyaNeumann
