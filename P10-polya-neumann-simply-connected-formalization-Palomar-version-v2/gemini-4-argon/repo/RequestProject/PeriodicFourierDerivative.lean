module

public import RequestProject.CutFourier
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# A continuous periodic Fourier derivative is the actual derivative

The coefficient identity is inverted by constructing a genuine interval
primitive. Its mean-zero derivative makes that primitive periodic. Fourier
uniqueness then shows that its difference from the original function is a
constant, which is fixed by the value at the boundary origin. No absolute
continuity or differentiability of the original function is assumed.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set

local instance periodicDerivativeTwoPiPos : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

private theorem periodicDerivative_fourierCoeffOn_sub
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) n :
    fourierCoeffOn Real.two_pi_pos (fun θ => f θ - g θ) n =
      fourierCoeffOn Real.two_pi_pos f n - fourierCoeffOn Real.two_pi_pos g n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    fourierCoeffOn_eq_integral, ← smul_sub, ← intervalIntegral.integral_sub]
  · simp_rw [smul_sub]
  · exact (((map_continuous (fourier (-n))).comp continuous_quotient_mk').smul
      hf).intervalIntegrable _ _
  · exact (((map_continuous (fourier (-n))).comp continuous_quotient_mk').smul
      hg).intervalIntegrable _ _

/-- A continuous periodic function with zero nonconstant Fourier coefficients
has its actual constant value everywhere, including the boundary origin. -/
theorem eq_at_zero_of_periodic_nonzero_fourier_eq_zero
    {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f (2 * Real.pi))
    (hcoeff : ∀ n : ℤ, n ≠ 0 → fourierCoeffOn Real.two_pi_pos f n = 0)
    θ : f θ = f 0 := by
  let F : C(AddCircle (2 * Real.pi), ℂ) := ⟨hper.lift, by
    refine continuous_quot_lift _ hf⟩
  have hF (x : ℝ) : F (x : AddCircle (2 * Real.pi)) = f x := rfl
  have hc (n : ℤ) : fourierCoeff F n = fourierCoeffOn Real.two_pi_pos f n := by
    rw [fourierCoeff_eq_intervalIntegral _ n 0, fourierCoeffOn_eq_integral]
    simp [hF]
  have hvalue x : f x = fourierCoeff F 0 := by
    exact (hF x).symm.trans ((has_pointwise_sum_fourier_series_of_summable (f := F) (by
      refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
      rw [hc n]
      exact hcoeff n (by simpa using hn)) (x : AddCircle (2 * Real.pi))).unique (by
      convert hasSum_single (f := fun n =>
        fourierCoeff F n • fourier n (x : AddCircle (2 * Real.pi))) 0
        (fun n hn => by
          rw [hc n, hcoeff n hn, zero_smul]) using 1; simp))
  exact (hvalue θ).trans (hvalue 0).symm

/-- The coefficient derivative identity forces the derivative's true integral
over one full period to vanish; the zero Fourier mode is retained. -/
theorem integral_eq_zero_of_periodic_fourier_derivative
    
    (hcoeff : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos d n =
      (Complex.I * n) * fourierCoeffOn Real.two_pi_pos v n) :
    (∫ θ in 0..(2 * Real.pi), d θ) = 0 := by
  have h0 := hcoeff 0
  simp at h0
  rw [fourierCoeffOn_eq_integral] at h0
  simp only [neg_zero, fourier_zero, one_smul, sub_zero] at h0
  exact (smul_eq_zero.mp h0).resolve_left (by positivity)

/-- The continuous periodic Fourier derivative is the actual derivative at
every real parameter, not merely an almost-everywhere representative. -/
theorem hasDerivAt_of_periodic_fourier_derivative
     (hv : Continuous v) (hd : Continuous d)
    (hvper : Function.Periodic v (2 * Real.pi))
    (hdper : Function.Periodic d (2 * Real.pi))
    (hcoeff : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos d n =
      (Complex.I * n) * fourierCoeffOn Real.two_pi_pos v n)
    θ : HasDerivAt v (d θ) θ := by
  rw [show v = fun t => v 0 + ∫ s in 0..t, d s by
    funext t
    exact (by
      let P : ℝ → ℂ := fun t => ∫ s in 0..t, d s
      have hP : Continuous P :=
        intervalIntegral.continuous_primitive (fun x y => hd.intervalIntegrable x y) 0
      have hPd t : HasDerivAt P (d t) t :=
        intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable 0 t)
          hd.aestronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt
      have hPper : Function.Periodic P (2 * Real.pi) := by
        intro t
        change (∫ s in 0..t + 2 * Real.pi, d s) = ∫ s in 0..t, d s
        rw [hdper.intervalIntegral_add_eq_add 0 t
          (fun x y => hd.intervalIntegrable x y)]
        simp [integral_eq_zero_of_periodic_fourier_derivative hcoeff]
      have hPc n : fourierCoeffOn Real.two_pi_pos d n =
          Complex.I * n * fourierCoeffOn Real.two_pi_pos P n := by
        exact fourierCoeffOn_deriv hPd hd (by simpa using
          (hPper 0).symm) n
      have hncoeff n (hn : n ≠ 0) :
          fourierCoeffOn Real.two_pi_pos v n = fourierCoeffOn Real.two_pi_pos P n := by
        exact mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn)) ((hcoeff n).symm.trans (hPc n))
      have hconst := eq_at_zero_of_periodic_nonzero_fourier_eq_zero (hv.sub hP)
        (hvper.sub hPper) (fun n hn => by
          rw [show v - P = fun t => v t - P t from rfl,
            periodicDerivative_fourierCoeffOn_sub hv hP n, hncoeff n hn, sub_self]) t
      change v t - P t = v 0 - P 0 at hconst
      rw [show P 0 = 0 by simp [P], sub_zero] at hconst
      exact sub_eq_iff_eq_add.mp hconst)]
  have h := (hasDerivAt_const θ (v 0)).add (intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable 0 θ) hd.aestronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt)
  rw [zero_add] at h
  exact h

end PolyaNeumann

end
