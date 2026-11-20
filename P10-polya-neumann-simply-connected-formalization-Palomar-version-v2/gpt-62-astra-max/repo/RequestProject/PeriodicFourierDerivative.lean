module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.CutFourier
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import RequestProject.PlanarNotation

/-!
# A continuous periodic Fourier derivative is the actual derivative

The coefficient identity is inverted by constructing a genuine interval
primitive. Its mean-zero derivative makes that primitive periodic. Fourier
uniqueness then shows that its difference from the original function is a
constant, which is fixed by the value at the boundary origin. No absolute
continuity or differentiability of the original function is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set

private theorem periodicDerivative_fourierCoeffOn_sub
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    angleCoeff (fun θ => f θ - g θ) n =
      angleCoeff f n - angleCoeff g n := by
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
    {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f anglePeriod)
    (hcoeff : ∀ n : ℤ, n ≠ 0 → angleCoeff f n = 0)
    (θ : ℝ) : f θ = f 0 := by
  let F : C(ParamCircle, ℂ) := ⟨hper.lift, by
    refine continuous_quot_lift _ hf⟩
  have hF (x : ℝ) : F x = f x := rfl
  have hc (n : ℤ) : fourierCoeff F n = fourierCoeffOn Real.two_pi_pos f n := by
    rw [fourierCoeff_eq_intervalIntegral _ n 0, fourierCoeffOn_eq_integral]
    simp [hF]
  
  have hvalue (x : ℝ) : f x = fourierCoeff F 0 := by
    have hsum := has_pointwise_sum_fourier_series_of_summable (f := F) (by
        refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
        rw [hc n]
        grind)
      x
    
    refine (hF x).symm.trans (hsum.unique ?_)
    convert hasSum_single (f := fun n : ℤ =>
      fourierCoeff F n • fourier n (x : ParamCircle)) 0
      (fun n hn => by
        simp [*]) using 1; simp
  simp [*]

/-- The coefficient derivative identity forces the derivative's true integral
over one full period to vanish; the zero Fourier mode is retained. -/
theorem integral_eq_zero_of_periodic_fourier_derivative
    {v d : ℝ → ℂ}
    (hcoeff : ∀ n : ℤ, angleCoeff d n =
      (Complex.I * (n : ℂ)) * angleCoeff v n) :
    (∫ₚ θ, d θ) = 0 := by
  have h0 := hcoeff 0
  
  rw [fourierCoeffOn_eq_integral] at h0
  
  aesop

/-- The true interval primitive reconstructs the continuous periodic function
from its Fourier derivative, with its actual initial value. -/
theorem eq_add_integral_of_periodic_fourier_derivative
    {v d : ℝ → ℂ} (hv : Continuous v) (hd : Continuous d)
    (hvper : Function.Periodic v anglePeriod)
    (hdper : Function.Periodic d anglePeriod)
    (hcoeff : ∀ n : ℤ, angleCoeff d n =
      (Complex.I * (n : ℂ)) * angleCoeff v n)
    (θ : ℝ) : v θ = v 0 + ∫ s in (0 : ℝ)..θ, d s := by
  let P  := fun t => ∫ s in 0..t, d s
  have hP : Continuous P :=
    (by fun_prop)
  have hPd (t : ℝ)  :=
    intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable 0 t)
      hd.aestronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt
  
  have hPper : Function.Periodic P anglePeriod := by
    intro t
    change (∫ s in (0 : ℝ)..t + anglePeriod, d s) = ∫ s in (0 : ℝ)..t, d s
    rw [hdper.intervalIntegral_add_eq_add 0 t
      hd.intervalIntegrable]
    simp [(integral_eq_zero_of_periodic_fourier_derivative hcoeff)]
  have hPc (n : ℤ) := fourierCoeffOn_deriv hPd hd (by simpa only [zero_add] using
      (hPper 0).symm) n
  have hncoeff (n : ℤ) (hn : n ≠ 0) :
      angleCoeff v n = angleCoeff P n := by
    have hmult := (hcoeff n).symm.trans (hPc n)
    exact mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn)) hmult
  have hconst := eq_at_zero_of_periodic_nonzero_fourier_eq_zero (hv.sub hP)
    (hvper.sub hPper) (fun n hn => by
      rw [show v - P = fun θ => v θ - P θ from rfl,
        periodicDerivative_fourierCoeffOn_sub hv hP n, hncoeff n hn, sub_self]) θ
  change _ = v 0 - P 0 at hconst
  have hP0 : P 0 = 0 := by simp [P]
  rw [hP0, sub_zero] at hconst
  exact sub_eq_iff_eq_add.mp hconst

/-- The continuous periodic Fourier derivative is the actual derivative at
every real parameter, not merely an almost-everywhere representative. -/
theorem hasDerivAt_of_periodic_fourier_derivative
    {v d : ℝ → ℂ} (hv : Continuous v) (hd : Continuous d)
    (hvper : Function.Periodic v anglePeriod)
    (hdper : Function.Periodic d anglePeriod)
    (hcoeff : ∀ n : ℤ, angleCoeff d n =
      (Complex.I * (n : ℂ)) * angleCoeff v n)
    (θ : ℝ) : HasDerivAt v (d θ) θ := by
  
  have heq : v = fun t => v 0 + ∫ s in 0..t, d s := by
    funext t
    exact eq_add_integral_of_periodic_fourier_derivative hv hd hvper hdper hcoeff t
  rw [heq]
  have h := (hasDerivAt_const θ (v 0)).add (intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable 0 θ)
    hd.aestronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt)
  rw [zero_add] at h
  exact h

end PolyaNeumann

end
