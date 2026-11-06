module

public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

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

public section



namespace PolyaNeumann

open MeasureTheory Set



/-- A continuous periodic function with zero nonconstant Fourier coefficients
has its actual constant value everywhere, including the boundary origin. -/
theorem eq_at_zero_of_periodic_nonzero_fourier_eq_zero
    {f : ComplexCurve} (hf : Continuous f) (hper : Function.Periodic f circlePeriod)
    (hcoeff : ∀ n : ℤ, n ≠ 0 → fourierCoeffOn Real.two_pi_pos f n = 0)
    θ : f θ = f 0 := by
  let F : C(AddCircle circlePeriod, ℂ) := ⟨hper.lift, by
    refine continuous_quot_lift _ hf⟩
  have hF (x : ℝ) : F (x : AddCircle circlePeriod) = f x := rfl
  have hc (n : ℤ) : fourierCoeff F n = fourierCoeffOn Real.two_pi_pos f n := by
    rw [fourierCoeff_eq_intervalIntegral _ n 0, fourierCoeffOn_eq_integral]
    simp_all
  have hs : Summable (fourierCoeff (F : AddCircle circlePeriod → ℂ)) := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp_all
  have hvalue (x : ℝ) : f x = fourierCoeff F 0 := by
    have hsum := has_pointwise_sum_fourier_series_of_summable (f := F) hs
      x
    have hsingle : HasSum
        (fun n : ℤ => fourierCoeff F n • fourier n (x : AddCircle circlePeriod))
        (fourierCoeff F 0) := by
      convert hasSum_single (f := fun n : ℤ =>
        fourierCoeff F n • fourier n x) 0
        (fun n hn => by
          rw [hc n, hcoeff n hn, zero_smul]) using 1; simp
    exact (hF x).symm.trans (hsum.unique hsingle)
  exact (hvalue θ).trans (hvalue 0).symm

/-- The coefficient derivative identity forces the derivative's true integral
over one full period to vanish; the zero Fourier mode is retained. -/
theorem integral_eq_zero_of_periodic_fourier_derivative
    
    (hcoeff : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos d n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos v n) :
    (∫ θ in (0 : ℝ)..circlePeriod, d θ) = 0 := by
  have h0 := hcoeff 0
  rw [fourierCoeffOn_eq_integral] at h0
  simp_all

section
variable {v d : ComplexCurve} (hv : Continuous v) (hd : Continuous d) (hvper : Function.Periodic v circlePeriod) (hdper : Function.Periodic d circlePeriod) (hcoeff : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos d n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos v n) (θ : ℝ)
include v d hv hd hvper hdper hcoeff θ

/-- The true interval primitive reconstructs the continuous periodic function
from its Fourier derivative, with its actual initial value. -/
theorem eq_add_integral_of_periodic_fourier_derivative : v θ = v 0 + ∫ s in (0 : ℝ)..θ, d s := by
  let P  := fun t => ∫ s in (0)..t, d s
  have hP : Continuous P :=
    intervalIntegral.continuous_primitive hd.intervalIntegrable 0
  have hPd (t : ℝ)  :=
    intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable 0 t)
      hd.aestronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt
  have hmean := integral_eq_zero_of_periodic_fourier_derivative hcoeff
  have hPper : Function.Periodic P circlePeriod := by
    intro t
    change (∫ s in (0)..t + 2 * Real.pi, d s) = ∫ s in (0)..t, d s
    rw [hdper.intervalIntegral_add_eq_add 0 t
      hd.intervalIntegrable]
    simp  [hmean]
  have hPc (n : ℤ) : fourierCoeffOn Real.two_pi_pos d n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos P n := by
    exact fourierCoeffOn_deriv hPd hd (by measurability) n
  have hncoeff (n : ℤ) (hn : n ≠ 0) :
      fourierCoeffOn Real.two_pi_pos v n = fourierCoeffOn Real.two_pi_pos P n := by
    have hmult := (hcoeff n).symm.trans (hPc n)
    simp_all
  have hconst := eq_at_zero_of_periodic_nonzero_fourier_eq_zero (hv.sub hP)
    (hvper.sub hPper) (fun n hn => by
      rw [show v - P = fun θ => v θ - P θ from rfl,
        fourierCoeffOn_sub_of_continuousOn hv.continuousOn hP.continuousOn n, hncoeff n hn, sub_self]) θ
  change v θ - P θ = v 0 - P 0 at hconst
  have hP0 : P 0 = 0 := by simp [P]
  grind

/-- The continuous periodic Fourier derivative is the actual derivative at
every real parameter, not merely an almost-everywhere representative. -/
theorem hasDerivAt_of_periodic_fourier_derivative : HasDerivAt v (d θ) θ := by
  have hp := intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable 0 θ)
    hd.aestronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt
  have heq : v = fun t => v 0 + ∫ s in (0 : ℝ)..t, d s := by
    grind only [eq_add_integral_of_periodic_fourier_derivative]
  rw [heq]
  have h := (hasDerivAt_const θ (v 0)).add hp
  rw [zero_add] at h
  exact h

end


end PolyaNeumann
