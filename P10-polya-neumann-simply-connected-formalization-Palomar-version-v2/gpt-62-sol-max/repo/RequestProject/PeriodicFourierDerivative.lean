module

public import RequestProject.CircleFourier
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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set


/-- A continuous periodic function with zero nonconstant Fourier coefficients
has its actual constant value everywhere, including the boundary origin. -/
theorem eq_at_zero_of_periodic_nonzero_fourier_eq_zero
    {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f (2 * Real.pi))
    (hcoeff : ∀ n : ℤ, n ≠ 0 → fourierCoeffOn Real.two_pi_pos f n = 0)
    (θ : ℝ) : f θ = f 0 := by
  let F : C(AddCircle (2 * Real.pi), ℂ) := ⟨hper.lift, by
    refine continuous_quot_lift _ hf⟩
  have hF (x : ℝ) : F (x : AddCircle (2 * Real.pi)) = f x := rfl
  have hc (n : ℤ) : fourierCoeff F n = fourierCoeffOn Real.two_pi_pos f n := by
    rw [fourierCoeff_eq_intervalIntegral _ n 0, fourierCoeffOn_eq_integral]
    simp_all
  have hs : Summable (fourierCoeff (F : AddCircle (2 * Real.pi) → ℂ)) := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp_all
  have hvalue (x : ℝ) : f x = fourierCoeff F 0 := by
    have hsum := has_pointwise_sum_fourier_series_of_summable (f := F) hs
      (x : AddCircle (2 * Real.pi))
    have hsingle : HasSum
        (fun n : ℤ => fourierCoeff F n • fourier n (x : AddCircle (2 * Real.pi)))
        (fourierCoeff F 0) := by
      convert hasSum_single (f := fun n : ℤ =>
        fourierCoeff F n • fourier n (x : AddCircle (2 * Real.pi))) 0
        (fun n hn => by simp_all) using 1; simp
    exact (hF x).symm.trans (hsum.unique hsingle)
  simp_all

/-- The coefficient derivative identity forces the derivative's true integral
over one full period to vanish; the zero Fourier mode is retained. -/
theorem integral_eq_zero_of_periodic_fourier_derivative
    {v d : ℝ → ℂ}
    (hcoeff : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos d n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos v n) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), d θ) = 0 := by
  have h0 := hcoeff 0
  simp_all [zero_mul, fourierCoeffOn_eq_integral, neg_zero, fourier_zero, one_smul, sub_zero]


end PolyaNeumann

end
