module

public import RequestProject.HardyAntiderivative
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Fourier Hardy primitive is the actual boundary integral

For continuous periodic functions with absolutely summable Fourier
coefficients, the existing coefficient operator `antiPrim` reconstructs
the integral of their product from the boundary origin. Strictly negative
multiplier support and nonpositive input support remove the constant
coefficient of the product. An H¹ Fourier input satisfies the required
absolute summability by the existing point-evaluation estimate.

The conclusion concerns the actual functions and ordinary parameter
measure. It does not assume their derivatives, elliptic regularity, or
existence of conformal coordinates.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Filter
open scoped Real

local instance hardyPrimitiveTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Pointwise Fourier reconstruction in the averaged coefficient convention. -/
def hardyFourierTrace (c : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑' n, c n * fourier (T := 2 * Real.pi) n (θ : AddCircle (2 * Real.pi))

variable (n : ℤ) (θ : ℝ)

theorem hardyFourierTrace_periodic (c : ℤ → ℂ) :
    Function.Periodic (hardyFourierTrace c) (2 * Real.pi) := by
  simp [hardyFourierTrace]

private theorem hardy_fourier_exp :
    fourier (T := 2 * Real.pi) n (θ : AddCircle (2 * Real.pi)) =
      Complex.exp ((n : ℂ) * θ * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

private theorem hardy_norm_exp :
    ‖Complex.exp ((n : ℂ) * θ * Complex.I)‖ = 1 := by
  simp [show (n : ℂ) * θ * Complex.I = (((n : ℝ) * θ : ℝ) : ℂ) * Complex.I by     norm_num, Complex.norm_exp_ofReal_mul_I]

private theorem hardy_norm_primSeq_le (ψ : ℤ → ℂ) (n : ℤ) :
    ‖primSeq ψ n‖ ≤ ‖ψ n‖ := by
  by_cases hn : n = 0
  · simp_all [primSeq]
  · have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
    rw [primSeq, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hn')).2
    nlinarith [norm_nonneg (ψ n)]

theorem continuous_hardyFourierTrace {c : ℤ → ℂ}
    (hc : Summable fun n => ‖c n‖) : Continuous (hardyFourierTrace c) := by
  unfold hardyFourierTrace
  simp_rw [hardy_fourier_exp]
  refine continuous_tsum (fun n => by fun_prop) hc fun n θ => ?_
  simp [hardy_norm_exp]

/-- Reconstruction agrees with the actual continuous periodic input. -/
theorem hardyFourierTrace_fourierCoeff (H : C(AddCircle (2 * Real.pi), ℂ))
    (hH : Summable fun n => ‖fourierCoeff H n‖) (θ : ℝ) :
    hardyFourierTrace (fourierCoeff H) θ = H θ := by
  simpa only [hardyFourierTrace, smul_eq_mul] using
    (has_pointwise_sum_fourier_series_of_summable  hH.of_norm
      θ).tsum_eq

/-- The normalized Fourier primitive equals the genuine Volterra integral
of the multiplier and input functions, at every real parameter value. -/
theorem hardyFourierTrace_antiPrim_eq_integral
    (A H : C(AddCircle (2 * Real.pi), ℂ))
    (hA : Summable fun n => ‖fourierCoeff A n‖)
    (hH : Summable fun n => ‖fourierCoeff H n‖)
    (hAn : IsStrictNegativeFourierSupport (fourierCoeff A))
    (hHn : IsNonpositiveFourierSupport (fourierCoeff H)) (θ : ℝ) :
    hardyFourierTrace (antiPrim (fourierCoeff A) (fourierCoeff H)) θ =
      ∫ s in 0..θ,
        A s * H s := by
  let ψ := seqConv (fourierCoeff A) (fourierCoeff H)
  let p := primSeq ψ
  have hAw : IsWL1 0 (fourierCoeff A) := by
    simp_all [IsWL1]
  have hψ : Summable fun n => ‖ψ n‖ := by
    simpa only [IsWL1, Real.rpow_zero, one_mul] using (wl1Norm_seqConv_le (by norm_num) hAw (by
    simp_all [IsWL1])).2.1
  have hψ0 : ψ 0 = 0 := seqConv_zero_of_strictNegative_nonpositive hAn hHn
  have hpN  :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg (p n))
      (hardy_norm_primSeq_le ψ) hψ
  have hpθN : Summable fun n => ‖p n * Complex.exp (n * θ * Complex.I)‖ := by
    simp_all [hardy_norm_exp]
  have hpθ  := hpθN.of_norm
  have heq (n : ℤ) :
      antiPrim (fourierCoeff A) (fourierCoeff H) n *
          Complex.exp (n * θ * Complex.I) =
        p n * Complex.exp (n * θ * Complex.I) -
          if n = 0 then ∑' m, p m else 0 := by
    by_cases hn : n = 0
    · simp_all [antiPrim, p, ψ, primSeq]
    · simp only [antiPrim, if_neg hn, sub_zero]
      rfl
  have htrace :
      hardyFourierTrace (antiPrim (fourierCoeff A) (fourierCoeff H)) θ =
        (∑' n, p n * Complex.exp (n * θ * Complex.I)) - ∑' n, p n := by
    simp only [hardyFourierTrace, hardy_fourier_exp, heq]
    rw [Summable.tsum_sub hpθ (summable_of_ne_finset_zero (s := {0}) fun n hn => by
      simp_all), tsum_ite_eq]
  let F  := A * H
  have hcoef : fourierCoeff F = ψ := fourierCoeff_mul_eq_seqConv A hA.of_norm (by
    have hHi' : IntegrableOn H Set.univ AddCircle.haarAddCircle :=
      H.continuous.continuousOn.integrableOn_compact isCompact_univ
    simp_all)
  have hseries (s : ℝ) :
      HasSum (fun n => ψ n * Complex.exp (n * s * Complex.I))
        (A s * H s) := by
    have ht := has_pointwise_sum_fourier_series_of_summable 
      (by rw [hcoef]; exact hψ.of_norm) s
    rw [hcoef] at ht
    change HasSum (fun n => ψ n • fourier  n
      s)
      (A s * H s) at ht
    simpa only [smul_eq_mul, hardy_fourier_exp] using ht
  have hi : HasSum (fun n => ∫ s in 0..θ,
      ψ n * Complex.exp (n * s * Complex.I))
      (∫ s in 0..θ,
        A s * H s) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => ‖ψ n‖)
      (fun n => (by fun_prop : Continuous fun s : ℝ =>
        ψ n * Complex.exp (n * s * Complex.I)).aestronglyMeasurable)
      (fun n => Eventually.of_forall fun s _ => ?_)
      (Eventually.of_forall fun _ _ => hψ) intervalIntegrable_const
      (Eventually.of_forall fun s _ => hseries s)
    simp [hardy_norm_exp]
  have hint (n : ℤ) :
      (∫ s in 0..θ, ψ n * Complex.exp (n * s * Complex.I)) =
        p n * Complex.exp (n * θ * Complex.I) - p n := by
    by_cases hn : n = 0
    · simp_all
    · rw [intervalIntegral.integral_const_mul]
      simp_rw [show ∀ s : ℝ, n * s * Complex.I = (n * Complex.I) * s
        from fun s => by ring]
      rw [integral_exp_mul_complex (mul_ne_zero (Int.cast_ne_zero.mpr hn) Complex.I_ne_zero)]
      simp 
      dsimp only [p, primSeq]
      field_simp 
  simp_rw [hint] at hi
  rw [htrace]
  simpa only [Summable.tsum_sub hpθ hpN.of_norm] using hi.tsum_eq

end PolyaNeumann

end
