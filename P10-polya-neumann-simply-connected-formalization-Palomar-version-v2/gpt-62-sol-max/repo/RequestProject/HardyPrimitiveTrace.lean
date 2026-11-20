module

public import RequestProject.CircleFourier
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

/-- Pointwise Fourier reconstruction in the averaged coefficient convention. -/
def hardyFourierTrace (c : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑' n, c n * fourier (T := 2 * Real.pi) n (θ : AddCircle (2 * Real.pi))

theorem hardyFourierTrace_periodic (c : ℤ → ℂ) :
    Function.Periodic (hardyFourierTrace c) (2 * Real.pi) := by simp_all [hardyFourierTrace]

private theorem hardy_norm_exp (n : ℤ) (θ : ℝ) :
    ‖Complex.exp ((n : ℂ) * θ * Complex.I)‖ = 1 := by
  rw [show (n : ℂ) * θ * Complex.I = (((n : ℝ) * θ : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

private theorem hardy_norm_primSeq_le (ψ : ℤ → ℂ) (n : ℤ) :
    ‖primSeq ψ n‖ ≤ ‖ψ n‖ := by
  by_cases hn : n = 0
  simp_all [primSeq]
  · have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
    rw [primSeq, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hn')).2
    nlinarith [norm_nonneg (ψ n)]

theorem continuous_hardyFourierTrace {c : ℤ → ℂ}
    (hc : Summable fun n => ‖c n‖) : Continuous (hardyFourierTrace c) := by
  unfold hardyFourierTrace
  simp_rw [fourier_coe_two_pi]
  refine continuous_tsum (fun n => by fun_prop) hc fun n θ => ?_
  simp only [norm_mul, hardy_norm_exp, mul_one]
  exact le_rfl

/-- Reconstruction agrees with the actual continuous periodic input. -/
theorem hardyFourierTrace_fourierCoeff (H : C(AddCircle (2 * Real.pi), ℂ))
    (hH : Summable fun n => ‖fourierCoeff H n‖) (θ : ℝ) :
    hardyFourierTrace (fourierCoeff H) θ = H (θ : AddCircle (2 * Real.pi)) := HasSum.tsum_eq (has_pointwise_sum_fourier_series_of_summable (Summable.of_norm hH) ↑θ)

/-- The normalized Fourier primitive equals the genuine Volterra integral
of the multiplier and input functions, at every real parameter value. -/
theorem hardyFourierTrace_antiPrim_eq_integral
    (A H : C(AddCircle (2 * Real.pi), ℂ))
    (hA : Summable fun n => ‖fourierCoeff A n‖)
    (hH : Summable fun n => ‖fourierCoeff H n‖)
    (hAn : IsStrictNegativeFourierSupport (fourierCoeff A))
    (hHn : IsNonpositiveFourierSupport (fourierCoeff H)) (θ : ℝ) :
    hardyFourierTrace (antiPrim (fourierCoeff A) (fourierCoeff H)) θ =
      ∫ s in (0 : ℝ)..θ,
        A (s : AddCircle (2 * Real.pi)) * H (s : AddCircle (2 * Real.pi)) := by
  let ψ := seqConv (fourierCoeff A) (fourierCoeff H)
  let p := primSeq ψ
  have hAw : IsWL1 0 (fourierCoeff A) := by
    grind [IsWL1, Real.rpow_zero, one_mul]
  have hHw : IsWL1 0 (fourierCoeff H) := by
    grind [IsWL1, Real.rpow_zero, one_mul]
  have hψw := (wl1Norm_seqConv_le (by norm_num : (0 : ℝ) ≤ 0) hAw hHw).2.1
  have hψ : Summable fun n => ‖ψ n‖ := by
    grind [IsWL1, Real.rpow_zero, one_mul]
  have hψ0 : ψ 0 = 0 := seqConv_zero_of_strictNegative_nonpositive hAn hHn
  have hpN : Summable fun n => ‖p n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg (p n))
      (fun n => hardy_norm_primSeq_le ψ n) hψ
  have hp : Summable p := hpN.of_norm
  have hpθN : Summable fun n => ‖p n * Complex.exp ((n : ℂ) * θ * Complex.I)‖ := by
    grind [norm_mul, hardy_norm_exp, mul_one]
  have hpθ : Summable fun n => p n * Complex.exp ((n : ℂ) * θ * Complex.I) := hpθN.of_norm
  have hδ : Summable fun n : ℤ => if n = 0 then ∑' m, p m else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by grind
  have heq (n : ℤ) :
      antiPrim (fourierCoeff A) (fourierCoeff H) n *
          Complex.exp ((n : ℂ) * θ * Complex.I) =
        p n * Complex.exp ((n : ℂ) * θ * Complex.I) -
          if n = 0 then ∑' m, p m else 0 := by
    by_cases hn : n = 0
    simp_all [antiPrim, p, ψ, primSeq]
    grind [antiPrim, sub_zero]
  have htrace :
      hardyFourierTrace (antiPrim (fourierCoeff A) (fourierCoeff H)) θ =
        (∑' n, p n * Complex.exp ((n : ℂ) * θ * Complex.I)) - ∑' n, p n := by
    simp only [hardyFourierTrace, fourier_coe_two_pi, heq]
    rw [Summable.tsum_sub hpθ hδ, tsum_ite_eq]
  let F : C(AddCircle (2 * Real.pi), ℂ) := A * H
  have hHi : Integrable H AddCircle.haarAddCircle := by
    have hHi' : IntegrableOn H Set.univ AddCircle.haarAddCircle :=
      H.continuous.continuousOn.integrableOn_compact isCompact_univ
    simp_all
  have hcoef : fourierCoeff F = ψ := by
    change fourierCoeff (fun x => A x * H x) = _
    exact fourierCoeff_mul_eq_seqConv A hA.of_norm hHi
  have hseries (s : ℝ) :
      HasSum (fun n => ψ n * Complex.exp ((n : ℂ) * s * Complex.I))
        (A (s : AddCircle (2 * Real.pi)) * H (s : AddCircle (2 * Real.pi))) := by
    have ht := has_pointwise_sum_fourier_series_of_summable (f := F)
      (by simpa [hcoef] using hψ.of_norm) (s : AddCircle (2 * Real.pi))
    rw [hcoef] at ht
    change HasSum (fun n => ψ n • fourier (T := 2 * Real.pi) n
      (s : AddCircle (2 * Real.pi)))
      (A (s : AddCircle (2 * Real.pi)) * H (s : AddCircle (2 * Real.pi))) at ht
    grind [smul_eq_mul, fourier_coe_two_pi]
  have hi : HasSum (fun n => ∫ s in (0 : ℝ)..θ,
      ψ n * Complex.exp ((n : ℂ) * s * Complex.I))
      (∫ s in (0 : ℝ)..θ,
        A (s : AddCircle (2 * Real.pi)) * H (s : AddCircle (2 * Real.pi))) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => ‖ψ n‖)
      (fun n => (by fun_prop : Continuous fun s : ℝ =>
        ψ n * Complex.exp ((n : ℂ) * s * Complex.I)).aestronglyMeasurable)
      (fun n => Eventually.of_forall fun s _ => ?_)
      (Eventually.of_forall fun _ _ => hψ) intervalIntegrable_const
      (Eventually.of_forall fun s _ => hseries s)
    simp only [norm_mul, hardy_norm_exp, mul_one]
    exact le_rfl
  have hint (n : ℤ) :
      (∫ s in (0 : ℝ)..θ, ψ n * Complex.exp ((n : ℂ) * s * Complex.I)) =
        p n * Complex.exp ((n : ℂ) * θ * Complex.I) - p n := by
    by_cases hn : n = 0
    simp_all
    · have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
      rw [intervalIntegral.integral_const_mul]
      simp_rw [show ∀ s : ℝ, (n : ℂ) * s * Complex.I = ((n : ℂ) * Complex.I) * s
        from fun s => by ring]
      rw [integral_exp_mul_complex (mul_ne_zero hnC Complex.I_ne_zero)]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      dsimp only [p, primSeq]
      ring
  simp_rw [hint] at hi
  rw [htrace]
  simpa only [Summable.tsum_sub hpθ hp] using hi.tsum_eq

end PolyaNeumann

end
