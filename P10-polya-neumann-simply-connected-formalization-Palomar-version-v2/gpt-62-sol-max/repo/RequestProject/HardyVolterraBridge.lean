module

public import RequestProject.CircleFourier
public import RequestProject.HardyPrimitiveTrace
public import RequestProject.VolterraIterateBound

/-!
# Actual Fourier primitive iterates are Volterra primitive iterates

Absolutely summable sequences are reconstructed as continuous functions on the
circle.  Their averaged Haar Fourier coefficients are proved to be the original
sequences.  The one-step Hardy primitive identity can therefore be applied to
every actual `antiPrimIter`, using its proved H¹ regularity and nonpositive support.

The resulting identity preserves period `2π`, the nonpositive Fourier sector, and
the zero value of every positive iterate at the boundary origin.  It transfers
the genuine interval-integral factorial bounds and exponential-weight
summability to the reconstructed Fourier iterates.

The assumptions on the multiplier and initial sequence are explicit input
obligations.  This file does not construct a physical conformal parametrization
or identify a physical multiplier with a given circle function.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory
open scoped InnerProductSpace

/-- Uniform Fourier synthesis as an actual continuous circle function. -/
def hardyCircleReconstruction (c : ℤ → ℂ) : C(AddCircle (2 * Real.pi), ℂ) :=
  ∑' n, c n • fourier (T := 2 * Real.pi) n

section

variable {c : ℤ → ℂ} (hc : Summable fun n => ‖c n‖)
include c hc

private theorem summable_hardyCircleReconstruction_terms  :
    Summable (fun n => c n • fourier (T := 2 * Real.pi) n) := by
  apply Summable.of_norm
  simp_all [norm_smul, fourier_norm]

/-- Uniform synthesis has the same pointwise values as the actual Fourier trace. -/
theorem hardyCircleReconstruction_coe  (θ : ℝ) :
    hardyCircleReconstruction c (θ : AddCircle (2 * Real.pi)) =
      hardyFourierTrace c θ := by
  have hs := (ContinuousMap.evalCLM ℂ (θ : AddCircle (2 * Real.pi))).hasSum
    (summable_hardyCircleReconstruction_terms hc).hasSum
  exact id (fun hs => id (Eq.symm (HasSum.tsum_eq hs))) hs

end

private def hardyVolterraCoefficientCLM (n : ℤ) :
    C(AddCircle (2 * Real.pi), ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ (fourierLp (T := 2 * Real.pi) 2 n)).comp
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)

private theorem hardyVolterraCoefficientCLM_apply (n : ℤ)
    (H : C(AddCircle (2 * Real.pi), ℂ)) :
    hardyVolterraCoefficientCLM n H = fourierCoeff H n := by
  change ⟪fourierLp (T := 2 * Real.pi) 2 n,
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ H⟫_ℂ = fourierCoeff H n
  rw [← fourierCoeff_toLp H n, ← fourierBasis_repr,
    HilbertBasis.repr_apply_apply, coe_fourierBasis]

/-- The synthesized function has exactly the original averaged Fourier coefficients. -/
theorem hardyCircleReconstruction_fourierCoeff {c : ℤ → ℂ}
    (hc : Summable fun n => ‖c n‖) :
    fourierCoeff (hardyCircleReconstruction c) = c := by
  funext n
  have hterm (k : ℤ) :
      hardyVolterraCoefficientCLM n (c k • fourier (T := 2 * Real.pi) k) =
        if k = n then c n else 0 := by
    rw [hardyVolterraCoefficientCLM_apply]
    change fourierCoeff (fun x => c k * fourier (T := 2 * Real.pi) k x) n = _
    rw [fourierCoeff.const_mul, fourierCoeff_fourier]
    grind
  have hs := (hardyVolterraCoefficientCLM n).hasSum
    (summable_hardyCircleReconstruction_terms hc).hasSum
  change HasSum
    (fun k => hardyVolterraCoefficientCLM n (c k • fourier (T := 2 * Real.pi) k))
    (hardyVolterraCoefficientCLM n (hardyCircleReconstruction c)) at hs
  simp_rw [hterm] at hs
  rw [hardyVolterraCoefficientCLM_apply] at hs
  simpa only [tsum_ite_eq] using hs.tsum_eq.symm

theorem fourierCoeffOn_hardyFourierTrace {c : ℤ → ℂ} (hc : Summable fun n => ‖c n‖) :
    fourierCoeffOn Real.two_pi_pos (hardyFourierTrace c) = c := by
  have h : (fun θ : ℝ => hardyCircleReconstruction c (θ : AddCircle (2 * Real.pi))) =
      hardyFourierTrace c := funext (hardyCircleReconstruction_coe hc)
  rw [← h, ← fourierCoeff_eq_on_circle, hardyCircleReconstruction_fourierCoeff hc]

/-- The one-step integral identity for an arbitrary absolutely summable input sequence. -/
theorem hardyFourierTrace_antiPrim_eq_integral_seq
    (A : C(AddCircle (2 * Real.pi), ℂ))
    (hA : Summable fun n => ‖fourierCoeff A n‖)
    {h : ℤ → ℂ} (hh : Summable fun n => ‖h n‖)
    (hAn : IsStrictNegativeFourierSupport (fourierCoeff A))
    (hhn : IsNonpositiveFourierSupport h) (θ : ℝ) :
    hardyFourierTrace (antiPrim (fourierCoeff A) h) θ =
      ∫ s in (0 : ℝ)..θ,
        A (s : AddCircle (2 * Real.pi)) * hardyFourierTrace h s := by
  let H := hardyCircleReconstruction h
  have hcoef : fourierCoeff H = h := hardyCircleReconstruction_fourierCoeff hh
  have hH : Summable fun n => ‖fourierCoeff H n‖ := by
    simp_all
  have hHn : IsNonpositiveFourierSupport (fourierCoeff H) := by
    simp_all
  have hval (s : ℝ) : H (s : AddCircle (2 * Real.pi)) = hardyFourierTrace h s :=
    hardyCircleReconstruction_coe hh s
  simpa [hcoef, hval] using hardyFourierTrace_antiPrim_eq_integral A H hA hH hAn hHn θ

/-- One weighted ℓ¹ derivative in particular gives absolute summability. -/
theorem summable_norm_of_isWL1_one {a : ℤ → ℂ} (ha : IsWL1 1 a) :
    Summable fun n => ‖a n‖ := by
  have hw : Summable fun n => sobWeight n * ‖a n‖ := by
    simp_all [IsWL1]
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg (a n)) (fun n => ?_) hw
  simpa using mul_le_mul_of_nonneg_right (one_le_sobWeight n) (norm_nonneg (a n))

/-- Every actual primitive iterate of an H¹ input has absolutely summable coefficients. -/
theorem summable_norm_antiPrimIter_of_H1 {a h : ℤ → ℂ}
    (ha : IsWL1 1 a) (hh : IsSobolevSeq 1 h) (j : ℕ) :
    Summable fun n => ‖antiPrimIter a j h n‖ := by
  have hj := (antiPrimIter_bound (by norm_num : (0 : ℝ) ≤ 1) ha hh j).1
  exact (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hj)).1

section

variable (A : C(AddCircle (2 * Real.pi), ℂ)) (hA : IsWL1 1 (fourierCoeff A)) {h : ℤ → ℂ} (hh : IsSobolevSeq 1 h) (hAn : IsStrictNegativeFourierSupport (fourierCoeff A)) (hhn : IsNonpositiveFourierSupport h)
include A hA h hh hAn hhn

/-- Iteration of the actual normalized Fourier primitive agrees with iteration of
the actual interval primitive, at every real parameter. -/
theorem hardyFourierTrace_antiPrimIter_eq_volterraPrimitiveIterate
     :
    ∀ j θ, hardyFourierTrace (antiPrimIter (fourierCoeff A) j h) θ =
      volterraPrimitiveIterate (fun s => A (s : AddCircle (2 * Real.pi)))
        (hardyFourierTrace h) j θ := by
  intro j
  induction j with
  | zero =>
      tauto
  | succ j ih =>
      intro θ
      have hj : antiPrimIter (fourierCoeff A) (j + 1) h =
          antiPrim (fourierCoeff A) (antiPrimIter (fourierCoeff A) j h) :=
        Function.iterate_succ_apply' _ _ _
      rw [hj]
      change hardyFourierTrace
          (antiPrim (fourierCoeff A) (antiPrimIter (fourierCoeff A) j h)) θ =
        ∫ s in (0 : ℝ)..θ, A (s : AddCircle (2 * Real.pi)) *
          volterraPrimitiveIterate (fun s => A (s : AddCircle (2 * Real.pi)))
            (hardyFourierTrace h) j s
      rw [hardyFourierTrace_antiPrim_eq_integral_seq A
        (summable_norm_of_isWL1_one hA) (summable_norm_antiPrimIter_of_H1 hA hh j)
        hAn (antiPrimIter_nonpositive hAn hhn j) θ]
      simp_all

/-- The genuine derivative of each reconstructed successor iterate. -/
theorem hasDerivAt_hardyFourierTrace_antiPrimIter_succ
     (j : ℕ) (θ : ℝ) :
    HasDerivAt (hardyFourierTrace (antiPrimIter (fourierCoeff A) (j + 1) h))
      (A (θ : AddCircle (2 * Real.pi)) *
        hardyFourierTrace (antiPrimIter (fourierCoeff A) j h) θ) θ := by
  have hhs : Summable fun n => ‖h n‖ :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simp_all)).1
  have hfun : hardyFourierTrace (antiPrimIter (fourierCoeff A) (j + 1) h) =
      volterraPrimitiveIterate (fun s => A (s : AddCircle (2 * Real.pi)))
        (hardyFourierTrace h) (j + 1) := by
    funext s
    exact hardyFourierTrace_antiPrimIter_eq_volterraPrimitiveIterate A hA hh hAn hhn _ s
  rw [hfun, hardyFourierTrace_antiPrimIter_eq_volterraPrimitiveIterate A hA hh hAn hhn]
  exact hasDerivAt_volterraPrimitiveIterate_succ
    (A.continuous.comp (AddCircle.continuous_mk' _))
    (continuous_hardyFourierTrace hhs) j θ

end

end PolyaNeumann

end
