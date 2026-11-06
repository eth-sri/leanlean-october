module
import Mathlib
public import GuthMaynard.Improvement.StrengthenedAffine
public import GuthMaynard.Improvement.SparseAffineInput

@[expose] public section

open MeasureTheory Set
open scoped SchwartzMap FourierTransform ContDiff
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Smoothness and compact support for arbitrary integrable compact inputs;
no regularity of a measurable mask boundary is required. -/
theorem compact_smoothed_general_schwartz {g : ℝ → ℝ} {a b δ : ℝ}
    (hg : Integrable g) (hδ : 0 < δ)
    (hs : ∀ x, x ∉ Icc a b → g x = 0) :
    ∃ f : 𝓢(ℝ, ℝ), (f : ℝ → ℝ) = smooth (scaledKernel compactKernel δ) g := by
  have hc : HasCompactSupport (scaledKernel compactKernel δ) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2*δ) (2*δ)))
    intro x hx
    apply scaled_compactKernel_zero hδ
    grind
  have hd : ContDiff ℝ ∞ (scaledKernel compactKernel δ) :=
    contDiff_const.mul (compactKernel_smooth.comp (contDiff_id.div_const δ))
  have hsd : ContDiff ℝ ∞ (smooth (scaledKernel compactKernel δ) g) := by
    rw [smooth_eq_convolution]
    exact hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hg.locallyIntegrable hd
  have hsc : HasCompactSupport (smooth (scaledKernel compactKernel δ) g) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (a-2*δ) (b+2*δ)))
    intro x hx
    exact smooth_support_interval (fun t ht => scaled_compactKernel_zero hδ ht) hs hx
  exact ⟨hsc.toSchwartzMap hsd,rfl⟩

/-- Fixed Fourier constants precede every height, width, and measurable input.
The normalization uses the actual output supremum, never inverse mask mass. -/
theorem compact_smoothed_full_input (a b : ℝ) (hab : a ≤ b) :
    ∃ D : ℝ → ℕ → ℝ, (∀ β n, 0 ≤ D β n) ∧
      ∀ (T δ : ℝ) (g : ℝ → ℝ), 2 ≤ T → 0 < δ → δ ≤ 1 → δ⁻¹ ≤ T →
      Integrable g → (∀ x, 0 ≤ g x) → (∀ x, x ∉ Icc a b → g x = 0) →
      FourierSupInput D T (smooth (scaledKernel compactKernel δ) g) := by
  choose C hC h using compact_smoothing_normalized_fourier hab
  refine ⟨fun _ n => C n,fun _ n => (hC n).le,?_⟩
  intro T δ g hT hδ hδ1 hδT hg hg0 hs
  obtain ⟨f,hf⟩ := compact_smoothed_general_schwartz hg hδ hs
  have hsup : ∀ x, smooth (scaledKernel compactKernel δ) g x ≤ sourceSup f := by
    intro x
    rw [← hf, sourceSup_eq_seminorm]
    exact (le_abs_self _).trans (by
      simpa only [gmAffineComplexify_apply, Complex.norm_real, Real.norm_eq_abs] using
        SchwartzMap.norm_le_seminorm (𝕜 := ℝ) (gmAffineComplexify f) x)
  have hU : 0 ≤ sourceSup f := (smooth_nonneg
    (scaledKernel_nonneg compactKernel_nonneg hδ) hg0 0).trans (hsup 0)
  intro β hβ n ξ hξ
  have hh := h n δ hδ hδ1 g hg hg0 hs (sourceSup f) hsup ξ
  have ht : 1 ≤ T^β := Real.one_le_rpow (by linarith) hβ.le
  have hpow : δ⁻¹^n ≤ T^n := pow_le_pow_left₀ (by positivity) hδT n
  have hξp : 0 < |ξ|^n := pow_pos (abs_pos.mpr hξ) n
  have hnum : |ξ|^n * ‖𝓕 (fun x => (smooth (scaledKernel compactKernel δ) g x : ℂ)) ξ‖ ≤
      C n*T^β*T^n*sourceSup f := hh.trans (by
    calc
      _ ≤ T^n*C n*sourceSup f := by gcongr; exact (hC n).le
      _ ≤ C n*T^β*T^n*sourceSup f := by nlinarith [mul_nonneg (mul_nonneg (hC n).le (pow_nonneg (by linarith : 0 ≤ T) n)) hU])
  change _ ≤ C n*T^β*(T/|ξ|)^n*sourceSup (smooth (scaledKernel compactKernel δ) g)
  rw [← hf] at hnum ⊢
  calc
    _ ≤ (C n*T^β*T^n*sourceSup f) / |ξ|^n :=
      (le_div_iff₀ hξp).mpr (by simpa only [mul_comm] using hnum)
    _ = _ := by rw [div_pow]; ring


