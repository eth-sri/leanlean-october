module
public import DensityEnergyGM.SharpPolynomialCount
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Filter Finset GuthMaynard.Improvement GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- Pure numeric conditions for the sharp actual-polynomial count. -/
structure SharpCountWindow (σ a : ℝ) : Prop where
  sigma_low : 4/5 ≤ σ
  sigma_high : σ < 1
  a_low : 1/2 ≤ a
  a_high : a < 2/3
  budgets : ∀ x : ℝ, a ≤ x → ∀ j : Fin 3, ∀ i : Fin 5,
    0 ≤ gmTraceEnergyMargin σ a x j i

section
variable {σ : ℝ}
include σ
theorem sharpCountWindow_row6 (hlo : 1959705/2298302 ≤ σ) (hhi : σ ≤ 6482825/7570038) :
    SharpCountWindow σ (597962/(2187648*σ-772245)) := by
  pm_1101
  pm_4911
  have ha : 1/2 ≤ 597962/(2187648*σ-772245) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  pm_3978
  · intro x hxa j i
    have hh := gmTraceEnergyMargin_row6 hlo hhi (le_refl (597962/(2187648*σ-772245)))
      (show 597962/(2187648*σ-772245) ≤ 3*(597962/(2187648*σ-772245))/2 by linarith) j i
    exact hh.trans (gmTraceEnergyMargin_mono_length hσ hxa j i)

theorem sharpCountWindow_row7 (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354) :
    SharpCountWindow σ (16504356/(62198298*σ-22870785)) := by
  pm_494
  pm_4911
  have ha : 1/2 ≤ 16504356/(62198298*σ-22870785) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  pm_3978
  · intro x hxa j i
    have hh := gmTraceEnergyMargin_row7 hlo hhi (le_refl (16504356/(62198298*σ-22870785)))
      (show 16504356/(62198298*σ-22870785) ≤ 3*(16504356/(62198298*σ-22870785))/2 by linarith) j i
    exact hh.trans (gmTraceEnergyMargin_mono_length hσ hxa j i)

theorem sharpCountWindow_row8 (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8) :
    SharpCountWindow σ (2172/(8226*σ-3045)) := by
  pm_1102
  pm_4911
  have ha : 1/2 ≤ 2172/(8226*σ-3045) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  pm_3978
  · intro x hxa j i
    have hh := gmTraceEnergyMargin_row8 hlo hhi (le_refl (2172/(8226*σ-3045)))
      (show 2172/(8226*σ-3045) ≤ 3*(2172/(8226*σ-3045))/2 by linarith) j i
    exact hh.trans (gmTraceEnergyMargin_mono_length hσ hxa j i)
end

/-- The full perturbed short-polynomial window, with all analytic inputs
supplied and only the numeric window remaining as a parameter. -/
theorem sharp_polynomial_count_window_loss {σ a δ : ℝ}
    (hw : SharpCountWindow σ a) (hδ : 0 < δ) (hδa : δ ≤ (1-3*a/2)/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 2 ≤ T → T^a ≤ N → N ≤ T^(3*a/2+δ) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*a*(1-σ)+72*δ) :=
  sharp_polynomial_count_loss hw.sigma_low hw.sigma_high hw.a_low hw.a_high hδ hδa hw.budgets

end Montgomery.RationalMoment
