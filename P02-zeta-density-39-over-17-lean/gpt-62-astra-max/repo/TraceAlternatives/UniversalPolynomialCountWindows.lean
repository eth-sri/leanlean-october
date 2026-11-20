module
public import TraceAlternatives.UniversalPolynomialCount
public import TraceAlternatives.UniversalCountTargetWindows

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Filter Finset GuthMaynard.Improvement GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- Pure numeric conditions for the sharp actual-polynomial count. -/
structure UniversalCountWindow (σ a : ℝ) : Prop where
  sigma_low : 4/5 ≤ σ
  sigma_high : σ < 1
  a_low : 1/2 ≤ a
  a_high : a < 2/3
  budgets : ∀ x : ℝ, a ≤ x → ∀ j : Fin 3, ∀ i : Fin 5,
    0 ≤ universalTraceEnergyMargin σ a x j i
  low_budget : ∀ x : ℝ, a ≤ x → 1/100 ≤ universalLowMargin σ a x



/-- The full perturbed short-polynomial window, with all analytic inputs
supplied and only the numeric window remaining as a parameter. -/
theorem universal_polynomial_count_window_loss {σ a δ : ℝ}
    (hw : UniversalCountWindow σ a) (hδ : 0 < δ) (hδsmall : δ ≤ 1/1800) (hδa : δ ≤ (1-3*a/2)/2) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ T t₀ N : ℝ, T₀ ≤ T → T^a ≤ N → N ≤ T^(3*a/2+δ) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*a*(1-σ)+144*δ) :=
  universal_polynomial_count_loss hw.sigma_low hw.sigma_high hw.a_low hw.a_high hδ hδsmall hδa hw.budgets hw.low_budget


end Montgomery.RationalMoment
