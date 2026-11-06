module
public import ThirdWindow

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

theorem third_upper_large_values {σ a p α δ : ℝ}
    (hw : ThirdWindow σ a p α) (hδ : 0 < δ) (_hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ H → 2 ≤ N → H^α ≤ N → N ≤ H^(3*a/2+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+H) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*H^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*H^(p+18*δ) :=
  upper_large_values_of_fields hw.a_high hw.sigma_low hw.sigma_high
    hw.p_identity hw.mean_identity hδ _hδ'

end Montgomery.RationalMoment
