module
public import AdjacentWindow
public import TwoTermLargeValues
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1200000
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement
open Finset
theorem adjacent_upper_large_values {σ a p α δ : ℝ}
    (hw : AdjacentWindow σ a p α) (hδ : 0 < δ) (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ H → 2 ≤ N → H^α ≤ N → N ≤ H^(3*a/2+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+H) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*H^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*H^(p+18*δ) := by pm_2768



end Montgomery.RationalMoment
