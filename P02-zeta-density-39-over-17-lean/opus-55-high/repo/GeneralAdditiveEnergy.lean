module
public import GeneralLargeGcdEnergy
public import DiscreteAdditiveEnergy
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1600000
open Finset
namespace Montgomery.RationalMoment

/-- Actual four-term additive energy, with no cardinality lower bound. -/
theorem discrete_energy_adjacent_unrestricted {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 1 < T → 0 < N → N ≤ T →
      ∀ (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
      (∀ n ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖a n‖ ≤ 1) →
      0 < V → (∀ t ∈ W, V ≤ ‖GuthMaynard.Improvement.boundedPolynomial N a t‖) →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (discreteAdditiveEnergy W:ℝ) ≤ C*T^η*(N^4*(W.card:ℝ)/V^4+
        (N*(W.card:ℝ)^3+T*(W.card:ℝ)^((5:ℝ)/2)+
          N*T^((1:ℝ)/4)*(W.card:ℝ)^((31:ℝ)/12))/V^2) := by
  pm_418 large_gcd_adjacent_general
  intro T t₀ N hT hN hNT a W V ha hV hlargeW hW hsep
  have ht : 0 < T := by linarith
  by_cases he : W = ∅
  · subst W
    simp [discreteAdditiveEnergy]
  have hr : (0:ℝ) < W.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr he)
  pm_2724
  pm_284
  pm_61 hB B
  pm_2723
  pm_125
  have hlarge' := hlarge T t₀ N hT hN hNT Q (by
    pm_4584 p hp hd
    pm_6
    exact ⟨h1,h2,hl1,hu1,hl2,hu2,hd⟩) W hW hsep
  pm_60
  pm_85


end Montgomery.RationalMoment
