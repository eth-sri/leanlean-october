module
public import GuthMaynard.Improvement.ShortTypeIICount
public import GuthMaynard.Improvement.WeakShortMoment
public import HalfLossTypeIICount

@[expose] public section
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

/-- The ordinary fourth moment and a crude mollifier bound suffice, with a fixed
1/25 loss. Constants precede sigma, height and every finite family. -/
theorem weak_short_typeII_count
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C H₀ : ℝ, 0 < C ∧ 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ σ : ℝ,
      ∀ (W : Finset ℝ) (ρ : ℝ → ℂ), 9/13 ≤ σ →
      oneSeparated W → (∀ u ∈ W,u ∈ Icc H (2*H)) →
      (∀ u ∈ W,(ρ u).im=u ∧ σ ≤ (ρ u).re ∧ (ρ u).re ≤ 1) →
      (∀ u ∈ W,(1/3:ℝ) ≤ ‖detectorIntegral (ρ u) (2*H^((1:ℝ)/100)) (H^((1:ℝ)/2))‖) →
      (W.card:ℝ) ≤ C*H^(2-2*σ+1/25+ε) := by pf_73 weak_short_moment 25

end GuthMaynard.Improvement
