module
public import GuthMaynard.Improvement.ShortTypeICount
public import HalfLossTypeIICount
public import GuthMaynard.Improvement.ShortDetectorCounting
public import MathCollab.Density.DensityDyadicSummation
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Filter Set MathCollab.Density
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Actual Type-II zero representatives from the ordinary fourth moment. -/
theorem half_loss_typeII_zero_slab_count
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ : ℝ) (R : Finset ℂ),
      9/13 ≤ σ → R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3:ℝ) ≤
        ‖detectorIntegral ρ (2*H^((100:ℝ)⁻¹)) (H^(1/2:ℝ))‖) →
      (R.card:ℝ) ≤ C*H^(2-2*σ+1/50+ε) := by pm_3945 half_loss_short_typeII_count


end GuthMaynard.Improvement
