module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftJets
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftIntegrability
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
import Mathlib.Tactic

/-! # Compact smooth stationary tests and their radial lift identities -/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/- The transport and diffusion tests preserve compact support away from the origin. -/
theorem bellman_radial_stationary_test_properties (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet) :
    (Continuous (fun q => q.2 * bellmanDx zeta q) ∧
      HasCompactSupport (fun q => q.2 * bellmanDx zeta q) ∧
      tsupport (fun q => q.2 * bellmanDx zeta q) ⊆ bellmanPuncturedSet) ∧
    (Continuous (bellmanDvv zeta) ∧ HasCompactSupport (bellmanDvv zeta) ∧
      tsupport (bellmanDvv zeta) ⊆ bellmanPuncturedSet) := by
  have hx := bellman_contDiff_direction hz (1, 0)
  have hv := bellman_contDiff_direction hz (0, 1)
  have hvv := bellman_contDiff_direction hv (0, 1)
  have hts : tsupport (fun q => q.2 * bellmanDx zeta q) ⊆ tsupport zeta :=
    tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (1, 0))
  have hrs : tsupport (bellmanDvv zeta) ⊆ tsupport zeta :=
    (tsupport_fderiv_apply_subset ℝ (0, 1)).trans (tsupport_fderiv_apply_subset ℝ (0, 1))
  exact ⟨⟨continuous_snd.mul hx.continuous,
    hc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hs⟩,
    ⟨hvv.continuous, hc.of_isClosed_subset (isClosed_tsupport _) hrs, hrs.trans hs⟩⟩

/- Integrating the two dilated stationary tests gives exactly the operator of the lifted test. -/
end HypoellipticAleksandrov.KineticAleksandrov
