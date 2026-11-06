module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftJets
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftIntegrability
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # Compact smooth stationary tests and their radial lift identities -/

 public section

open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The transport and diffusion tests preserve compact support away from the origin. -/
theorem bellman_radial_stationary_test_properties (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiff ℝ PDE.smoothOrder zeta) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet) :
    (Continuous (fun q => q.2 * bellmanDx zeta q) ∧
      HasCompactSupport (fun q => q.2 * bellmanDx zeta q) ∧
      tsupport (fun q => q.2 * bellmanDx zeta q) ⊆ bellmanPuncturedSet) ∧
    (Continuous (bellmanDvv zeta) ∧ HasCompactSupport (bellmanDvv zeta) ∧
      tsupport (bellmanDvv zeta) ⊆ bellmanPuncturedSet) := by



  have hts : tsupport (fun q => q.2 * bellmanDx zeta q) ⊆ tsupport zeta :=
    tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (1, 0))
  have hrs : tsupport (bellmanDvv zeta) ⊆ tsupport zeta :=
    (tsupport_fderiv_apply_subset ℝ (0, 1)).trans (tsupport_fderiv_apply_subset ℝ (0, 1))
  exact ⟨⟨continuous_snd.mul (bellman_contDiff_direction hz (1, 0)).continuous,
    hc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hs⟩,
    ⟨(bellman_contDiff_direction (bellman_contDiff_direction hz (0, 1)) (0, 1)).continuous, hc.of_isClosed_subset (isClosed_tsupport _) hrs, hrs.trans hs⟩⟩

/-- Integrating the two dilated stationary tests gives exactly the operator of the lifted test. -/
theorem bellman_lift_operator_integral (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiff ℝ PDE.smoothOrder zeta) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet) (q : ℝ × ℝ)
    (hq : q ∈ bellmanPuncturedSet) (b : ℝ) :
    bellmanOperator b (lift alpha zeta) q =
      ∫ r : BellmanPositiveTime,
        (r.val ^ (1 - alpha) *
          ((bellmanPlaneDilation r.val q).2 * bellmanDx zeta
            (bellmanPlaneDilation r.val q))) +
        (r.val ^ (1 - alpha) * (b * bellmanDvv zeta (bellmanPlaneDilation r.val q)))
        ∂bellmanPositiveTimeVolume := by
  obtain ⟨⟨ht, htc, hts⟩, ⟨hv, hvc, hvs⟩⟩ :=
    bellman_radial_stationary_test_properties zeta hz hc hs
  have hiT := bellman_lift_integrand_integrable (alpha - 2)
    (fun q => q.2 * bellmanDx zeta q) ht htc hts q hq
  have hiV := (bellman_lift_integrand_integrable (alpha - 2)
    (bellmanDvv zeta) hv hvc hvs q hq).const_mul b
  have he : -1 - (alpha - 2) = 1 - alpha := by ring
  rw [he] at hiT hiV

  rw [integral_add hiT (hiV.congr (ae_of_all _ (fun r => by ring))), bellmanOperator,
    bellman_lift_dx alpha zeta (hz.of_le (by norm_num)).contDiffOn hc hs q hq,
    bellman_lift_dvv alpha zeta (hz.of_le (by norm_num)).contDiffOn hc hs q hq]
  unfold lift
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1
  · apply integral_congr_ae
    apply ae_of_all
    intro r
    dsimp only [bellmanPlaneDilation]
    have hp : r.val ^ (-1 - (alpha - 3)) = r.val ^ (1 - alpha) * r.val := by
      calc
        r.val ^ (-1 - (alpha - 3)) = r.val ^ ((1 - alpha) + 1) := by congr 1; ring
        _ = r.val ^ (1 - alpha) * r.val ^ (1 : ℝ) := Real.rpow_add r.property _ _
        _ = r.val ^ (1 - alpha) * r.val := by rw [Real.rpow_one]
    rw [hp]
    ring
  · apply integral_congr_ae
    exact ae_of_all _ (fun r => by rw [he]; ring)

end HypoellipticAleksandrov.KineticAleksandrov
