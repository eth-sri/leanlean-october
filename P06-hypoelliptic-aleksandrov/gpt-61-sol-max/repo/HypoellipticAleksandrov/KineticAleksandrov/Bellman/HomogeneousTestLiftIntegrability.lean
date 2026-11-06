module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftWindow
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! # Absolute integrability of the compact radial test integrands -/

 public section

open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The radial integrand has compact support for every fixed punctured spatial point. -/
theorem bellman_lift_integrand_compactSupport (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
    HasCompactSupport (fun r : BellmanPositiveTime => r.val ^ (-1 - alpha) *
      zeta (bellmanPlaneDilation r.val q)) := by
  obtain ⟨U, _, hqU, _, a, b, ha, _, hwindow⟩ :=
    bellman_compact_test_local_radius_window zeta hc hs q hq
  have hK := bellmanRadiusWindow_isCompact a b ha
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal
  · intro r hr

    exact hwindow q hqU r (subset_tsupport zeta (by
        intro he
        exact hr (by simp only [he, mul_zero])))
  · exact hK.isClosed

/-- Compact radial support and continuity prove absolute integrability of the lift integrand. -/
theorem bellman_lift_integrand_integrable (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hz : Continuous zeta) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
    Integrable (fun r : BellmanPositiveTime => r.val ^ (-1 - alpha) *
      zeta (bellmanPlaneDilation r.val q)) bellmanPositiveTimeVolume := (Continuous.integrable_of_hasCompactSupport
  (Continuous.mul (Continuous.rpow_const continuous_subtype_val fun r => Or.inl (LT.lt.ne' r.property))
    (Continuous.comp hz
      (id
        (Continuous.prodMk
          (Continuous.mul_const (Continuous.comp' (Continuous.fun_pow continuous_id' 3) continuous_subtype_val) q.1)
          (Continuous.mul_const continuous_subtype_val q.2)))))
  (bellman_lift_integrand_compactSupport alpha zeta hc hs q hq))

end HypoellipticAleksandrov.KineticAleksandrov
