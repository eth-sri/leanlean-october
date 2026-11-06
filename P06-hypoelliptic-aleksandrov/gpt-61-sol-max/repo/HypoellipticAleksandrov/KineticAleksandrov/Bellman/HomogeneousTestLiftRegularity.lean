module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftWindow
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftSmoothIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-! # C² regularity of the actual homogeneous test lift -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The joint lift integrand on the ambient plane and positive real radius. -/
def bellmanLiftIntegrand (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (w : (ℝ × ℝ) × ℝ) : ℝ :=
  w.2 ^ (-1 - alpha) * zeta (bellmanPlaneDilation w.2 w.1)

/-- The test gives joint regularity of the same order wherever the radius is positive. -/
theorem bellmanLiftIntegrand_contDiffOn_order (n : WithTop ℕ∞)
    (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ) (hz : ContDiff ℝ n zeta) :
    ContDiffOn ℝ n (bellmanLiftIntegrand alpha zeta) (univ ×ˢ Ioi 0) := (ContDiffOn.mul (ContDiffOn.rpow_const_of_ne contDiffOn_snd fun w hw => ne_of_gt hw.right)
  (ContDiff.contDiffOn
    (ContDiff.comp hz
      (ContDiff.prodMk (ContDiff.mul (ContDiff.pow contDiff_snd 3) (ContDiff.fst contDiff_fst))
        (ContDiff.mul contDiff_snd (ContDiff.snd contDiff_fst))))))

variable (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)

/-- The compact test gives joint C² regularity wherever the radial variable is positive. -/
theorem bellmanLiftIntegrand_contDiffOn
    (hz : ContDiff ℝ 2 zeta) : type_of% (bellmanLiftIntegrand_contDiffOn_order 2 alpha zeta hz) :=
  bellmanLiftIntegrand_contDiffOn_order 2 alpha zeta hz

/-- Compact support makes the radial integral C² on the entire punctured plane. -/
theorem bellman_lift_contDiffOn
    (hz : ContDiffOn ℝ 2 zeta bellmanPuncturedSet) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet) :
    ContDiffOn ℝ 2 (lift alpha zeta) bellmanPuncturedSet := by


  intro q hq
  obtain ⟨U, hU, hqU, _, a, b, ha, _, hwindow⟩ :=
    bellman_compact_test_local_radius_window zeta hc hs q hq
  let K : Set BellmanPositiveTime := {r | r.val ∈ Icc a b}
  have hK  := bellmanRadiusWindow_isCompact a b ha
  let  := isCompact_iff_compactSpace.mp hK
  let mu : Measure K := Measure.comap Subtype.val bellmanPositiveTimeVolume
  let  := bellman_radius_window_volume_finite K hK
  let radius : K → ℝ := fun r => r.val.val


  have hI : ContDiffOn ℝ 2
      (fun x => ∫ r : K, bellmanLiftIntegrand alpha zeta (x, radius r) ∂mu) U :=
    bellman_joint_contDiff_integral mu hU radius (continuous_subtype_val.comp continuous_subtype_val) (fun r => r.val.property)
      _ ((bellmanLiftIntegrand_contDiffOn alpha zeta (bellman_compact_test_contDiff zeta hz hs)).mono (prod_mono (subset_univ U) Subset.rfl))


  exact (((hI q hqU).contDiffAt (hU.mem_nhds hqU)).congr_of_eventuallyEq (show lift alpha zeta =ᶠ[𝓝 q]
      fun x => ∫ r : K, bellmanLiftIntegrand alpha zeta (x, radius r) ∂mu by
      filter_upwards [hU.mem_nhds hqU] with x hx
      apply bellman_integral_compact_radius_subtype K hK
      intro r hrK
      have hzero : zeta (bellmanPlaneDilation r.val x) = 0 := by
        by_contra hn
        exact hrK (hwindow x hx r (subset_tsupport zeta hn))
      simp only [hzero, mul_zero])).contDiffWithinAt

end HypoellipticAleksandrov.KineticAleksandrov
