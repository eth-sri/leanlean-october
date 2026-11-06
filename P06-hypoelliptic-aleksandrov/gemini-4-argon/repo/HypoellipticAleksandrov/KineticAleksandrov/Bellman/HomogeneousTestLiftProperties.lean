module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftScaling
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationDensity
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLift
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpace
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftSmoothIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # The homogeneous-test-lift node with its literal operator chain rule -/

@[expose] public section
noncomputable section
open Set
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory
open Filter Topology

/- The actual radial integral is C² homogeneous with the required operator scaling. -/
theorem bellman_test_lift (alpha : ℝ) (_ha : 0 < alpha) (_ha1 : alpha < 1)
    (zeta : (ℝ × ℝ) → ℝ) (hz : ContDiffOn ℝ 2 zeta bellmanPuncturedSet)
    (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet) :
    IsBellmanHomogeneous alpha (lift alpha zeta) ∧
      ∀ r : ℝ, 0 < r → ∀ q ∈ bellmanPuncturedSet, ∀ b : ℝ,
        bellmanOperator b (fun z => zeta (bellmanPlaneDilation r z)) q =
          r ^ 2 * bellmanOperator b zeta (bellmanPlaneDilation r q) := by
  have _h_xinl_0 : ContDiffOn ℝ 2 (lift alpha zeta) bellmanPuncturedSet := by
    have hzglobal : ContDiff ℝ 2 zeta := by
        exact (
      bellman_compact_test_contDiff_order 2 zeta hz hs
      )
    have hf : ContDiffOn ℝ 2 (bellmanLiftIntegrand alpha zeta) (univ ×ˢ Ioi 0) := by
        exact (
      bellmanLiftIntegrand_contDiffOn_order 2 alpha zeta hzglobal


      )
    intro q hq
    obtain ⟨U, hU, hqU, _, a, b, ha, _, hwindow⟩ :=
      bellman_compact_test_local_radius_window zeta hc hs q hq
    let K : Set BellmanPositiveTime := {r | r.val ∈ Icc a b}
    have hK : IsCompact K := bellmanRadiusWindow_isCompact a b ha
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let mu : Measure K := Measure.comap Subtype.val bellmanPositiveTimeVolume
    let : IsFiniteMeasure mu := bellman_radius_window_volume_finite K hK
    let radius : K → ℝ := fun r => r.val.val
    have hr : Continuous radius := continuous_subtype_val.comp continuous_subtype_val
    have hrp : ∀ r : K, 0 < radius r := fun r => r.val.property
    have hI : ContDiffOn ℝ 2
        (fun x => ∫ r : K, bellmanLiftIntegrand alpha zeta (x, radius r) ∂mu) U :=
      bellman_joint_contDiff_integral mu hU radius hr hrp
        (bellmanLiftIntegrand alpha zeta) (hf.mono (prod_mono (subset_univ U) Subset.rfl))
    have he : lift alpha zeta =ᶠ[𝓝 q]
        fun x => ∫ r : K, bellmanLiftIntegrand alpha zeta (x, radius r) ∂mu := by
      filter_upwards [hU.mem_nhds hqU] with x hx
      apply bellman_integral_compact_radius_subtype K hK
      intro r hrK
      have hzero : zeta (bellmanPlaneDilation r.val x) = 0 := by
        by_contra hn
        exact hrK (hwindow x hx r (subset_tsupport zeta hn))
      simp only [hzero, mul_zero]
    exact (((hI q hqU).contDiffAt (hU.mem_nhds hqU)).congr_of_eventuallyEq he).contDiffWithinAt
  refine ⟨⟨_h_xinl_0, ?_⟩, ?_⟩
  · intro r hr q _
    let s := r
    let F : BellmanPositiveTime → ℝ := fun r =>
      r.val ^ (-1 - alpha) * zeta (bellmanPlaneDilation r.val q)
    have he (r : BellmanPositiveTime) :
        F (bellmanRadialScale s hr r) = s ^ (-1 - alpha) *
          (r.val ^ (-1 - alpha) *
            zeta (bellmanPlaneDilation r.val (bellmanPlaneDilation s q))) := by
      dsimp [F, bellmanRadialScale]
      rw [Real.mul_rpow hr.le r.property.le, bellmanPlaneDilation_comp]
      rw [mul_comm r.val s]
      ring
    apply mul_left_cancel₀ (Real.rpow_pos_of_pos hr (-1 - alpha)).ne'
    calc
      s ^ (-1 - alpha) * lift alpha zeta (bellmanPlaneDilation s q) =
          ∫ r, F (bellmanRadialScale s hr r) ∂bellmanPositiveTimeVolume := by
        simp_rw [he]
        rw [integral_const_mul]
        rfl
      _ = s⁻¹ * lift alpha zeta q := by
        rw [← (bellmanRadialScale s hr).measurableEmbedding.integral_map,
          map_bellmanPositiveTimeVolume_radialScale, integral_smul_measure,
          ENNReal.toReal_ofReal (inv_nonneg.mpr hr.le)]
        rfl
      _ = s ^ (-1 - alpha) * (s ^ alpha * lift alpha zeta q) := by
        rw [← mul_assoc, ← Real.rpow_add hr]
        have ha : -1 - alpha + alpha = (-1 : ℝ) := by ring
        rw [ha, Real.rpow_neg_one]
  · intro r hr q hq b
    exact bellmanOperator_comp_dilation r hr zeta hz q hq b

end HypoellipticAleksandrov.KineticAleksandrov
