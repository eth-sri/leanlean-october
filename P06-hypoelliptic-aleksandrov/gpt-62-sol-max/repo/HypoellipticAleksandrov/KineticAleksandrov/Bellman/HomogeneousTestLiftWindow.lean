module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftSupport
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Compact positive-radius windows and their literal integral restrictions -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A closed interval of positive radii is compact on the source radial subtype. -/
theorem bellmanRadiusWindow_isCompact (a b : ℝ) (ha : 0 < a) :
    IsCompact {r : BellmanPositiveTime | r.val ∈ Icc a b} := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : (Subtype.val : BellmanPositiveTime → ℝ) '' {r | r.val ∈ Icc a b} =
      Icc a b := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hr
      exact ⟨⟨r, lt_of_lt_of_le ha hr.1⟩, hr, rfl⟩
  rw [he]
  exact isCompact_Icc

/-- Restricting a test to a compact radial window is exactly a subtype integral. -/
theorem bellman_integral_compact_radius_subtype {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (K : Set BellmanPositiveTime) (hK : IsCompact K)
    (f : BellmanPositiveTime → F) (hf : ∀ r, r ∉ K → f r = 0) :
    (∫ r, f r ∂bellmanPositiveTimeVolume) =
      ∫ r : K, f r.val ∂Measure.comap Subtype.val bellmanPositiveTimeVolume := by
  rw [← (MeasurableEmbedding.subtype_coe hK.measurableSet).integral_map,
    map_comap_subtype_coe hK.measurableSet]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm

/-- Pullback radial volume is finite on a compact radius window. -/
theorem bellman_radius_window_volume_finite (K : Set BellmanPositiveTime)
    (hK : IsCompact K) :
    IsFiniteMeasure (Measure.comap (Subtype.val : K → BellmanPositiveTime)
      bellmanPositiveTimeVolume) := by
  exact ⟨by rw [(MeasurableEmbedding.subtype_coe hK.measurableSet).comap_apply,
    Subtype.coe_image_univ]; exact hK.measure_lt_top⟩

/-- Near a punctured point the lift is an integral over a single compact window. -/
theorem bellman_lift_locally_eq_subtype (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ q ∈ U ∧ ∃ K : Set BellmanPositiveTime, IsCompact K ∧
      (∀ r : BellmanPositiveTime, bellmanPlaneDilation r.val q ∈ tsupport zeta → r ∈ K) ∧
      lift alpha zeta =ᶠ[𝓝 q] fun x => ∫ r : K,
        r.val.val ^ (-1 - alpha) * zeta (bellmanPlaneDilation r.val.val x)
          ∂Measure.comap Subtype.val bellmanPositiveTimeVolume := by
  obtain ⟨U, hU, hqU, _, a, b, ha, _, hwindow⟩ :=
    bellman_compact_test_local_radius_window zeta hc hs q hq
  have hK := bellmanRadiusWindow_isCompact a b ha
  refine ⟨U, hU, hqU, _, hK, fun r => hwindow q hqU r, ?_⟩
  filter_upwards [hU.mem_nhds hqU] with x hx
  apply bellman_integral_compact_radius_subtype _ hK
  intro r hrK
  rw [image_eq_zero_of_notMem_tsupport (fun hs => hrK (hwindow x hx r hs)), mul_zero]

end HypoellipticAleksandrov.KineticAleksandrov
