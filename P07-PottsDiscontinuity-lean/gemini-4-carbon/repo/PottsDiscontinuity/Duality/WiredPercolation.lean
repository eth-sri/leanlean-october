module

public import PottsDiscontinuity.Duality.LargeCircuitWitness
public import PottsDiscontinuity.Duality.PeierlsSummability
public import PottsDiscontinuity.Duality.ReverseInfiniteDuality
public import PottsDiscontinuity.RCInfinite.ClusterEvents
public import PottsDiscontinuity.RCInfinite.BoxExhaustion

/-! Exponential decay of the free two-point function forces positive wired
origin percolation at the dual parameter. The Peierls argument counts actual
connection events rather than enumerating exponentially many circuits. -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK FK.Medial MeasureTheory
noncomputable section

lemma no_infinite_cluster_opposite_indices_infinite (ω : LatticeConfiguration)
    (hno : ω ∉ existsInfiniteCluster) :
    {t : OppositeConnectionIndex |
      wholePlaneDualConfigurationHomeomorph ω ∈ oppositeConnectionEvent t}.Infinite := by
  intro hf
  let N := hf.toFinset.sup (fun t => t.1.1)
  obtain ⟨k, j, w, hk, hw, hconn⟩ := no_infinite_cluster_implies_opposite_connections ω hno (N + 1)
  have ht : ((k, w), j) ∈ hf.toFinset := hf.mem_toFinset.2 ⟨hw, hconn⟩
  have hle : k ≤ N := Finset.le_sup (f := fun t : OppositeConnectionIndex => t.1.1) ht
  omega

/-- The summable Peierls bound and actual wired-to-free duality give almost-sure
existence of an infinite cluster at the dual parameter. -/
theorem wired_ae_existsInfiniteCluster_of_free_decay (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ₀ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    ∀ᵐ ω ∂μ₁, ω ∈ existsInfiniteCluster := by
  have hmapped : ∀ᵐ η ∂μ₁.map wholePlaneDualConfigurationHomeomorph,
      {t : OppositeConnectionIndex | η ∈ oppositeConnectionEvent t}.Finite := by
    rw [wired_map_dual_eq_free θ μ₀ μ₁ hμ₀ hμ₁]
    exact free_ae_finite_oppositeConnections θ μ₀ hμ₀ C c hC hc hdecay
  filter_upwards [ae_of_ae_map wholePlaneDualConfigurationHomeomorph_measurable.aemeasurable hmapped]
    with ω hω
  by_contra hn
  exact no_infinite_cluster_opposite_indices_infinite ω hn hω

theorem wired_existsInfiniteCluster_eq_one_of_free_decay (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ₀ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    μ₁ existsInfiniteCluster = 1 := by
  have := hμ₁.1
  have hz : μ₁ (existsInfiniteCluster)ᶜ = 0 :=
    ae_iff.1 (wired_ae_existsInfiniteCluster_of_free_decay θ μ₀ μ₁ hμ₀ hμ₁ C c hC hc hdecay)
  have hmeas : MeasurableSet existsInfiniteCluster := RCInfinite.measurableSet_infiniteClusterEvent
  simpa only [hz, add_zero, measure_univ] using measure_add_measure_compl (μ := μ₁) hmeas

/-- Positive origin percolation follows by countability and translation
invariance, so no finite-energy loss depending on the chosen radius is needed. -/
theorem wired_origin_pos_of_free_exponential_decay (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ₀ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    0 < μ₁ (infiniteClusterAt 0) := by
  by_contra hn
  have hz : μ₁ (RCInfinite.infiniteAt (0, 0)) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hn)
  refine zero_ne_one ((?_ : μ₁ existsInfiniteCluster = 0).symm.trans
    (wired_existsInfiniteCluster_eq_one_of_free_decay θ μ₀ μ₁ hμ₀ hμ₁ C c hC hc hdecay))
  rw [show existsInfiniteCluster = ⋃ x, RCInfinite.infiniteAt x from
    RCInfinite.infiniteClusterEvent_eq_iUnion]
  refine measure_iUnion_null fun x => ?_
  have hmap := congrArg (· (RCInfinite.infiniteAt x))
    (RCInfinite.translation_invariant _ _ (dualParameters θ).property 1 μ₁ hμ₁ x)
  rw [Measure.map_apply (RCInfinite.edgeTranslate_measurable x)
    (RCInfinite.measurableSet_infiniteAt x),
    show RCInfinite.edgeTranslate x ⁻¹' RCInfinite.infiniteAt x = RCInfinite.infiniteAt (0, 0) by
      simpa [latticeTranslate] using RCInfinite.infiniteAt_preimage x (0, 0), hz] at hmap
  exact hmap.symm

end
end PottsDiscontinuity.Duality
