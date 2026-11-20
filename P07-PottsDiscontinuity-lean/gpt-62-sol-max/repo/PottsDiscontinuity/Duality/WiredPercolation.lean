module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.HalfPlaneBoundary
public import PottsDiscontinuity.Duality.PeierlsSummability
public import PottsDiscontinuity.Duality.PercolationErgodicity
public import PottsDiscontinuity.Duality.ReverseInfiniteDuality

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
  let N := hf.toFinset.sup (fun t => t.1)
  obtain ⟨k,w,hk,hw,hconn⟩ := no_infinite_cluster_implies_opposite_connections ω hno (N+1)
  have ht : (k,w) ∈ hf.toFinset := hf.mem_toFinset.2 ⟨hw,hconn⟩
  grind [Finset.le_sup]

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
  have hfree := free_ae_finite_oppositeConnections θ μ₀ hμ₀ C c hC hc hdecay
  have hmap := wired_map_dual_eq_free θ μ₀ μ₁ hμ₀ hμ₁
  have hmapped : ∀ᵐ η ∂μ₁.map wholePlaneDualConfigurationHomeomorph,
      {t : OppositeConnectionIndex | η ∈ oppositeConnectionEvent t}.Finite := by
    simp_all
  have hfinite := ae_of_ae_map wholePlaneDualConfigurationHomeomorph_measurable.aemeasurable hmapped
  filter_upwards [hfinite] with ω hω
  by_contra hn
  exact no_infinite_cluster_opposite_indices_infinite ω hn hω

/-- The almost-sure percolation event has measure one; countability and
translation invariance then give positive probability at the origin. -/
theorem wired_percolation_of_free_decay (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ₀ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    μ₁ existsInfiniteCluster = 1 ∧ 0 < μ₁ (infiniteClusterAt 0) := by
  have := hμ₁.1
  have hae := wired_ae_existsInfiniteCluster_of_free_decay θ μ₀ μ₁ hμ₀ hμ₁ C c hC hc hdecay
  have hz : μ₁ (existsInfiniteCluster)ᶜ = 0 := ae_iff.1 hae
  have hmeas : MeasurableSet existsInfiniteCluster := RCInfinite.measurableSet_infiniteClusterEvent
  have hone : μ₁ existsInfiniteCluster = 1 := by
    simp_all
  refine ⟨hone, (existsInfiniteCluster_pos_iff_origin_pos (dualParameters θ) 1 μ₁ hμ₁).1 ?_⟩
  simp [hone]

end
end PottsDiscontinuity.Duality
