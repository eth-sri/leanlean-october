module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.LargeCircuitWitness
public import PottsDiscontinuity.Duality.PeierlsSummability
public import PottsDiscontinuity.Duality.PercolationErgodicity
public import PottsDiscontinuity.Duality.ReverseInfiniteDuality

/-! Exponential decay of the free two-point function forces positive wired
origin percolation at the dual parameter. The Peierls argument counts actual
connection events rather than enumerating exponentially many circuits. -/

public section

namespace PottsDiscontinuity.Duality
open FK FK.Medial MeasureTheory
noncomputable section

theorem no_infinite_cluster_opposite_indices_infinite (ω : LatticeConfiguration)
    (hno : ω ∉ existsInfiniteCluster) :
    {t : OppositeConnectionIndex |
      wholePlaneDualConfigurationHomeomorph ω ∈ oppositeConnectionEvent t}.Infinite := by
  intro hf
  let N := hf.toFinset.sup (fun t => t.1.1)
  obtain ⟨k,j,w,hk,hw,hconn⟩ := no_infinite_cluster_implies_opposite_connections ω hno (N+1)
  have ht : ((k,w),j) ∈ hf.toFinset := hf.mem_toFinset.2 ⟨hw,hconn⟩
  have hle : k ≤ N := Finset.le_sup (f := fun t : OppositeConnectionIndex => t.1.1) ht
  omega

section
variable (θ : Parameters) (μ₀ μ₁ : Measure LatticeConfiguration) (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀) (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hdecay : ∀ x : LatticeVertex, twoPoint μ₀ x ≤ C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|)))
include θ μ₀ μ₁ hμ₀ hμ₁ C c hC hc hdecay
/-- The summable Peierls bound and actual wired-to-free duality give almost-sure
existence of an infinite cluster at the dual parameter. -/
theorem wired_ae_existsInfiniteCluster_of_free_decay  :
    ∀ᵐ ω ∂μ₁, ω ∈ existsInfiniteCluster := by
  have hfree := free_ae_finite_oppositeConnections θ μ₀ hμ₀ C c hC hc hdecay
  have hmap := wired_map_dual_eq_free θ μ₀ μ₁ hμ₀ hμ₁
  have hmapped : ∀ᵐ η ∂μ₁.map wholePlaneDualConfigurationHomeomorph,
      {t : OppositeConnectionIndex | η ∈ oppositeConnectionEvent t}.Finite := by
    simp_all
  filter_upwards [(ae_of_ae_map wholePlaneDualConfigurationHomeomorph_measurable.aemeasurable hmapped)] with ω hω
  by_contra hn
  simp_all [no_infinite_cluster_opposite_indices_infinite]

/-- Positive origin percolation follows by countability and translation
invariance, so no finite-energy loss depending on the chosen radius is needed. -/
theorem wired_origin_pos_of_free_exponential_decay  :
    0 < μ₁ (infiniteClusterAt 0) := by
  have := hμ₁.1
  have hz : μ₁ (existsInfiniteCluster)ᶜ = 0 := ae_iff.1 (wired_ae_existsInfiniteCluster_of_free_decay θ μ₀ μ₁ hμ₀ hμ₁ C c hC hc hdecay)
  have hmeas : MeasurableSet existsInfiniteCluster := RCInfinite.measurableSet_infiniteClusterEvent
  have hone : μ₁ existsInfiniteCluster = 1 := by
    simp_all
  apply (existsInfiniteCluster_pos_iff_origin_pos (dualParameters θ) 1 μ₁ hμ₁).1
  positivity

/-- The final zero–one step uses the proved ergodicity-based zero–one law for
infinite-volume random-cluster measures (`RCInfinite/`), rather than an
additional zero–one premise. -/
theorem wired_existsInfiniteCluster_eq_one_of_free_decay  :
    μ₁ existsInfiniteCluster = 1 :=
  existsInfiniteCluster_eq_one_of_origin_pos (dualParameters θ) 1 μ₁ hμ₁
    (wired_origin_pos_of_free_exponential_decay θ μ₀ μ₁ hμ₀ hμ₁ C c hC hc hdecay)
end

end
end PottsDiscontinuity.Duality
