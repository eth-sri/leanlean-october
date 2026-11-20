/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.CylinderDetermination
public import PottsDiscontinuity.FK.BoxExhaustion
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Weak convergence from monotone finite cylinders

On the compact whole-lattice configuration space, monotonicity of every finite
all-open cylinder probability forces weak convergence of the probability laws.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open Set MeasureTheory Filter Topology
noncomputable section


/-- The coordinate map recording every finite all-open cylinder probability. -/
def cylinderProbabilityCoordinates (μ : ProbabilityMeasure LatticeConfiguration) :
    Finset squareLattice.edgeSet → NNReal :=
  fun F => μ (LatticeConfiguration.allOpen F)

theorem continuous_cylinderProbabilityCoordinates :
    Continuous cylinderProbabilityCoordinates := by
  refine continuous_pi fun F => ?_
  rw [continuous_iff_continuousAt]
  intro μ
  exact LatticeConfiguration.tendsto_allOpen_of_weak tendsto_id F

theorem cylinderCoordinates_embedding : IsClosedEmbedding cylinderProbabilityCoordinates :=
  continuous_cylinderProbabilityCoordinates.isClosedEmbedding fun _ _ h =>
    LatticeConfiguration.probabilityMeasure_eq_of_allOpen (congrFun h)

variable {X : Type*}

/-- Convergence along every nested exhaustion by translated boxes. -/
def IsBoxLimit [TopologicalSpace X] (g : LatticeVertex → ℕ → X) (z : X) : Prop :=
  ∀ (c : ℕ → LatticeVertex) (r : ℕ → ℕ),
    (∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n+1)) (r (n+1))) →
    (∀ v, ∃ n, v ∈ latticeBox (c n) (r n)) → Tendsto (fun n => g (c n) (r n)) atTop (𝓝 z)

/-- The supremum over all boxes is reached in the limit of any exhaustion.
Use the dual order for decreasing cylinder probabilities. -/
theorem exists_boxLimit_of_mono [ConditionallyCompleteLinearOrder X]
    [TopologicalSpace X] [OrderTopology X] (g : LatticeVertex → ℕ → X) (u : X)
    (hu : ∀ c r, g c r ≤ u) (hm : ∀ c d r s, latticeBox c r ⊆ latticeBox d s → g c r ≤ g d s) :
    ∃ z, IsBoxLimit g z := by
  let G (b : LatticeVertex × ℕ) := g b.1 b.2
  have hG : BddAbove (range G) := ⟨u, by rintro _ ⟨b,rfl⟩; grind⟩
  refine ⟨⨆ b, G b, fun c r hn he => ?_⟩
  let f n := g (c n) (r n)
  have hf : BddAbove (range f) := ⟨u, by rintro _ ⟨n,rfl⟩; grind⟩
  have hsup : (⨆ b, G b) = ⨆ n, f n := by
    apply le_antisymm <;> apply ciSup_le
    · intro b
      obtain ⟨n, h⟩ := latticeBox_subset_eventually_of_nested_exhaustive hn he b.1 b.2
      exact le_ciSup_of_le hf n (hm _ _ _ _ (h n le_rfl))
    · exact fun n => le_ciSup_of_le hG (c n, r n) le_rfl
  rw [hsup]
  exact tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hm _ _ _ _ (hn n)) hf

/-- Convergent cylinder coordinates determine a unique weak box limit. -/
theorem existsUnique_boxLimit (g : LatticeVertex → ℕ → ProbabilityMeasure LatticeConfiguration)
    (hc : ∀ F, ∃ z, IsBoxLimit (fun a n => cylinderProbabilityCoordinates (g a n) F) z) :
    ∃! μ, IsBoxLimit g μ := by
  choose z hz using hc
  have ht :=
    tendsto_pi_nhds.2 fun F => hz F _ _ origin_latticeBox_nested origin_latticeBox_exhaustive
  obtain ⟨μ, rfl⟩ := cylinderCoordinates_embedding.isClosed_range.mem_of_tendsto ht
    (.of_forall fun n => mem_range_self (g (0,0) n))
  refine ⟨μ, fun c r hn he => cylinderCoordinates_embedding.tendsto_nhds_iff.2
    (tendsto_pi_nhds.2 fun F => hz F c r hn he), fun ν hν => ?_⟩
  exact tendsto_nhds_unique (hν _ _ origin_latticeBox_nested origin_latticeBox_exhaustive)
    (cylinderCoordinates_embedding.tendsto_nhds_iff.2 ht)

end
end PottsDiscontinuity.FK
