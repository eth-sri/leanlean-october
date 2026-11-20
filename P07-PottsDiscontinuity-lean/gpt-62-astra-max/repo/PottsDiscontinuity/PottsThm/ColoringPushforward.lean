module

public import PottsDiscontinuity.Potts.FreeCylinderPartition
public import PottsDiscontinuity.Potts.GhostCylinderPartition
public import PottsDiscontinuity.FK.BoxCoverage
public import PottsDiscontinuity.Frozen.Defs.IsPottsInfiniteVolumeLimit
public import PottsDiscontinuity.Potts.InfinitePartitionMeasurability
public import PottsDiscontinuity.PottsThm.SamplerObservations

@[expose] public section
namespace PottsDiscontinuity.PottsThm
open MeasureTheory Filter Topology FK Potts RCInfinite
open scoped ENNReal Classical

variable {q : ℕ} {φ : Measure LatticeConfiguration} [IsProbabilityMeasure φ]

private theorem colorLaw_partition (pin : Set.Icc 1 q) (A : Finset Vertex) (ξ : SpinSpace q)
    {I : Type*} [Finite I] {r : LatticeConfiguration → Setoid I} (K : Setoid I → ℝ)
    (hK : ∀ R, 0 ≤ K R) (hm : ∀ R, MeasurableSet {ω | r ω = R})
    (hf : ∀ᵐ ω ∂φ, colorNoise _ {u | ∀ a : A, clusterColoring pin (ω,u) a.val = ξ a.val} =
      ENNReal.ofReal (K (r ω))) :
    (colorLaw φ pin).real (spinCylinder A ξ) = partitionExpectation φ r K := by
  rw [Measure.real_def, colorLaw_apply pin (spinCylinder_isClopen q A ξ).isOpen.measurableSet]
  convert! toReal_lintegral_finitePartitionKernel φ r K hK hm using 1
  congr 1; apply lintegral_congr_ae
  filter_upwards [hf] with ω h; simpa [Set.preimage, spinCylinder] using h

/-- On a box containing the observation set, the finite-volume cylinder in the
statement is precisely the one read on the subtype of observed sites. -/
private theorem box_pattern_sum (q : ℕ) (β : ℝ) (i : Fin (q+1)) {A : Finset Vertex} (ξ : SpinSpace q)
    {n} (hA : A ⊆ box n) {D : Finset (SpinConfiguration q (box n))} (hD : ∀ σ, σ ∈ D) :
    (∑ σ ∈ D, if ∀ a : A, σ ⟨a.val, hA a.prop⟩ = ξ a.val
        then pottsProb q (box n) β i σ else 0) =
      ∑ σ : SpinConfiguration q (box n), if ∀ x ∈ A, ∃ h : x ∈ box n, σ ⟨x,h⟩ = ξ x
        then pottsProb q (box n) β i σ else 0 := by
  apply Finset.sum_congr (Finset.ext fun σ => by grind); intro σ _
  congr 1; apply propext; constructor
  · exact fun h x hx => ⟨hA hx, h ⟨x,hx⟩⟩
  · grind

variable (hq : 2 ≤ q) {β : ℝ} (hβ : 0 < β) (φP : ProbabilityMeasure LatticeConfiguration)

theorem free_colorLaw_limit
    (hw : Tendsto (fun n => boxProbabilityMeasure (fkParameters hq hβ) (0,0) n) atTop (𝓝 φP))
    (hfin : ∀ᵐ ω ∂φP.toMeasure, ∀ x, (cluster ω x).Finite) :
    IsPottsInfiniteVolumeLimit q β 0 (colorLaw φP.toMeasure ⟨1, le_rfl, by omega⟩) := by
  refine ⟨inferInstance, fun A ξ => ?_⟩
  have hs : ∀ᶠ n in atTop, A ⊆ box n := (eventually_all_finset A).mpr (fun x _ => FK.eventually_mem_box x)
  let K := fun R => clusterCylinderProbability R id (fun a : A => ξ a.val)
  have ht := free_partitionExpectation_tendsto _ φP hw (fun a : A => a.val) K
  have hk : (colorLaw φP.toMeasure ⟨1, le_rfl, by omega⟩).real (spinCylinder A ξ) = partitionExpectation φP.toMeasure (infiniteFreePartition (fun a : A => a.val)) K := by
    apply colorLaw_partition _ A ξ _
      (fun R => by dsimp [K, clusterCylinderProbability]; split_ifs <;> positivity)
      (infiniteFreePartition_measurableSet _)
    filter_upwards [hfin] with ω hω
    exact freeClusterColoring_fiber_cylinder_uniform q (by omega) ω A ξ hω
  rw [← hk] at ht
  apply ht.congr'
  filter_upwards [hs] with n hn
  exact (potts_free_cylinder_eq_partitionExpectation q hq β hβ n _ (fun a : A => hn a.prop) _).symm.trans
      (box_pattern_sum q β 0 ξ hn (by simp))


theorem wired_colorLaw_limit (i : Fin (q+1)) (hi : 1 ≤ (i:ℕ))
    (hw : Tendsto (fun n => wiredBoxProbabilityMeasure (fkParameters hq hβ) (0,0) n) atTop (𝓝 φP)) :
    IsPottsInfiniteVolumeLimit q β i (colorLaw φP.toMeasure (boundaryColor hi)) := by
  refine ⟨inferInstance, fun A ξ => ?_⟩
  have hs : ∀ᶠ n in atTop, A ⊆ box n := (eventually_all_finset A).mpr (fun x _ => FK.eventually_mem_box x)
  let K := fun R => pinnedClusterCylinderProbability R some (fun a : A => ξ a.val) none (boundaryColor hi)
  have ht := wired_partitionExpectation_tendsto q hq β hβ φP hw (Option.map (fun a : A => a.val)) K
  have hk : (colorLaw φP.toMeasure (boundaryColor hi)).real (spinCylinder A ξ) = partitionExpectation φP.toMeasure (infiniteWiredPartition (Option.map (fun a : A => a.val))) K := by
    apply colorLaw_partition _ A ξ _
      (fun R => by dsimp [K, pinnedClusterCylinderProbability]; split_ifs <;> positivity)
      (infiniteWiredPartition_measurableSet _)
    exact .of_forall fun ω => wiredClusterColoring_fiber_cylinder_uniform q (by omega) ω A ξ i hi
  rw [← hk] at ht
  apply ht.congr'
  filter_upwards [hs, eventually_gt_atTop 0] with n hn hn0
  exact (potts_ghost_cylinder_eq_partitionExpectation q hq β hβ i hi n hn0 _ (fun a : A => hn a.prop) _).symm.trans
      (box_pattern_sum q β i ξ hn (by simp))


end PottsDiscontinuity.PottsThm
