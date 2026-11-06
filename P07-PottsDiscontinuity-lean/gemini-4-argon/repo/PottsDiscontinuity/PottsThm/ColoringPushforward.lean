module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.Potts.ESCylinderLaw
public import PottsDiscontinuity.Potts.InfinitePartitionMeasurability
public import PottsDiscontinuity.PottsThm.ColoringCylinderLaw

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory
open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite
open PottsDiscontinuity.Duality
open scoped ENNReal

noncomputable section

theorem freeColoringMap_isFreeESC (q : ℕ) (hq : 4 < q)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hno : φ.toMeasure Duality.existsInfiniteCluster = 0) :
    IsFreeEdwardsSokalColouring q φ.toMeasure
      ((φ.toMeasure.prod (iidFieldMeasure
        (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))))).map
          (clusterColoring (⟨1, le_rfl, by omega⟩ : Set.Icc 1 q))) := by
  classical
  let ν : Measure (Set.Icc 1 q) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))
  let c₀ : Set.Icc 1 q := ⟨1, le_rfl, by omega⟩
  have : Nonempty (Set.Icc 1 q) := ⟨c₀⟩
  have : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.uniformOn _))
  have : IsProbabilityMeasure (iidFieldMeasure (I := Vertex) ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : Vertex => ν)))
  have : IsProbabilityMeasure φ.toMeasure := φ.property
  have hF : Measurable (clusterColoring c₀ : _ → SpinSpace q) := measurable_clusterColoring c₀
  refine ⟨inferInstance, fun A ξ => ?_⟩
  let E : Set (LatticeConfiguration × (Vertex → Set.Icc 1 q)) :=
    {z | ∀ a : ↥A, clusterColoring c₀ z a.val = ξ a.val}
  have hEq : E = clusterColoring c₀ ⁻¹' spinCylinder q A ξ := by ext; simp [E, spinCylinder]
  have hCyl : MeasurableSet (spinCylinder q A ξ) :=
    (spinCylinder_isClopen q A ξ).isOpen.measurableSet
  have hfinite_ae : ∀ᵐ ω ∂φ.toMeasure, ∀ x, (RCInfinite.cluster ω x).Finite := by
    filter_upwards [(ae_iff (p := fun ω => ω ∉ Duality.existsInfiniteCluster)).mpr
      (by simpa using hno)] with ω hω x
    by_contra hfinite
    exact hω ⟨x, by simpa [RCInfinite.cluster, Duality.cluster] using hfinite⟩
  let r : LatticeConfiguration → Setoid (↥A) := infiniteFreePartition (fun a : ↥A => a.val)
  let K : Setoid (↥A) → ℝ := fun R => clusterCylinderProbability R id (fun a : ↥A => ξ a.val)
  have hfiber_ae : ∀ᵐ ω ∂φ.toMeasure,
      iidFieldMeasure ν (Prod.mk ω ⁻¹' E) = ENNReal.ofReal (K (r ω)) := by
    filter_upwards [hfinite_ae] with ω hfinite
    let : Fintype (Quotient (r ω)) := Fintype.ofFinite _
    exact freeClusterColoring_fiber_cylinder_uniform q (by omega) ω A ξ hfinite
  rw [Measure.real_def, Measure.map_apply hF hCyl, ← hEq, Measure.prod_apply (hEq ▸ hF hCyl),
    lintegral_congr_ae hfiber_ae,
    toReal_lintegral_finitePartitionKernel φ.toMeasure r K
      (fun R => by dsimp [K, clusterCylinderProbability]; split_ifs <;> positivity)
      (infiniteFreePartition_measurableSet (fun a : ↥A => a.val))]
  rfl

theorem wiredColoringMap_isWiredESC (q : ℕ) (hq : 4 < q)
    (φ : ProbabilityMeasure LatticeConfiguration) (i : Fin (q + 1))
    (hi : 1 ≤ (i : ℕ)) :
    IsWiredEdwardsSokalColouring q φ.toMeasure i hi
      ((φ.toMeasure.prod (iidFieldMeasure
        (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))))).map
          (clusterColoring (boundaryColor q i hi))) := by
  classical
  let ν : Measure (Set.Icc 1 q) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))
  let c₀ : Set.Icc 1 q := boundaryColor q i hi
  have : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.uniformOn _))
  have : IsProbabilityMeasure (iidFieldMeasure (I := Vertex) ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : Vertex => ν)))
  have : IsProbabilityMeasure φ.toMeasure := φ.property
  have hF : Measurable (clusterColoring c₀ : _ → SpinSpace q) := measurable_clusterColoring c₀
  refine ⟨inferInstance, fun A ξ => ?_⟩
  let E : Set (LatticeConfiguration × (Vertex → Set.Icc 1 q)) :=
    {z | ∀ a : ↥A, clusterColoring c₀ z a.val = ξ a.val}
  have hEq : E = clusterColoring c₀ ⁻¹' spinCylinder q A ξ := by ext; simp [E, spinCylinder]
  have hCyl : MeasurableSet (spinCylinder q A ξ) :=
    (spinCylinder_isClopen q A ξ).isOpen.measurableSet
  let r : LatticeConfiguration → Setoid (Option ↥A) :=
    infiniteWiredPartition (Option.map (fun a : ↥A => a.val))
  let K : Setoid (Option ↥A) → ℝ := fun R =>
    pinnedClusterCylinderProbability R some (fun a : ↥A => ξ a.val) none c₀
  have hfiber (ω : LatticeConfiguration) :
      iidFieldMeasure ν (Prod.mk ω ⁻¹' E) = ENNReal.ofReal (K (r ω)) :=
    wiredClusterColoring_fiber_cylinder_uniform q (by omega) ω A ξ i hi
  rw [Measure.real_def, Measure.map_apply hF hCyl, ← hEq, Measure.prod_apply (hEq ▸ hF hCyl),
    lintegral_congr_ae (Filter.Eventually.of_forall hfiber),
    toReal_lintegral_finitePartitionKernel φ.toMeasure r K
      (fun R => by dsimp [K, pinnedClusterCylinderProbability]; split_ifs <;> positivity)
      (infiniteWiredPartition_measurableSet (Option.map (fun a : ↥A => a.val)))]
  rfl

end
end PottsDiscontinuity.PottsThm
