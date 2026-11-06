module
public import Mathlib

public import FixedPointTheorems.brouwer
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

open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts




noncomputable section

section

variable (q : ℕ) (hq : 4 < q) (φ : ProbabilityMeasure LatticeConfiguration)
include hq

/-- The canonical free cluster coloring has the Edwards--Sokal cylinder law
whenever the bond measure almost surely has only finite clusters. -/
theorem freeColoringMap_isFreeESC 
    (hno : φ.toMeasure Duality.existsInfiniteCluster = 0) :
    IsFreeEdwardsSokalColouring q φ.toMeasure
      ((φ.toMeasure.prod (iidFieldMeasure
        (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))))).map
          (clusterColoring (⟨1, le_rfl, by omega⟩ : Set.Icc 1 q))) := by
  classical
  let ν : Measure (Set.Icc 1 q) :=
    ProbabilityTheory.uniformOn Set.univ
  let c₀ : Set.Icc 1 q := ⟨1, le_rfl, by omega⟩
  have : Nonempty (Set.Icc 1 q) := ⟨c₀⟩
  
  have : IsProbabilityMeasure (iidFieldMeasure (I := Vertex) ν) := by
    change IsProbabilityMeasure (Measure.infinitePi  fun _  => ν )
    infer_instance
  
  let F  :=
    clusterColoring c₀
  have hF : Measurable F := measurable_clusterColoring c₀
  refine ⟨inferInstance, ?_⟩
  intro A ξ
  let E  :=
    {z | ∀ a : ↥A, clusterColoring c₀ z a.val = ξ a.val}
  have hEq : E = F ⁻¹' spinCylinder q A ξ := by
    
    simp [E, F, spinCylinder]
  have hCyl  :=
    (spinCylinder_isClopen q A ξ).isOpen.measurableSet
  
  have hfinite_ae : ∀ᵐ ω ∂φ.toMeasure, ∀ x, (RCInfinite.cluster ω x).Finite := by
    have hnot : ∀ᵐ ω ∂φ.toMeasure, ω ∉ Duality.existsInfiniteCluster := ae_iff.mpr (by simpa using hno)
    filter_upwards [hnot] with ω hω x
    simp only [Duality.existsInfiniteCluster, Set.mem_ofPred_eq, not_exists] at hω
    by_contra hfinite
    exact hω x (by assumption)
  let r  :=
     infiniteFreePartition  fun a : ↥A => a.val  
  let K  :=
    fun R => clusterCylinderProbability R id  fun a : ↥A => ξ a.val 
  
  
  
  calc
    ((φ.toMeasure.prod (iidFieldMeasure ν)).map F).real (spinCylinder q A ξ) =
        (∫⁻ ω, ENNReal.ofReal (K (r ω)) ∂φ.toMeasure).toReal := by
      rw [Measure.real_def, Measure.map_apply hF hCyl, ← hEq, Measure.prod_apply (by
                                                                                    rw [hEq]
                                                                                    exact hF hCyl)]
      rw [lintegral_congr_ae (by
                                filter_upwards [hfinite_ae] with ω hfinite
                                
                                
                                exact freeClusterColoring_fiber_cylinder_uniform q (by omega) ω A ξ hfinite)]
    _ = freeESCylinder q φ.toMeasure A ξ := by
      rw [toReal_lintegral_finitePartitionKernel φ.toMeasure r K  fun R => by
                                                                    dsimp [K, clusterCylinderProbability]
                                                                    split_ifs <;> positivity   (infiniteFreePartition_measurableSet Subtype.val) ]
      rfl

/-- The canonical wired cluster coloring has the wired Edwards--Sokal cylinder
law for every bond measure. Infinite clusters are assigned the fixed boundary
color. -/
theorem wiredColoringMap_isWiredESC  (i : Fin (q + 1))
    (hi : 1 ≤ (i : ℕ)) :
    IsWiredEdwardsSokalColouring q φ.toMeasure i hi
      ((φ.toMeasure.prod (iidFieldMeasure
        (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))))).map
          (clusterColoring (boundaryColor q i hi))) := by
  
  let ν : Measure (Set.Icc 1 q) :=
    ProbabilityTheory.uniformOn Set.univ
  let c₀  := boundaryColor q i hi
  have : Nonempty (Set.Icc 1 q) := by
                                     aesop
  
  have : IsProbabilityMeasure (iidFieldMeasure (I := Vertex) ν) := by
    change IsProbabilityMeasure (Measure.infinitePi  fun _  => ν )
    infer_instance
  
  let F  :=
    clusterColoring c₀
  have hF : Measurable F := measurable_clusterColoring c₀
  refine ⟨inferInstance, ?_⟩
  intro A ξ
  let E  :=
    {z | ∀ a : ↥A, clusterColoring c₀ z a.val = ξ a.val}
  have hEq : E = F ⁻¹' spinCylinder q A ξ := by
    
    simp [E, F, spinCylinder]
  have hCyl  :=
    (spinCylinder_isClopen q A ξ).isOpen.measurableSet
  
  let r  :=
    (infiniteWiredPartition (Option.map  fun a : ↥A => a.val ))
  let K  := fun R =>
    pinnedClusterCylinderProbability R some (fun a : ↥A => ξ a.val) none c₀
  
  
  have hfiber (ω : LatticeConfiguration) :
      iidFieldMeasure ν (Prod.mk ω ⁻¹' E) = ENNReal.ofReal (K (r ω)) := by
    
    exact wiredClusterColoring_fiber_cylinder_uniform q (by omega) ω A ξ i hi
  calc
    ((φ.toMeasure.prod (iidFieldMeasure ν)).map F).real (spinCylinder q A ξ) =
        (∫⁻ ω, ENNReal.ofReal (K (r ω)) ∂φ.toMeasure).toReal := by
      rw [Measure.real_def, Measure.map_apply hF hCyl, ← hEq, Measure.prod_apply (by
                                                                                    rw [hEq]
                                                                                    exact hF hCyl)]
      simp_all
    _ = wiredESCylinder q φ.toMeasure i hi A ξ := by
      rw [toReal_lintegral_finitePartitionKernel φ.toMeasure r K  fun R => by
                                                                    dsimp [K, pinnedClusterCylinderProbability]
                                                                    split_ifs <;> positivity   (infiniteWiredPartition_measurableSet (Option.map Subtype.val)) ]
      rfl

end

end
end PottsDiscontinuity.PottsThm
