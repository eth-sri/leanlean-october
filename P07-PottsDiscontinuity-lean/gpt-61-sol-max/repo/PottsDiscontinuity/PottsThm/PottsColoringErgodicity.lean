module
public import Mathlib

public import Mathlib.Probability.UniformOn
public import PottsDiscontinuity.PottsThm.ColoringErgodicity
public import PottsDiscontinuity.RCInfinite.Mixing

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology

open PottsDiscontinuity.FK
open PottsDiscontinuity.RCInfinite


noncomputable section

/-- The canonical iid cluster-colouring factor of an RC infinite-volume limit
is translation ergodic. -/
theorem clusterColoring_map_ergodic_of_RCmixing {C : Type*} [MeasurableSpace C]
    [MeasurableSingletonClass C] [Fintype C] [Nonempty C]
    (θ : FK.Parameters) (i : Fin 2) (φ : Measure LatticeConfiguration)
    (hφ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i φ) (c₀ : C) :
    IsTranslationErgodic
      ((φ.prod (iidFieldMeasure (ProbabilityTheory.uniformOn (Set.univ : Set C)))).map
        (clusterColoring c₀)) := by
  let ν : Measure C := ProbabilityTheory.uniformOn Set.univ
  
  have : IsProbabilityMeasure (iidFieldMeasure (I := Vertex) ν) := by
    change IsProbabilityMeasure (Measure.infinitePi  fun _  => ν )
    infer_instance
  have hcolorPres (a : Vertex)  :=
    iidFieldShift_measurePreserving ν (latticeShiftEquiv a)
  
  have hRCmix := isRCInfiniteVolumeLimit_interior_edge_mixing θ i φ hφ
  let : IsProbabilityMeasure φ := hφ.1
  exact mixingProduct_factor_translationErgodic
    (fun a ω => edgeTranslate a ω)
    (fun a u => iidFieldShift (latticeShiftEquiv a) u)
    (fun a => ⟨edgeTranslate_measurable a, hRCmix.1 a⟩) hcolorPres
      hRCmix.2   (fun A B hA hB => iidField_mixing_of_finite_separation ν c₀ latticeShiftEquiv eventually_latticeShift_disjoint hA hB)
    (clusterColoring c₀) (measurable_clusterColoring c₀)
     (clusterColoring_equivariant c₀) 

end
end PottsDiscontinuity.PottsThm
