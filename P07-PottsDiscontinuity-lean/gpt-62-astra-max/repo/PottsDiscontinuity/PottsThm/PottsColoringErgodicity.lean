module

public import PottsDiscontinuity.PottsThm.ColoringErgodicity
public import PottsDiscontinuity.RCInfinite.Mixing

@[expose] public section
namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter FK RCInfinite

variable {C : Type*} [MeasurableSpace C] [MeasurableSingletonClass C] [Fintype C]

noncomputable abbrev colorNoise (C : Type*) [MeasurableSpace C] [MeasurableSingletonClass C] :=
  iidFieldMeasure (I := Vertex) (ProbabilityTheory.uniformOn (Set.univ : Set C))

noncomputable def colorLaw (φ : Measure LatticeConfiguration) (pin : C) : Measure (Vertex → C) :=
  (φ.prod (colorNoise C)).map (clusterColoring pin)

instance (φ : Measure LatticeConfiguration) [IsProbabilityMeasure φ] (pin : C) :
    IsProbabilityMeasure (colorLaw φ pin) := by
  letI : Nonempty C := ⟨pin⟩
  unfold colorLaw; infer_instance

/-- The colour sampler is an equivariant factor of two mixing systems. -/
theorem colorLaw_mixing (θ : FK.Parameters) (i : Fin 2) {φ : Measure LatticeConfiguration}
    (hφ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i φ) (pin : C) :
    MixingFamily spinShift (colorLaw φ pin) cofinite := by
  letI : Nonempty C := ⟨pin⟩
  have := hφ.1
  have hc := iidField_mixing (ProbabilityTheory.uniformOn (Set.univ : Set C))
    latticeShiftEquiv eventually_latticeShift_disjoint
  exact ((isRCInfiniteVolumeLimit_interior_edge_mixing θ i φ hφ).prod hc).map
    (measurable_clusterColoring pin) (fun a => measurable_pi_iff.mpr fun x => measurable_pi_apply _)
    (fun a z => funext (clusterColoring_equivariant pin a z))

end PottsDiscontinuity.PottsThm
