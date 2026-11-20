module

public import PottsDiscontinuity.Infra.Mixing
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.UniformOn

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Set Topology
open scoped ENNReal

noncomputable section

section
variable {I C : Type*}

abbrev iidFieldMeasure [MeasurableSpace C]
    (ν : Measure C) : Measure (I → C) := Measure.infinitePi (fun _ => ν)

def iidFieldShift (e : I ≃ I) (u : I → C) : I → C :=
  fun i => u (e.symm i)

theorem iidFieldShift_measurePreserving [MeasurableSpace C]
    (ν : Measure C) [IsProbabilityMeasure ν] (e : I ≃ I) :
    MeasurePreserving (iidFieldShift e) (iidFieldMeasure ν) (iidFieldMeasure ν) := by
  constructor
  · exact measurable_pi_iff.mpr fun i => measurable_pi_apply (e.symm i)
  · have hfun : iidFieldShift e =
        ⇑(MeasurableEquiv.piCongrLeft (fun _ : I => C) e) := by
      funext u i
      simp [iidFieldShift, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    rw [hfun]
    exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : I => ν) e

end

/-- Separated finite coordinate sets are independent in the product measure.
It suffices to check these cylinders, with no finiteness assumption on the colours. -/
theorem iidField_mixing {I C Γ : Type*} [MeasurableSpace C] (ν : Measure C)
    [IsProbabilityMeasure ν] (e : Γ → I ≃ I) {l : Filter Γ}
    (hsep : ∀ F G : Finset I, ∀ᶠ a in l, Disjoint F (G.map (e a).symm.toEmbedding)) :
    MixingFamily (fun a => iidFieldShift (e a)) (iidFieldMeasure ν) l := by
  have hp a := iidFieldShift_measurePreserving ν (e a)
  refine ⟨hp, fun {_ _} => mixing_of_piSystem hp generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders ?_⟩
  intro A hA B hB
  obtain ⟨F, U, hU, rfl⟩ := (mem_measurableCylinders A).mp hA
  obtain ⟨G, V, hV, rfl⟩ := (mem_measurableCylinders B).mp hB
  apply tendsto_const_nhds.congr'
  filter_upwards [hsep F G] with a ha
  let J := G.map (e a).symm.toEmbedding
  let r (u : J → C) (j : G) := u ⟨(e a).symm j, Finset.mem_map.mpr ⟨j, j.prop, rfl⟩⟩
  have hr : Measurable r := measurable_pi_iff.mpr fun j => measurable_pi_apply _
  have heval : ProbabilityTheory.iIndepFun (fun i (u : I → C) => u i) (iidFieldMeasure ν) :=
    ProbabilityTheory.iIndepFun_infinitePi (X := fun _ (c : C) => c) (by fun_prop)
  have h := (heval.indepFun_finset F J ha (fun i => measurable_pi_apply i)).measure_inter_preimage_eq_mul
    U (r ⁻¹' V) hU (hr hV)
  rw [Measure.real_def, Measure.real_def, Measure.real_def, ← ENNReal.toReal_mul,
    ← (hp a).measure_preimage hV.cylinder.nullMeasurableSet]
  exact congrArg ENNReal.toReal h.symm

end
end PottsDiscontinuity.PottsThm
