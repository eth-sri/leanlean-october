module

public import PottsDiscontinuity.Infra.MeasureMixing
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.UniformOn

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Set Topology

section

variable {I C : Type*}

noncomputable def iidFieldMeasure [MeasurableSpace C]
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

private theorem iidField_independent_cylinders [DecidableEq I] [MeasurableSpace C]
    (ν : Measure C) [IsProbabilityMeasure ν] (F G : Finset I)
    (hFG : Disjoint F G) {A : Set (F → C)} {B : Set (G → C)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    iidFieldMeasure ν (cylinder F A ∩ cylinder G B) =
      iidFieldMeasure ν (cylinder F A) * iidFieldMeasure ν (cylinder G B) := by
  have h := ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : I => ν)
    (X := fun _ (c : C) => c) (by fun_prop)
  exact (h.indepFun_finset F G hFG fun i => measurable_pi_apply i).measure_inter_preimage_eq_mul
    A B hA hB

/-- Disjoint finite coordinate sets see independent noise once the shift is far enough. -/
theorem iidField_mixing_of_finite_separation [DecidableEq I] [MeasurableSpace C]
    (ν : Measure C) [IsProbabilityMeasure ν] (e : (ℤ × ℤ) → I ≃ I)
    (hsep : ∀ F G : Finset I, ∀ᶠ a : ℤ × ℤ in cofinite,
      Disjoint F (G.map (e a).symm.toEmbedding))
    {A B : Set (I → C)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun a : ℤ × ℤ =>
      (iidFieldMeasure ν).real (A ∩ iidFieldShift (e a) ⁻¹' B)) cofinite
      (𝓝 ((iidFieldMeasure ν).real A * (iidFieldMeasure ν).real B)) := by
  let μ : Measure (I → C) := iidFieldMeasure ν
  have : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))
  refine mixing_of_generators generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    μ (fun a => iidFieldShift_measurePreserving ν (e a)) ?_ hA hB
  intro R hR S hS
  obtain ⟨F, A, hA, rfl⟩ := (mem_measurableCylinders R).mp hR
  obtain ⟨G, B, hB, rfl⟩ := (mem_measurableCylinders S).mp hS
  unfold MixingLimit
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hsep F G] with a ha
  let σ := e a
  let G' := G.map σ.symm.toEmbedding
  let f (i : G) : G' := ⟨σ.symm i, Finset.mem_map.mpr ⟨i, i.property, rfl⟩⟩
  let B' : Set (G' → C) := (fun u i => u (f i)) ⁻¹' B
  have hB' : MeasurableSet B' := by
    exact (measurable_pi_iff.mpr (fun i => measurable_pi_apply (f i)) :
      Measurable fun (u : G' → C) (i : G) => u (f i)) hB
  have hpre : iidFieldShift σ ⁻¹' cylinder G B = cylinder G' B' := rfl
  have hμ :=
    (iidFieldShift_measurePreserving ν σ).measure_preimage (hB.cylinder G).nullMeasurableSet
  have hind := iidField_independent_cylinders ν F G' ha hA hB'
  rw [← hpre, hμ] at hind
  simpa [Measure.real_def] using (congrArg ENNReal.toReal hind).symm

end
end PottsDiscontinuity.PottsThm
