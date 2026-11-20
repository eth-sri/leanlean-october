/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.MeasureTheory.CylinderLaws
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

variable {α : Type*} [MeasurableSpace α]

/-- Record a measure by its masses on a chosen family of sets. -/
abbrev measureMassCode {S : Set (Set α)} {p : Measure α → Prop} (μ : Subtype p) (U : S) : ℝ≥0∞ :=
  μ.1 U.1

section
variable {S : Set (Set α)} {p : Measure α → Prop} (hS : ∀ U : S, MeasurableSet U.1)
include S hS

theorem measurable_measureMassCode : Measurable (measureMassCode (p := p) (S := S)) :=
  .of_eval fun U => (Measure.measurable_coe (hS U)).comp measurable_subtype_coe

/-- The code generates the usual σ-algebra if the underlying measure is measurable from it. -/
theorem measureMassCode_comap_eq
    (hforget : @Measurable (Subtype p) (Measure α) (MeasurableSpace.pi.comap (measureMassCode (S := S))) _ Subtype.val) :
    MeasurableSpace.pi.comap (measureMassCode (p := p) (S := S)) = Subtype.instMeasurableSpace :=
  le_antisymm (measurable_measureMassCode hS).comap_le hforget.comap_le

end

/-- Open-set masses generate the σ-algebra of finite measures on a Borel space. -/
theorem finiteOpenMassCode_comap_eq [TopologicalSpace α] [BorelSpace α] :
    MeasurableSpace.pi.comap (measureMassCode (S := {U : Set α | IsOpen U}) (p := IsFiniteMeasure)) =
      (inferInstance : MeasurableSpace (FiniteMeasure α)) := by
  refine measureMassCode_comap_eq (fun U => U.2.measurableSet) ?_
  let m : MeasurableSpace (FiniteMeasure α) :=
    MeasurableSpace.pi.comap (measureMassCode (S := {U : Set α | IsOpen U}) (p := IsFiniteMeasure))
  let _ := m
  have hc : @Measurable (FiniteMeasure α) ({U : Set α // IsOpen U} → ℝ≥0∞)
      m _ measureMassCode := .of_comap_le le_rfl
  letI : ∀ μ : Subtype (IsFiniteMeasure : Measure α → Prop), IsFiniteMeasure μ.1 := fun μ => μ.2
  exact Measurable.measure_of_isPiSystem (BorelSpace.measurable_eq (α := α)) isPiSystem_isOpen
    (fun U hU => (measurable_pi_iff.mp hc) ⟨U, hU⟩) ((measurable_pi_iff.mp hc) ⟨univ, isOpen_univ⟩)

/-- Finite vectors of masses determine the law of random measures when the mass coordinates
of individual measures generate their σ-algebra. -/
theorem identDistrib_measure_of_mass_fdd {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P]
    {S : Set (Set α)} {p : Measure α → Prop} {M : Ω → Measure α} {N : Ω' → Measure α}
    (hc : MeasurableSpace.pi.comap (measureMassCode (S := S) (p := p)) = Subtype.instMeasurableSpace)
    (hM : AEMeasurable M P) (hN : AEMeasurable N P') (hMp : ∀ ω, p (M ω)) (hNp : ∀ ω, p (N ω))
    (h : ∀ s : Finset S, P.map (fun ω (j : s) => M ω j.1.1) = P'.map (fun ω (j : s) => N ω j.1.1)) :
    IdentDistrib M N P P' := by
  have hm := Measurable.of_comap_le hc.le
  have hf : AEMeasurable (fun ω => (⟨M ω, hMp ω⟩ : Subtype p)) P := hM.subtype_mk (hfs := hMp)
  have hg : AEMeasurable (fun ω => (⟨N ω, hNp ω⟩ : Subtype p)) P' := hN.subtype_mk (hfs := hNp)
  exact (identDistrib_of_code hf hg hc
    (identDistrib_of_pi_fdd (hm.comp_aemeasurable hf) (hm.comp_aemeasurable hg) h)).comp measurable_subtype_coe

end DOZZ.Proofs
