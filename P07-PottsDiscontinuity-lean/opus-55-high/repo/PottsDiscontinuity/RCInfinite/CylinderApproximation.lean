module

public import PottsDiscontinuity.RCInfinite.Cylinders
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Measure.Trim
public import PottsDiscontinuity.PottsThm.ColorNoiseMixing

public section

open MeasureTheory MeasurableSpace Set
open scoped symmDiff ENNReal

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- A cylinder whose finite support lies in the specified edge set. -/
def SupportedCylinder (E : Set Edge) (A : Set LatticeConfiguration) : Prop :=
  ∃ F : Finset Edge, (F : Set Edge) ⊆ E ∧ DependsOn (F : Set Edge) A

section
variable {E : Set Edge} {A : Set LatticeConfiguration} (h : SupportedCylinder E A)
include E A h
theorem SupportedCylinder.isCylinder  : IsCylinder A := by
  obtain ⟨F, _, hF⟩ := h
  tauto

theorem SupportedCylinder.compl  : SupportedCylinder E Aᶜ := by
  obtain ⟨F, hFE, hF⟩ := h
  exact ⟨F, hFE, hF.compl⟩
end

theorem SupportedCylinder.union {E : Set Edge} {A B : Set LatticeConfiguration}
    (hA : SupportedCylinder E A) (hB : SupportedCylinder E B) : SupportedCylinder E (A ∪ B) := by
  obtain ⟨F, hFE, hF⟩ := hA
  obtain ⟨G, hGE, hG⟩ := hB
  refine ⟨F ∪ G, ?_, ?_⟩
  · simp_all
  · intro ω η hω
    exact or_congr (hF ω η (fun e he => hω e (by simp [he])))
      (hG ω η (fun e he => hω e (by simp [he])))

section
variable (E : Set Edge)
theorem supportedCylinder_isSetAlgebra  :
    IsSetAlgebra {A | SupportedCylinder E A} where
  empty_mem := ⟨∅, by simp, fun _ _ _ => Iff.rfl⟩
  compl_mem := fun {_} h => h.compl
  union_mem := fun {_ _} hA hB => hA.union hB

/-- The sigma algebra of events which read only edges in `E`. -/
abbrev edgeSigma  : MeasurableSpace LatticeConfiguration :=
  generateFrom {A | SupportedCylinder E A}

theorem edgeSigma_le  :
    edgeSigma E ≤ (MeasurableSpace.pi : MeasurableSpace LatticeConfiguration) :=
  generateFrom_le fun _ h => h.isCylinder.measurableSet

def edgeProjection (ω : LatticeConfiguration) : LatticeConfiguration :=
  fun e => if e ∈ E then ω e else false

theorem edgeProjection_measurable  :
    @Measurable LatticeConfiguration LatticeConfiguration (edgeSigma E) inferInstance
      (edgeProjection E) := by
  let  := edgeSigma E
  apply measurable_pi_iff.mpr
  intro e
  by_cases he : e ∈ E
  · have hcoord : @Measurable LatticeConfiguration Bool (edgeSigma E) inferInstance
        (fun ω => ω e) := by
      apply measurable_to_bool
      apply MeasurableSpace.measurableSet_generateFrom
      refine ⟨{e}, ?_, ?_⟩
      · simp_all
      · intro ω η hω
        simp_all
    simp_all [edgeProjection]
  simp_all [edgeProjection, LatticeConfiguration]
end

theorem DependsOn.measurable_edgeSigma {E : Set Edge} {A : Set LatticeConfiguration}
    (hdep : DependsOn E A) (hA : MeasurableSet A) : MeasurableSet[edgeSigma E] A := by
  have heq : A = edgeProjection E ⁻¹' A := by
    ext ω
    exact hdep ω (edgeProjection E ω) (by
      simp_all [edgeProjection])
  rw [heq]
  exact edgeProjection_measurable E hA

section
variable (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
include μ
/-- Approximation can preserve an arbitrary allowed set of coordinates. In
particular, an event independent of one edge admits independent cylinders as
approximants. -/
theorem exists_supportedCylinder_approx (E : Set Edge) {A : Set LatticeConfiguration} (hA : MeasurableSet A)
    (hdep : DependsOn E A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C, SupportedCylinder E C ∧ μ (C ∆ A) < ε := by
  have hAE := hdep.measurable_edgeSigma hA
  have hcover : ∃ D : Set (Set LatticeConfiguration), D.Countable ∧
      D ⊆ {C | SupportedCylinder E C} ∧ (μ.trim (edgeSigma_le E)) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, Set.countable_singleton _, ?_, by simp⟩
    intro C hC
    subst C
    exact (supportedCylinder_isSetAlgebra E).univ_mem
  obtain ⟨C, hC, hCA⟩ := @exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    LatticeConfiguration (edgeSigma E) (μ.trim (edgeSigma_le E)) inferInstance
    {C | SupportedCylinder E C} (supportedCylinder_isSetAlgebra E).isSetRing
    hcover rfl A hAE ε hε
  refine ⟨C, hC, ?_⟩
  have hCE := MeasurableSpace.measurableSet_generateFrom hC
  rwa [trim_measurableSet_eq (edgeSigma_le E) (hCE.symmDiff hAE)] at hCA

theorem exists_cylinder_approx {A : Set LatticeConfiguration} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, IsCylinder C ∧ μ.real (C ∆ A) < ε := by
  obtain ⟨C, hC, hCA⟩ := exists_supportedCylinder_approx μ univ hA
    (fun ω η hω => by
      have hh : ω = η := by grind
      simp_all) (ENNReal.ofReal_pos.mpr hε)
  refine ⟨C, hC.isCylinder, ?_⟩
  simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using ((ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hCA)
end

end
end PottsDiscontinuity.RCInfinite
