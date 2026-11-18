module

public import GS.Topology.SectionPair

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

noncomputable section
open GS GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

variable {A A' B B' X : Type*}
  [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B]
  [TopologicalSpace B'] [TopologicalSpace X]

def transportSectionPair (p : ContinuousSectionPair A B)
    (hA : A' ≃ₜ A) (hB : B ≃ₜ B') : ContinuousSectionPair A' B' where
  sectionMap a := hB (p.sectionMap (hA a))
  retractionMap b := hA.symm (p.retractionMap (hB.symm b))
  section_continuous := hB.continuous.comp (p.section_continuous.comp hA.continuous)
  retraction_continuous := hA.symm.continuous.comp (p.retraction_continuous.comp hB.symm.continuous)
  retraction_section a := by simp only [Homeomorph.symm_apply_apply, p.retraction_section]

abbrev PuncturedIn (U : Set X) (x : X) := {p : X // p ∈ U ∧ p ≠ x}

end GS.NonmanifoldFinal
