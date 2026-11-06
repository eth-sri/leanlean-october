import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Homeomorph.Lemmas

import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Defs



/-!
# A continuous section/retraction pair

The structure is moved verbatim from NonmanifoldObstruction/PuncturedNeighbourhood.
This separates the elementary homology-functor check from the matrix
geometry imports. Its namespace, fields, and mathematical meaning are unchanged.
-/
namespace GS.NonmanifoldObstruction

structure ContinuousSectionPair (A B : Type*) [TopologicalSpace A]
    [TopologicalSpace B] where
  sectionMap : A → B
  retractionMap : B → A
  section_continuous : Continuous sectionMap
  retraction_continuous : Continuous retractionMap
  retraction_section : ∀ a, retractionMap (sectionMap a) = a

end GS.NonmanifoldObstruction

namespace GS.NonmanifoldFinal
open GS.NonmanifoldObstruction
variable {A A' B B' X Y : Type*}
  [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B]
  [TopologicalSpace B'] [TopologicalSpace X] [TopologicalSpace Y]

/-- Transport BOTH maps, including the left-inverse identity. -/
def transportSectionPair (p : ContinuousSectionPair A B)
    (hA : A' ≃ₜ A) (hB : B ≃ₜ B') : ContinuousSectionPair A' B' where
  sectionMap a := hB (p.sectionMap (hA a))
  retractionMap b := hA.symm (p.retractionMap (hB.symm b))
  section_continuous := hB.continuous.comp (p.section_continuous.comp hA.continuous)
  retraction_continuous := hA.symm.continuous.comp
    (p.retraction_continuous.comp hB.symm.continuous)
  retraction_section a := by simp only [Homeomorph.symm_apply_apply,
    p.retraction_section]

/-- Remove a SINGLE marked point from an open subset. -/
abbrev PuncturedIn (U : Set X) (x : X) := {p : X // p ∈ U ∧ p ≠ x}

def puncturedImage (h : X ≃ₜ Y) (U : Set X) (x : X) :
    PuncturedIn U x ≃ₜ PuncturedIn (h '' U) (h x) :=
  h.subtype (fun a => by continuity)

end GS.NonmanifoldFinal
