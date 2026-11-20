module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

section

/-!
# Shared Euclidean sphere type

The definition is moved verbatim from NonmanifoldFinal/SphereCoordinates, with
unchanged namespace and type. It allows homology of ordinary balls and spheres
to be checked without importing the GS normalization/local-model construction.
-/
open scoped BigOperators

namespace GS.NonmanifoldFinal

abbrev UnitSphere (κ : Type*) [Fintype κ] :=
  {x : EuclideanSpace ℝ κ // x ∈ Metric.sphere 0 1}

end GS.NonmanifoldFinal

end

section

/-!
# A continuous section/retraction pair

The structure is moved verbatim from NonmanifoldObstruction/PuncturedNeighbourhood.
This separates the elementary homology-functor check from the matrix
geometry imports. Its namespace, fields, and mathematical meaning are unchanged.
-/
namespace GS.NonmanifoldObstruction

structure ContinuousSectionPair (A B : Type*) [TopologicalSpace A]
    [TopologicalSpace B] where
  sectionMap : C(A, B)
  retractionMap : C(B, A)
  retraction_section : ∀ a, retractionMap (sectionMap a) = a

end GS.NonmanifoldObstruction

end

section

/-!
# Transport the existing sphere retract to all finite column sets

The d+2 convention of the old section is eliminated by an explicit equivalence.
The resulting retract has a genuine Fin-indexed Euclidean sphere as its source.
-/
open GS GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

def transportSectionPair {A B B' : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace B'] (p : ContinuousSectionPair A B) (h : B ≃ₜ B') : ContinuousSectionPair A B' :=
  ⟨(h : C(B, B')).comp p.sectionMap, p.retractionMap.comp h.symm,
    fun x => by simp [p.retraction_section]⟩

/-- Remove a SINGLE marked point from an open subset. -/
abbrev PuncturedIn {X : Type*} (U : Set X) (x : X) := {p : X // p ∈ U ∧ p ≠ x}

end GS.NonmanifoldFinal

end
