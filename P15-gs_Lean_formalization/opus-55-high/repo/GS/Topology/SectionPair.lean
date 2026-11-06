module

public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section



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
