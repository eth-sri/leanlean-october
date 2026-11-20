module

public import RequestProject.VertexPunctureAcyclic
public import RequestProject.PositiveBoundaryCoordinates
public import RequestProject.NerveOrderHomotopy

@[expose] public section

/-! Actual augmented fillings on the boundary after its cut facet is removed. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

theorem positiveRetainedBoundary_acyclic (t : QOld A)
    (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    ∀ c ∈ Inc (RetainedProperBoundary t), Nerve.bdry c = 0 →
      ∃ y ∈ Inc (RetainedProperBoundary t), Nerve.bdry y = c :=
  exists_bdry_eq_of_cycle_of_orderIso
    (positiveBoundaryOrderIso t ht (positiveThreeCubeCoordinates t hcard))
    vertexPuncturedCube_acyclic

/-- The order homotopy to the retained proper faces supplies the missing prism. -/
theorem positiveCutPuncturedBoundary_acyclic (t : QOld A)
    (hne : t.1.spx.Nonempty) (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    ∀ c ∈ Inc (CutPuncturedBoundary t hne), Nerve.bdry c = 0 →
      ∃ y ∈ Inc (CutPuncturedBoundary t hne), Nerve.bdry y = c := by
  intro c hc hcyc
  refine boundary_reflection_of_section _ _ (cutBoundaryRetraction_monotone t hne)
    (cutBoundarySection_monotone t hne) (Or.inl (cutBoundary_le_section_retraction t hne)) c hc hcyc ?_
  exact positiveRetainedBoundary_acyclic t ht hcard _
    (cmap_mem_inc_of_monotone (cutBoundaryRetraction_monotone t hne) hc)
    (by rw [← cmap_bdry, hcyc, map_zero])

end FiniteChains.Davis
