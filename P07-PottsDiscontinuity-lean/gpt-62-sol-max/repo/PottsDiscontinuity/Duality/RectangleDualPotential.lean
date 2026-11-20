/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleFlowDimension
public import PottsDiscontinuity.Duality.NormalizedPotentialSpace

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

section

variable
  (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))

noncomputable def rectangleDualConfiguration :
    Configuration (rectangleDualGraph a w h) :=
  Finset.map (rectangleDualGraphEdgeEquiv a w h).toEmbedding
    (rectangleDualComplementEquiv a w h A)

@[simp] theorem mem_rectangleDualConfiguration
    (e : RectangleDualEdgeCarrier a w h) :
    rectangleDualGraphEdgeEquiv a w h e ∈ rectangleDualConfiguration a w h A ↔
      e.primalEdge ∉ A := by
  classical
  simp [rectangleDualConfiguration]

private theorem mem_rectangleDualConfiguration_iff
    (g : (rectangleDualGraph a w h).edgeSet) :
    g ∈ rectangleDualConfiguration a w h A ↔
      ((rectangleDualGraphEdgeEquiv a w h).symm g).primalEdge ∉ A := by
  classical
  constructor
  · intro hg
    rcases Finset.mem_map.mp hg with ⟨e, he, hge⟩
    aesop
  · intro hg
    apply Finset.mem_map.mpr
    refine ⟨(rectangleDualGraphEdgeEquiv a w h).symm g, ?_, ?_⟩
    · simp_all
    simp

theorem rectangleDualOpen_adj_iff
    (u v : RectangleDualVertex a w h) :
    (openGraph (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A)).Adj u v ↔
      ∃ e : RectangleDualEdgeCarrier a w h,
        e.primalEdge ∉ A ∧ s(u,v) = rectangleDualCarrierPair a w h e := by
  rw [openGraph_adj, openEdges]
  constructor
  · intro hv
    change ∃ g : (rectangleDualGraph a w h).edgeSet,
      g ∈ rectangleDualConfiguration a w h A ∧ (g : Sym2 _) = s(u,v) at hv
    rcases hv with ⟨g, hg, hgv⟩
    let e := (rectangleDualGraphEdgeEquiv a w h).symm g
    refine ⟨e, ?_, ?_⟩
    · exact (mem_rectangleDualConfiguration_iff a w h A g).mp hg
    · have he : rectangleDualGraphEdgeEquiv a w h e = g := Equiv.apply_symm_apply _ _
      have hpair : (rectangleDualGraphEdgeEquiv a w h e : Sym2 _) =
          rectangleDualCarrierPair a w h e := rfl
      simp_all
  · rintro ⟨e, he, huv⟩
    change ∃ g : (rectangleDualGraph a w h).edgeSet,
      g ∈ rectangleDualConfiguration a w h A ∧ (g : Sym2 _) = s(u,v)
    refine ⟨rectangleDualGraphEdgeEquiv a w h e, ?_, ?_⟩
    · simp_all
    aesop

end

section

variable (a : LatticeVertex) (w h : ℕ)

def rectangleDualBaseVertex :
    RectangleDualVertex a w h :=
  ⟨(a.1 - 1, a.2 - 1), by
    rw [rectangleDualExpanded, mem_latticeRectangle]
    simp
    omega⟩

theorem rectangleDualBaseVertex_boundary :
    (rectangleDualBaseVertex a w h).1 ∈ rectangleDualBoundary a w h := by
  simp [rectangleDualBaseVertex, rectangleDualBoundary, rectangleDualInterior,
    rectangleDualExpanded, mem_latticeRectangle, Finset.mem_filter]
  omega

end

end PottsDiscontinuity.FK
