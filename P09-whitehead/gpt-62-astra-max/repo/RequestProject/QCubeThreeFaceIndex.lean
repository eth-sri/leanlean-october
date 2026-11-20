module

public import RequestProject.QCubeDoubleFacetIndex
public import RequestProject.QCubeCubicalTwoBoundary

@[expose] public section

/-! The six square facets of a three-cell. -/
noncomputable section
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

variable (c : QThreeCube A)

def qThreeFaceSquare (i : Fin 3 × ZMod 2) := qThreeFacetSquare c.1 c.2 (c.dirs i.1, i.2)

theorem qThreeFaceSquare_injective : Function.Injective (qThreeFaceSquare c) :=
  (qThreeFacetSquare_injective c.1 c.2).comp (c.dirs.prodCongr (Equiv.refl _)).injective

theorem qThreeFaceSquare_exhaustive (s : QSquare A) (h : s.1 < c.1) :
    ∃ i, qThreeFaceSquare c i = s := by
  obtain ⟨v, hv, he⟩ := exists_qCube_facet_of_card s.1 c.1 h.le (by have := s.2; have := c.2; omega)
  obtain ⟨i, hi⟩ := c.dirs.surjective ⟨v, hv⟩
  exact ⟨(i, s.1.sgn v), Subtype.ext (by change qCubeFacet c.1 (c.dirs i).1 (s.1.sgn v) = s.1; rw [hi]; exact he.symm)⟩

end FiniteChains.Davis
