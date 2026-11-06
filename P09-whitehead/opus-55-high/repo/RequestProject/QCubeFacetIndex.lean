import RequestProject.QCubeCanonicalTwoCycles
import RequestProject.QCubeImmediateFaces


/-! Faithful indexing of the actual facets of a quotient cube. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def qCubeFacetIndex (c : QCube A) (i : {v : V // v ∈ c.spx} × ZMod 2) :=
  qCubeFacet c i.1.1 i.2

theorem qCubeFacetIndex_injective (c : QCube A) : Function.Injective (qCubeFacetIndex c) := by
  intro ⟨⟨v, hv⟩, s⟩ ⟨⟨w, hw⟩, t⟩ h
  have he : c.spx.erase v = c.spx.erase w := congrArg QCube.spx h
  have hvw : v = w := by
    by_contra hvw
    have hm : v ∈ c.spx.erase w := by simp_all
    grind
  grind [qCubeFacetIndex, qCubeFacet_sgn_self]

def qThreeFacetSquare (c : QCube A) (hc : c.spx.card = 3)
    (i : {v : V // v ∈ c.spx} × ZMod 2) : QSquare A :=
  ⟨qCubeFacetIndex c i, by
    change (c.spx.erase i.1.1).card = 2
    simp_all⟩

theorem qThreeFacetSquare_injective (c : QCube A) hc :
    Function.Injective (qThreeFacetSquare c hc) := by
  intro i j h
  exact qCubeFacetIndex_injective c (congrArg Subtype.val h)
