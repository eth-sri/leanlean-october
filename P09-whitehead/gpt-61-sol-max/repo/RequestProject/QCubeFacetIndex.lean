import Mathlib.Tactic

import RequestProject.QCubeCanonicalTwoCycles
import RequestProject.QCubeImmediateFaces

/-! Faithful indexing of the actual facets of a quotient cube. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

  (c : QCube A)
def qCubeFacetIndex  (i : {v : V // v ∈ c.spx} × ZMod 2)  :=
  qCubeFacet c i.1.1 i.2

theorem qCubeFacetIndex_injective  : Function.Injective (qCubeFacetIndex c) := by
  intro ⟨⟨v, hv⟩, s⟩ ⟨⟨w, hw⟩, t⟩ h
  have he : c.spx.erase v = c.spx.erase w := congrArg QCube.spx h
  have hvw : v = w := by
    classical grind [Finset.notMem_erase]
  subst w
  have hst := congrArg (fun d : QCube A => d.sgn v) h
  simp only [qCubeFacetIndex, qCubeFacet_sgn_self] at hst
  exact Prod.ext (Subtype.ext rfl) hst

def qThreeFacetSquare  (hc : c.spx.card = 3)
    (i : {v : V // v ∈ c.spx} × ZMod 2) : QSquare A :=
  ⟨qCubeFacetIndex c i, by
    change (c.spx.erase i.1.1).card = 2
    rw [Finset.card_erase_of_mem i.1.2, hc]⟩

theorem qThreeFacetSquare_injective  (hc : c.spx.card = 3) :
    Function.Injective (qThreeFacetSquare c hc) := by
  intro i j h
  exact qCubeFacetIndex_injective c (congrArg Subtype.val h)

end FiniteChains.Davis
