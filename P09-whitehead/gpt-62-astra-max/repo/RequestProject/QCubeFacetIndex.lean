module

public import RequestProject.QCubeCanonicalTwoCycles


@[expose] public section

/-! Faithful indexing of the actual facets of a quotient cube. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

variable (c : QCube A)

def qCubeFacetIndex (i : {v : V // v ∈ c.spx} × ZMod 2) :=
  qCubeFacet c i.1.1 i.2

theorem qCubeFacetIndex_injective : Function.Injective (qCubeFacetIndex c) := by
  intro ⟨⟨v, hv⟩, s⟩ ⟨⟨w, hw⟩, t⟩ h
  have he : c.spx.erase v = c.spx.erase w := congrArg QCube.spx h
  have hvw : v = w := by
    by_contra hvw
    have hm := Finset.mem_erase.mpr ⟨hvw, hv⟩
    grind
  grind [qCubeFacetIndex, qCubeFacet_sgn_self]

variable (hc : c.spx.card = 3)

def qThreeFacetSquare
    (i : {v : V // v ∈ c.spx} × ZMod 2) : QSquare A :=
  ⟨qCubeFacetIndex c i, by
    change (c.spx.erase _).card = 2
    simp_all⟩

theorem qThreeFacetSquare_injective :
    Function.Injective (qThreeFacetSquare c hc) := by
  intro i j h
  exact qCubeFacetIndex_injective c (congrArg Subtype.val h)

end FiniteChains.Davis
