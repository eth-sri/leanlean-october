import Mathlib.Tactic

import RequestProject.LocalSystemPosetCover
import RequestProject.OrderNerveRealizationFundamental
import Mathlib.Topology.Homotopy.Lifting

/-! Recover an actual poset cover from a genuine topological cover of an
order realization. Its vertices are actual points above the original
vertices, and incidence is the endpoint of genuine path lifting.
Unverified source. -/

noncomputable section
namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Topology
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)

def fibreFunctor : P ⥤ Type :=
  orderNerveRealizationFundamentalFunctor P ⋙ hp.monodromyFunctor

abbrev Cover := LocalSystem.Cover (fibreFunctor p hp)
def projection  := LocalSystem.projection (fibreFunctor p hp)

abbrev projection_monotone  :=
  FiniteChains.Comb.LocalSystem.projection_monotone (FiniteChains.Comb.TopologicalOrderCover.fibreFunctor p hp)

def point (v : Cover p hp)  := v.2.val

abbrev point_projection (v : Cover p hp)  :=
  v.snd.property

abbrev fibreFunctor_map_bijective {a b : P} (h : a ≤ b)  :=
  hp.monodromy_bijective (Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath h))

theorem projection_isPosetCover (hs : Function.Surjective p) : IsPosetCover (projection p hp) := by
  apply LocalSystem.projection_isPosetCover (fibreFunctor p hp)
  · exact fun h => fibreFunctor_map_bijective p hp h
  · intro a
    obtain ⟨x, hx⟩ := hs (orderNerveRealizationVertex a)
    exact ⟨⟨x, hx⟩⟩

/-- The defining incidence square retains the actual covering lift. -/
abbrev comparable_transport {v w : Cover p hp} (h : v ≤ w)  := h.choose_spec

end FiniteChains.Comb.TopologicalOrderCover
