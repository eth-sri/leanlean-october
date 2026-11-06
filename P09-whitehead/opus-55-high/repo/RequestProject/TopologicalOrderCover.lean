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

def fibreFunctor :=
  orderNerveRealizationFundamentalFunctor P ⋙ hp.monodromyFunctor

abbrev Cover := LocalSystem.Cover (fibreFunctor p hp)
def projection : Cover p hp → P := LocalSystem.projection _

theorem projection_monotone : Monotone (projection p hp) :=
  LocalSystem.projection_monotone _

def point (v : Cover p hp) := v.2.val

theorem point_projection v : p (point p hp v) = orderNerveRealizationVertex v.1 :=
  v.2.property

theorem fibreFunctor_map_bijective (h : a ≤ b) :
    Function.Bijective ((fibreFunctor p hp).map (homOfLE h)) :=
  hp.monodromy_bijective (Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath h))

theorem projection_isPosetCover (hs : Function.Surjective p) : IsPosetCover (projection p hp) := by
  apply LocalSystem.projection_isPosetCover _
  · exact (fibreFunctor_map_bijective p hp)
  · intro a
    cases' hs _ with x hx
    tauto

/-- The defining incidence square retains the actual covering lift. -/
theorem comparable_transport {v w : Cover p hp} (h : v ≤ w) :
    hp.monodromy (Path.Homotopic.Quotient.mk
      (orderNerveRealizationEdgePath h.choose)) v.2 = w.2 := h.choose_spec
