import Mathlib.Tactic

import RequestProject.OrderNerveCoverLiftGluing

/-! The actual continuous comparison from the reconstructed poset cover
to the given covering space, commuting with the projection. Unverified. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Simplicial Topology

variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)

def realizedProjection : C(orderNerveRealization (Cover p hp), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap (projection p hp) (projection_monotone p hp),
    (orderNerveRealizationMap (projection p hp) (projection_monotone p hp)).hom.continuous⟩

variable (v : Cover p hp)
def starProjection  :
    orderNerveVertexStar (Cover p hp) v → orderNerveVertexStar P v.1 :=
  fun w => projectedComparable p hp v w.val w.property

theorem starProjection_monotone  : Monotone (starProjection p hp v) :=
  fun _ _ h => projection_monotone p hp h

def localComparison   :=
  (starLift p hp v).comp
    ⟨orderNerveRealizationMap (starProjection p hp v) (starProjection_monotone p hp v),
      (orderNerveRealizationMap (starProjection p hp v)
        (starProjection_monotone p hp v)).hom.continuous⟩

theorem localComparison_projection 
    (z : orderNerveRealization (orderNerveVertexStar (Cover p hp) v)) :
    p (localComparison p hp v z) = realizedProjection p hp
      (orderNervePieceMap (orderNerveVertexStar (Cover p hp)) v z) := by
  
  rw (config := { transparency := .default }) [starLift_projection]
  
  rw (config := { transparency := .default }) [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  rfl

theorem localComparison_vertex 
    (w : orderNerveVertexStar (Cover p hp) v) :
    localComparison p hp v (orderNerveRealizationVertex w) = point p hp w.val := by
  change starLift p hp v (orderNerveRealizationMap _ _ _) = _
  rw (config := { transparency := .default }) [orderNerveRealizationMap_vertex]
  exact starLift_vertex p hp v w.val w.property

theorem vertexStars_cover_simplices (S : Type) [PartialOrder S]
    (n : SimplexCategory) (s : (nerve S).obj (Opposite.op n)) :
    ∃ v, ∀ i, s.obj i ∈ orderNerveVertexStar S v := by
  refine ⟨s.obj 0, fun i => Or.inr ?_⟩
  exact leOfHom (s.map (homOfLE (Fin.zero_le i)))

def realizationComparison  :=
  orderNerveCoverLift p hp (orderNerveVertexStar (Cover p hp))
    (realizedProjection p hp) (localComparison p hp) (point p hp)
    (localComparison_projection p hp) (localComparison_vertex p hp)
    (vertexStars_cover_simplices (Cover p hp))

theorem realizationComparison_projection (x : orderNerveRealization (Cover p hp)) :
    p (realizationComparison p hp x) = realizedProjection p hp x :=
  orderNerveCoverLift_projection p hp _ _ _ _ _ _ _ x

theorem realizationComparison_vertex  :
    realizationComparison p hp (orderNerveRealizationVertex v) = point p hp v := by
  let w : orderNerveVertexStar (Cover p hp) v := ⟨v, Or.inl le_rfl⟩
  have he : orderNervePieceMap (orderNerveVertexStar (Cover p hp)) v
      (orderNerveRealizationVertex w) = orderNerveRealizationVertex v :=
    orderNerveRealizationMap_vertex _ _ w
  rw  [← he]
  change orderNerveCoverLift p hp _ _ _ _ _ _ _ _ = _
  rw  [orderNerveCoverLift_piece]
  exact localComparison_vertex p hp v w

end FiniteChains.Comb.TopologicalOrderCover
