import RequestProject.OrderNerveCoverLiftGluing
import RequestProject.Tac


/-! The actual continuous comparison from the reconstructed poset cover
to the given covering space, commuting with the projection. Unverified. -/

noncomputable section
bwd

namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Simplicial Topology
open scoped Classical
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)

def realizedProjection : C(orderNerveRealization (Cover p hp), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap (projection p hp) (projection_monotone p hp),
    (orderNerveRealizationMap _ (projection_monotone p hp)).hom.continuous⟩

def starProjection v :
    orderNerveVertexStar (Cover p hp) v → orderNerveVertexStar P v.1 :=
  fun w => projectedComparable p hp v w.val w.property

theorem starProjection_monotone v : Monotone (starProjection p hp v) :=
  fun _ _ h => projection_monotone p hp h

def localComparison v :=
  (starLift p hp v).comp
    ⟨orderNerveRealizationMap (starProjection p hp v) (starProjection_monotone p hp v),
      (orderNerveRealizationMap _
        (starProjection_monotone p hp v)).hom.continuous⟩

theorem localComparison_projection v
    z :
    p (localComparison p hp v z) = realizedProjection p hp
      (orderNervePieceMap (orderNerveVertexStar (Cover p hp)) v z) := by
  rwd [starLift_projection]
  rwd [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  rfl

theorem localComparison_vertex v
    w :
    localComparison p hp v (orderNerveRealizationVertex w) = point p hp w.val := by
  change starLift p hp v (orderNerveRealizationMap _ _ _) = _
  rwd [orderNerveRealizationMap_vertex]
  exact starLift_vertex p hp v w.val w.property

theorem vertexStars_cover_simplices S [PartialOrder S]
    n (s : (nerve S).obj (Opposite.op n)) :
    ∃ v, ∀ i, s.obj i ∈ orderNerveVertexStar S v := by
  refine ⟨s.obj 0, fun i => Or.inr ?_⟩
  exact leOfHom (s.map (homOfLE i.zero_le))

def realizationComparison :=
  orderNerveCoverLift p hp _
    _ _ _
    (localComparison_projection p hp) (localComparison_vertex p hp)
    (vertexStars_cover_simplices _)

theorem realizationComparison_projection x :
    p (realizationComparison p hp x) = realizedProjection p hp x :=
  orderNerveCoverLift_projection p hp _ _ _ _ _ _ _ x

theorem realizationComparison_vertex v :
    realizationComparison p hp (orderNerveRealizationVertex v) = point p hp v := by
  let w : orderNerveVertexStar (Cover p hp) v := ⟨v, Or.inl le_rfl⟩
  have he : orderNervePieceMap _ v
      (orderNerveRealizationVertex w) = orderNerveRealizationVertex v :=
    orderNerveRealizationMap_vertex _ _ w
  rwd [← he]
  rwd [orderNerveCoverLift_piece]
  exact localComparison_vertex p hp v w
