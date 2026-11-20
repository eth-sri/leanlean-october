module

public import RequestProject.TopologicalOrderCoverComparison
public import RequestProject.CoveringFibreComparison
public import RequestProject.OrderNerveRealizationRegular

@[expose] public section

/-! The reconstructed poset covering has exactly the original covering
space as its actual geometric realization. No connectedness assumption
is needed for this identification. Unverified source. -/

noncomputable section
namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Simplicial Topology
open scoped Classical
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p) (hs : Function.Surjective p)

include hs in
theorem realizedProjection_isCoveringMap : IsCoveringMap (realizedProjection p hp) :=
  (projection_isPosetCover p hp hs).realizationMap_isCoveringMap

variable (q : P)

include hs in
theorem realizedProjection_vertex_fibre
    (x : orderNerveRealization (Cover p hp))
    (hx : realizedProjection p hp x = orderNerveRealizationVertex q) :
    ∃ v : Cover p hp, v.1 = q ∧ x = orderNerveRealizationVertex v := by
  obtain ⟨v, hxv⟩ := orderNerveRealizationOpenStar_cover _ x
  have himg : realizedProjection p hp x ∈ orderNerveRealizationOpenStar P v.1 :=
    (orderNerveRealizationMap_mem_openStar_iff _
      _ x v.1).mpr ⟨v, rfl, hxv⟩
  have hvq : v.1 = q := by
    by_contra h
    have h' := Ne.symm h
    simp_all [orderNerveRealizationOpenStar, Set.mem_setOf_eq, orderNerveRealizationCoordinates_vertex, if_neg]
  refine ⟨v, hvq, (projection_isPosetCover p hp hs).realizationMap_injOn_openStar v hxv ?_ ?_⟩
  · simp [orderNerveRealizationOpenStar, orderNerveRealizationCoordinates_vertex]
  · change realizedProjection p hp x = orderNerveRealizationMap _ _ _
    rw [orderNerveRealizationMap_vertex (projection p hp) (projection_isPosetCover p hp hs).mono v, hx]
    exact (congrArg (orderNerveRealizationVertex (P := P)) hvq).symm

include hs in
theorem comparison_vertex_fibre_bijective :
    Function.Bijective
      (CoveringComparison.fibreMap (realizedProjection p hp) p
        (realizationComparison p hp) (realizationComparison_projection p hp)
        (orderNerveRealizationVertex q)) := by
  constructor
  · intro x y hxy
    obtain ⟨v, hv, hx⟩ := realizedProjection_vertex_fibre p hp hs q x.val x.property
    obtain ⟨w, hw, hy⟩ := realizedProjection_vertex_fibre p hp hs q y.val y.property
    have hpoint : point p hp v = point p hp w := by
      have h := congrArg Subtype.val hxy
      change realizationComparison p hp x.val = realizationComparison p hp y.val at h
      grind [realizationComparison_vertex]
    have hvw : v = w := by
      cases v with
      | mk a e =>
        cases w with
        | mk b e' =>
          dsimp at hv hw
          have hab := hv.trans hw.symm
          clear hv hw
          subst b
          refine Sigma.ext rfl ?_
          exact heq_of_eq (Subtype.ext hpoint)
    grind
  · intro e
    refine ⟨⟨orderNerveRealizationVertex (⟨q, e⟩), ?_⟩, ?_⟩
    · apply orderNerveRealizationMap_vertex
    · apply Subtype.ext
      apply realizationComparison_vertex

include hs in
theorem comparison_fibre_bijective (x : orderNerveRealization P) :
    Function.Bijective
      (CoveringComparison.fibreMap (realizedProjection p hp) p
        (realizationComparison p hp) (realizationComparison_projection p hp) x) := by
  obtain ⟨n, s, z, hz⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  have hj := orderNerveRealizationSimplex_joined_vertex s z 0
  rw [hz] at hj
  exact CoveringComparison.fibreMap_bijective_of_joined _ p
    (realizedProjection_isCoveringMap p hp hs) hp _
    _ hj
    (comparison_vertex_fibre_bijective p hp hs (s.obj 0))

def realizationHomeomorph :=
  CoveringComparison.homeomorphOfFibrewise _ p
    (realizedProjection_isCoveringMap p hp hs) hp _
    _ (comparison_fibre_bijective p hp hs)

end FiniteChains.Comb.TopologicalOrderCover
