module

public import RequestProject.TopologicalOrderCoverStarVertices
public import RequestProject.OrderNerveRealizationCover

@[expose] public section

/-! Covering-space lifts on induced subposets glue from their vertex values.
The gluing uses the realization quotient topology, with no finiteness
assumption on the family. Unverified source. -/

noncomputable section

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

variable {S : Type} [PartialOrder S] {X E : Type}
  [TopologicalSpace X] [TopologicalSpace E]
  (p : C(E, X)) (hp : IsCoveringMap p)
  {J : Type} (A : J → Set S) (F : C(orderNerveRealization S, X))
  (l : ∀ j, C(orderNerveRealization (A j), E)) (v : S → E)
  (hl : ∀ j z, p (l j z) = F (orderNervePieceMap A j z))
  (hv : ∀ j (a : A j), l j (orderNerveRealizationVertex a) = v a.val)

include hp hl hv in
theorem orderNerveCoverLifts_agree (j k : J)
    (z : orderNerveRealization (A j)) (w : orderNerveRealization (A k))
    (he : orderNervePieceMap A j z = orderNervePieceMap A k w) : l j z = l k w := by
  let B := A j ∩ A k
  let bj : B → A j := fun b => ⟨b.val, b.property.1⟩
  let bk : B → A k := fun b => ⟨b.val, b.property.2⟩
  have hj : Monotone bj := fun _ _ h => h
  have hk : Monotone bk := fun _ _ h => h
  have hz : orderNervePieceMap A j z ∈ orderNerveRealizationSupported S B := by
    erw [orderNerveRealizationSupported_inter]
    constructor
    · exact (orderNerveRealizationSubtypeHomeomorph _ z).property
    · erw [he]
      exact (orderNerveRealizationSubtypeHomeomorph _ w).property
  let t := (orderNerveRealizationSubtypeHomeomorph B).symm
    ⟨orderNervePieceMap A j z, hz⟩
  have ht : orderNerveRealizationMap Subtype.val _ t =
      orderNervePieceMap A j z := congrArg Subtype.val ((orderNerveRealizationSubtypeHomeomorph B).apply_symm_apply _)
  have htj : orderNerveRealizationMap bj hj t = z := by
    apply orderNerveRealizationMap_injective Subtype.val
      (fun _ _ h => h) Subtype.val_injective
    erw [orderNerveRealizationMap_comp] <;> assumption
  have htk : orderNerveRealizationMap bk hk t = w := by
    apply orderNerveRealizationMap_injective Subtype.val
      (fun _ _ h => h) Subtype.val_injective
    erw [orderNerveRealizationMap_comp]
    exact ht.trans he
  obtain ⟨n, s, r, hr⟩ := orderNerveRealizationSimplex_jointly_surjective B t
  let f := fun a =>
    l j (orderNerveRealizationMap bj hj (orderNerveRealizationSimplex B s a))
  let g := fun a =>
    l k (orderNerveRealizationMap bk hk (orderNerveRealizationSimplex B s a))
  have hf : Continuous f := (l j).continuous.comp
    ((orderNerveRealizationMap bj hj).hom.continuous.comp
      (orderNerveRealizationSimplex B s).hom.continuous)
  have hg : Continuous g := (l k).continuous.comp
    ((orderNerveRealizationMap bk hk).hom.continuous.comp
      (orderNerveRealizationSimplex B s).hom.continuous)
  have hfg : p ∘ f = p ∘ g := by
    funext a
    dsimp [f, g]
    erw [hl, hl]
    erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]; rfl
  obtain ⟨a, ha⟩ := orderNerveRealizationVertex_mem_simplex s 0
  have hbase : f a = g a := by
    have hleft :=
      (congrArg (fun u : orderNerveRealization B => l j _) ha).trans
        ((congrArg (l j) (orderNerveRealizationMap_vertex bj hj (s.obj 0))).trans (hv j (bj (s.obj 0))))
    have hright :=
      (congrArg (fun u : orderNerveRealization B => l k _) ha).trans
        ((congrArg (l k) (orderNerveRealizationMap_vertex bk hk (s.obj 0))).trans (hv k (bk (s.obj 0))))
    exact hleft.trans hright.symm
  simpa only [f, g, hr, htj, htk] using (congrFun (hp.eq_of_comp_eq hf hg hfg a hbase) r)

variable (hc : ∀ (n : SimplexCategory) (s : (nerve S).obj (Opposite.op n)),
  ∃ j, ∀ i, s.obj i ∈ A j)

def coverLiftValue (x : orderNerveRealization S) :=
  let y := (orderNervePieceQuotient_surjective A hc x).choose
  l y.1 y.2

include hp hl hv in
theorem coverLiftValue_piece (j : J) (z : orderNerveRealization (A j)) :
    coverLiftValue A l hc (orderNervePieceMap A j z) = l j z := by
  let y := (orderNervePieceQuotient_surjective A hc (orderNervePieceMap A j z)).choose
  apply orderNerveCoverLifts_agree p hp A F l v hl hv y.1 j y.2 z
  exact (orderNervePieceQuotient_surjective A hc _).choose_spec

def orderNerveCoverLift : C(orderNerveRealization S, E) where
  toFun := coverLiftValue A l hc
  continuous_toFun := by
    apply (orderNervePieceQuotient_isQuotientMap A hc).continuous_iff.mpr
    have he : coverLiftValue A l hc ∘ orderNervePieceQuotient A =
        fun y => l y.1 y.2 := by
      funext y
      solve_by_elim [coverLiftValue_piece]
    erw [he]
    exact continuous_sigma (fun j => (l j).continuous)

theorem orderNerveCoverLift_piece (j : J) (z : orderNerveRealization (A j)) :
    orderNerveCoverLift p hp A F l v hl hv hc (orderNervePieceMap A j z) = l j z :=
  by solve_by_elim [coverLiftValue_piece]

theorem orderNerveCoverLift_projection (x : orderNerveRealization S) :
    p (orderNerveCoverLift p hp A F l v hl hv hc x) = F x := by
  obtain ⟨⟨j, z⟩, rfl⟩ := orderNervePieceQuotient_surjective A hc x
  erw [show orderNervePieceQuotient A _ = orderNervePieceMap A j z from rfl,
    orderNerveCoverLift_piece] <;> grind

end FiniteChains.Comb
