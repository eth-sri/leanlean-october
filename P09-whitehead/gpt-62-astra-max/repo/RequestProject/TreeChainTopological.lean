module

public import RequestProject.TreeUnivCoverIso
public import RequestProject.TreeChain

@[expose] public section

/-!
# `(1) ⇒ (2)` of Theorem A for chains of arbitrary two-complexes, topologically

`RequestProject/TreeChain.lean` proves `(1) ⇒ (2)` of Theorem A for chains of arbitrary finite
two-complexes, but with the hypothesis "the inclusion is zero on `π₂`" read *after* collapsing
compatible spanning trees.  `RequestProject/TreeUnivCoverIso.lean` shows that collapsing a
spanning tree does not change `π₂`.  Putting the two together removes the collapse from the
hypothesis:

* `FiniteChains.Comb.SpanningTree.zeroPi2_presInclHom_of_zeroPi2` — **if a subcomplex inclusion
  is zero on `π₂`, so is the induced inclusion of the collapsed presentation complexes**;
* `FiniteChains.Comb.SpanningTree.ComplexChainTop` — a chain `K ⊂ X₀ ⊂ ⋯ ⊂ Xₙ` of two-complexes
  with compatible spanning trees, whose inclusions are zero on `π₂` in the sense of the
  interface of Theorem A (`FiniteChains.Comb.ZeroPi2`);
* `FiniteChains.Comb.SpanningTree.hasAcyclicRegularCover_of_topComplexChains` — such chains of
  every length give a connected acyclic regular cover of `K`;
* `FiniteChains.Comb.TopChain` and
  `FiniteChains.Comb.hasAcyclicRegularCover_of_topChains_of_isConnected` — the same statement
  with no mention of spanning trees at all: **a finite connected two-complex which begins
  chains of every finite length of finite connected two-complexes, each inclusion being zero on
  `π₂`, has a connected acyclic regular cover.**
-/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

/-! ### Naturality of the identification of the two models -/

section Naturality

variable {X Y : Complex2.{u}} {TX : SpanningTree X} {TY : SpanningTree Y}
variable [Fintype (NonTree TX)] [DecidableEq (NonTree TX)] [Fintype X.F] [DecidableEq X.F]
variable [Fintype (NonTree TY)] [DecidableEq (NonTree TY)] [Fintype Y.F] [DecidableEq Y.F]
variable {h : Hom X Y} (hiff : ∀ e : X.E, TY.isTree (h.onE e) ↔ TX.isTree e)

omit [Fintype (NonTree TX)] [DecidableEq (NonTree TX)] [Fintype X.F] [DecidableEq X.F]
  [Fintype (NonTree TY)] [DecidableEq (NonTree TY)] [Fintype Y.F] [DecidableEq Y.F] in
/-- The element of `π₁` spelled by the image of a path is the image of the element spelled by
the path. -/
theorem uvQ_univLiftV {x₀ : X.V} (c : UV X x₀) :
    uvQ (univLiftV x₀ h c)
      = presInclGroupHom _ _ _ h.onF
          (treeRel_onF hiff) (uvQ (T := TX) c) := by
  induction c using UV.ind with
  | h p =>
      show QuotientGroup.mk (pathWord TY (mapPath h p.1)) = _; rw [pathWord_mapPath hiff]; rfl

variable (hE : Function.Injective h.onE)

variable {x₀ : X.V}

omit [Fintype (NonTree TX)] [Fintype X.F] [DecidableEq X.F] [Fintype (NonTree TY)]
  [Fintype Y.F] [DecidableEq Y.F] in
/-- The identification of the two models of the universal cover is natural in a subcomplex
inclusion: on two-cells it carries the lift of the inclusion to the inclusion of the universal
covers of the collapsed presentation complexes. -/
theorem uvFace_univLiftF (F : UF X x₀) :
    uvFace TY (univLiftF x₀ h F)
      = (univCoverInclHom _ (nonTreeIncl_injective hiff hE) _
          _ h.onF (treeRel_onF hiff)).onF (uvFace TX F) := by
  show ((uvQ _, h.onF _))
    = Prod.map _ h.onF (uvQ (T := TX) F.1.1, F.1.2)
  solve_by_elim [uvQ_univLiftV]

omit [Fintype (NonTree TX)] [Fintype X.F] [DecidableEq X.F] [Fintype (NonTree TY)]
  [Fintype Y.F] [DecidableEq Y.F] in
/-- The square of two-chains commutes. -/
theorem chain2_treeUnivHom_square
    (u : (uCover X x₀).F →₀ ℤ) :
    chain2 (treeUnivHom TY (h.onV x₀)) (chain2 (univLift X h x₀) u)
      = chain2 (univCoverInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE)
          (treeRel TX) (treeRel TY) h.onF (treeRel_onF hiff)) (chain2 (treeUnivHom TX x₀) u) := by
  classical
  show Finsupp.mapDomain _ (Finsupp.mapDomain _ u)
    = Finsupp.mapDomain _ (Finsupp.mapDomain _ u)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  refine congrArg (fun k => Finsupp.mapDomain k u) ?_
  funext F
  apply uvFace_univLiftF <;> assumption

omit [Fintype (NonTree TX)] [Fintype X.F] [DecidableEq X.F] [Fintype (NonTree TY)] [Fintype Y.F] [DecidableEq Y.F] in
/-- **If a subcomplex inclusion is zero on `π₂`, so is the induced inclusion of the collapsed
presentation complexes.**  This is the dictionary that turns the topological form of condition
(1) of Theorem A into the algebraic one used in Section 2 of the paper. -/
theorem zeroPi2_presInclHom_of_zeroPi2 (hzero : ZeroPi2 h) :
    ZeroPi2 (presInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE) (treeRel TX)
      (treeRel TY) h.onF (treeRel_onF hiff)) := by
  refine (Comb.zeroPi2_presInclHom_iff (ρ := treeRel TX) _
    _ h.onF (treeRel_onF hiff)).2 ?_
  intro v hv
  obtain ⟨u, rfl⟩ := chain2_treeUnivHom_surjective TX (x₀ := TX.root) v
  rw [← chain2_treeUnivHom_square hiff hE u, hzero TX.root u ((mem_pi2_iff_bdry2_univCover TX u).2 hv), map_zero]

end Naturality

/-! ### Chains of two-complexes with the topological hypothesis -/

variable {K : Complex2.{u}} (T₀ : SpanningTree K)
variable [Fintype (NonTree T₀)] [DecidableEq (NonTree T₀)] [Fintype K.F] [DecidableEq K.F]

end SpanningTree

/-! ### The statement without spanning trees -/

/-! ### Non-vacuity -/

end Comb
end FiniteChains
