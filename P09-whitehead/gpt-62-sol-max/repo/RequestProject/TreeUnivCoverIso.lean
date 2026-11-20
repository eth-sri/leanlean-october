module

public import RequestProject.TreeCoverAcyclic
public import RequestProject.CombPi2
public import RequestProject.UniversalCoverPi2
public import RequestProject.UniversalCoverVoltage

@[expose] public section

/-!
# Collapsing a spanning tree does not change `π₂`

`RequestProject/TreeCover.lean` builds, for a spanning tree `T` of a two-complex `K`, the
cover `treeCover T N` of `K` attached to a normal subgroup `N` of the free group on the
non-tree edges, and `RequestProject/TreeCoverAcyclic.lean` compares its chain complex with
that of the cover of the *collapsed* presentation complex `⟨E ∖ T | r⟩`.

Condition (1) of Theorem A, however, speaks of `π₂` in the homotopy-theoretic model
`FiniteChains.Comb.uCover` of the universal cover, the one built out of homotopy classes of
edge paths (`RequestProject/CombUniversalCover.lean`).  This file identifies the two:

* `FiniteChains.Comb.SpanningTree.uvQ` — the element of `π₁(K) = ⟨E ∖ T | r⟩` spelled by a
  vertex of the homotopy-theoretic universal cover (a homotopy class of edge paths);
* `FiniteChains.Comb.SpanningTree.treeUnivHom` — the resulting cellular map from the
  homotopy-theoretic universal cover of `K` to the algebraic one, `treeCover T ⟪r⟫`; it is
  bijective on vertices, edges and two-cells;
* `FiniteChains.Comb.SpanningTree.mem_pi2_iff_bdry2_univCover` — **a two-chain of the
  homotopy-theoretic universal cover of `K` is a cycle exactly when the corresponding chain of
  the universal cover of the collapsed presentation complex is**.  In other words, collapsing
  a spanning tree does not change `π₂`: the tree edges carry no homology, so deleting their
  coordinates does not enlarge the kernel of `∂₂`.

The last statement is what turns the topological form of condition (1) of Theorem A into the
algebraic one used in Section 2 of the paper.
-/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains
namespace Comb

universe u

namespace SpanningTree

variable {K : Complex2.{u}} (T : SpanningTree K)

/-- The relator subgroup of the collapsed presentation. -/
noncomputable abbrev relTree : Subgroup (FreeGroup (NonTree T)) := relSub (treeRel T)

/-- The universal cover of `K`, in the algebraic model: the cover attached to the relator
subgroup of the collapsed presentation. -/
noncomputable abbrev treeUniv : Complex2.{u} :=
  treeCover T (relTree T) (rel_mem_relSub (treeRel T))

/-! ### The element of `π₁(K)` spelled by a vertex of the homotopy-theoretic cover -/

variable {T}

/-- The element of `π₁(K) = ⟨E ∖ T | r⟩` spelled by a homotopy class of edge paths. -/
noncomputable def uvQ {x₀ : K.V} : UV K x₀ → CovQ T (relTree T) :=
  Quotient.lift (fun p  => wordQ T (relTree T) p.1)
    (fun _ _ h => wordClass_htpy T h)

@[simp] theorem uvQ_mk {x₀ : K.V} (p : PathFrom K x₀) :
    uvQ (T := T) (UV.mk p) = wordQ T (relTree T) p.1 := rfl

theorem uvQ_extend {x₀ : K.V} {c : UV K x₀} {eb : K.E × Bool}
    (h : endV c = germSrc K.src K.tgt eb) :
    uvQ (T := T) (extend eb c) = uvQ (T := T) c * germQ T (relTree T) eb := by
  induction c using UV.ind with
  | h p =>
      have hp  := h
      rw [extend_mk, uvQ_mk, extendP_pos hp, uvQ_mk, wordQ_append]
      congr 1
      rw [show ([eb] : List (K.E × Bool)) = eb :: [] from rfl, wordQ_cons, wordQ_nil, mul_one]

/-! ### The two-chain map is injective: `uvQ` separates classes with the same endpoint -/

theorem uvQ_conjPath {x₀ b : K.V} {l : List (K.E × Bool)} (hl : IsPath K.src K.tgt l x₀ b) :
    pi1ToPres T (loopOf T hl) = wordQ T (relTree T) l := by
  show wordClass T (conjPath T l x₀ b) = _
  rw [conjPath, wordClass_append, wordClass_append]
  have h₁ : wordClass T (T.treePath x₀) = 1 := by
    show QuotientGroup.mk (pathWord T (T.treePath x₀)) = 1
    simp
  have h₂ : wordClass T (revPath (T.treePath b)) = 1 := by
    show QuotientGroup.mk (pathWord T (revPath (T.treePath b))) = 1
    rw [pathWord_revPath, pathWord_treePath]
    simp
  aesop

/-- **Two homotopy classes of paths with the same endpoint spelling the same element of
`π₁(K)` are equal.**  This is the injectivity half of the computation of `π₁`. -/
theorem uvQ_injective {x₀ : K.V} {c d : UV K x₀} (hq : uvQ (T := T) c = uvQ (T := T) d)
    (he : endV c = endV d) : c = d := by
  induction c using UV.ind with
  | h p =>
    induction d using UV.ind with
    | h q =>
      have hpe : endpt K x₀ p.1 = endpt K x₀ q.1 := he
      have hp  := p.2
      have hq' : IsPath K.src K.tgt q.1 x₀ (endpt K x₀ p.1) := by
        rw [hpe]; exact q.2
      have hloop : loopOf T hp = loopOf T hq' := by
        refine (pi1EquivPres T).injective ?_
        show pi1ToPres T (loopOf T hp) = pi1ToPres T (loopOf T hq')
        rw [uvQ_conjPath hp, uvQ_conjPath hq']
        exact hq
      have hhtpy  := Quotient.exact hloop
      refine Quotient.sound ?_
      show Htpy K x₀ (endpt K x₀ p.1) p.1 q.1
      exact htpy_of_congr_append (T.treePath_isPath x₀)
        (isPath_revPath (T.treePath_isPath (endpt K x₀ p.1))) hp hq' hhtpy

/-- **Every element of `π₁(K)` is spelled by a path to every vertex.** -/
theorem exists_uvQ (x₀ : K.V) (g : CovQ T (relTree T)) (a : K.V) :
    ∃ c : UV K x₀, uvQ (T := T) c = g ∧ endV c = a := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective (s := relTree T) g
  obtain ⟨L, hL, hLw⟩ := exists_loop_spelling T w
  set l : List (K.E × Bool) := revPath (T.treePath x₀) ++ L ++ T.treePath a with hldef
  have hl  :=
    ((isPath_revPath (T.treePath_isPath x₀)).append hL).append (T.treePath_isPath a)
  have hend  := endpt_eq_of_isPath hl
  refine ⟨UV.mk ⟨l, by simp_all⟩, ?_, ?_⟩
  · show wordQ T (relTree T) l = _
    rw [hldef, wordQ_append, wordQ_append, wordQ_treePath]
    have hrev : wordQ T (relTree T) (revPath (T.treePath x₀)) = 1 := by
      show QuotientGroup.mk (pathWord T (revPath (T.treePath x₀))) = 1
      rw [pathWord_revPath, pathWord_treePath]
      simp
    aesop
  · assumption

/-! ### The cellular map to the algebraic model -/

variable (T)

/-- The map of edges: the edge `(c, e)` of the homotopy-theoretic cover goes to the edge
`(uvQ c, e)` of the algebraic one. -/
noncomputable def uvEdge {x₀ : K.V} (E : UE K x₀) : (treeUniv T).E := (uvQ (T := T) E.1.1, E.1.2)

/-- The map of two-cells. -/
noncomputable def uvFace {x₀ : K.V} (F : UF K x₀) : (treeUniv T).F := (uvQ (T := T) F.1.1, F.1.2)

/-- **The lifts of an edge path in the two models agree.** -/
theorem map_uLiftPath_tree {x₀ : K.V} : ∀ (L : List (K.E × Bool)) (c : UV K x₀) (w : K.V),
    IsPath K.src K.tgt L (endV c) w →
      (uLiftPath L c).map (fun Eb => (uvEdge T Eb.1, Eb.2))
        = liftK T (relTree T) L (uvQ (T := T) c) := by
  intro L c w hL
  exact map_uLiftPath_voltage (germQ T (relTree T)) uvQ (fun _ _ h => uvQ_extend h) hL

/-- **The homotopy-theoretic universal cover of `K` is the algebraic one.** -/
noncomputable def treeUnivHom (x₀ : K.V) : Hom (uCover K x₀) (treeUniv T) where
  onV c := (uvQ (T := T) c, endV c)
  onE := uvEdge T
  onF := uvFace T
  src_onE E := by
    show (uvQ (T := T) E.1.1, K.src E.1.2) = (uvQ (T := T) E.1.1, endV E.1.1)
    rw [E.2]
  tgt_onE E := by
    show covTgt T (relTree T) (uvQ (T := T) E.1.1, E.1.2)
      = (uvQ (T := T) (extend (E.1.2, true) E.1.1), endV (extend (E.1.2, true) E.1.1))
    rw [uvQ_extend (eb := (E.1.2, true)) E.2, endV_extend (eb := (E.1.2, true)) E.2]
    rfl
  base_onF F := by
    show (uvQ (T := T) F.1.1, K.base F.1.2) = (uvQ (T := T) F.1.1, endV F.1.1)
    grind
  att_onF F := by
    have hbase  := F.2
    have hatt : IsPath K.src K.tgt (K.att F.1.2) (endV F.1.1) (K.base F.1.2) := by
      rw [hbase]; exact K.att_isLoop F.1.2
    show liftK T (relTree T) (K.att F.1.2) (uvQ (T := T) F.1.1)
      = (uLiftPath (K.att F.1.2) F.1.1).map (fun Eb => (uvEdge T Eb.1, Eb.2))
    rw [map_uLiftPath_tree T (K.att F.1.2) F.1.1 (K.base F.1.2) hatt]

/-! ### The map is bijective -/

private theorem uvCell_bijective {B : Type u} {x₀ : K.V} (base : B → K.V) :
    Function.Bijective (fun x : {x : UV K x₀ × B // endV x.1 = base x.2} =>
      (uvQ (T := T) x.val.1, x.val.2)) := by
  constructor
  · rintro ⟨⟨c, e⟩, hc⟩ ⟨⟨d, e'⟩, hd⟩ h
    have he : e = e' := congrArg Prod.snd h
    exact Subtype.ext (Prod.ext (uvQ_injective (congrArg Prod.fst h)
      (hc.trans ((congrArg base he).trans hd.symm))) he)
  · rintro ⟨g, e⟩
    obtain ⟨c, hc, he⟩ := exists_uvQ x₀ g (base e)
    exact ⟨⟨(c, e), he⟩, Prod.ext hc rfl⟩

theorem uvEdge_injective {x₀ : K.V} : Function.Injective (uvEdge T (x₀ := x₀)) :=
  (uvCell_bijective T K.src).injective

theorem uvFace_injective {x₀ : K.V} : Function.Injective (uvFace T (x₀ := x₀)) :=
  (uvCell_bijective T K.base).injective

theorem uvFace_surjective {x₀ : K.V} : Function.Surjective (uvFace T (x₀ := x₀)) :=
  (uvCell_bijective T K.base).surjective

/-! ### `π₂` is the same in the two models -/

/-- **A two-chain of the homotopy-theoretic universal cover of `K` is a cycle exactly when the
corresponding two-chain of the universal cover of the collapsed presentation complex is.**
Collapsing a spanning tree does not change `π₂`. -/
theorem mem_pi2_iff_bdry2_univCover [DecidableEq (NonTree T)] {x₀ : K.V} (u : (uCover K x₀).F →₀ ℤ) :
    u ∈ Pi2 K x₀ ↔
      bdry2 (univCover (treeRel T)) (chain2 (treeUnivHom T x₀) u) = 0 := by
  classical
  have hkey : bdry2 (univCover (treeRel T)) (chain2 (treeUnivHom T x₀) u)
      = piE T (relTree T) (chain1 (treeUnivHom T x₀) (bdry2 (uCover K x₀) u)) := by
    rw [← bdry2_chain2 (treeUnivHom T x₀) u]
    exact (piE_bdry2 (T := T) (N := relTree T) (hN := rel_mem_relSub (treeRel T))
      (chain2 (treeUnivHom T x₀) u)).symm
  constructor
  · intro hu
    have h0  := hu
    rw [hkey, h0, map_zero, map_zero]
  · intro hu
    show bdry2 (uCover K x₀) u = 0
    set z := chain1 (treeUnivHom T x₀) (bdry2 (uCover K x₀) u) with hz
    have hze : piE T (relTree T) z = 0 := by rw [hz, ← hkey]; exact hu
    have hbz : bdry1 (treeUniv T) z = 0 := by
      rw [hz, ← bdry2_chain2 (treeUnivHom T x₀) u]
      exact bdry1_bdry2 _
    have hzero  :=
      treeChain_eq_zero (T := T) (N := relTree T) (hN := rel_mem_relSub (treeRel T))
        (support_isTree_of_piE_eq_zero (T := T) (N := relTree T) hze) hbz
    have hinj : Function.Injective (chain1 (treeUnivHom T x₀)) :=
      Finsupp.mapDomain_injective (uvEdge_injective T)
    exact hinj (by tauto)

/-- Every two-chain of the universal cover of the collapsed presentation complex comes from a
two-chain of the homotopy-theoretic universal cover of `K`. -/
theorem chain2_treeUnivHom_surjective {x₀ : K.V} :
    Function.Surjective (chain2 (treeUnivHom T x₀)) := by
  classical
  intro v
  obtain ⟨u, hu⟩ := Finsupp.mapDomain_surjective (M := ℤ) (uvFace_surjective T (x₀ := x₀)) v
  tauto

end SpanningTree
end Comb
end FiniteChains
