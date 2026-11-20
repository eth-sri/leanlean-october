module

public import RequestProject.TreeCoverAcyclic
public import RequestProject.CombPi2


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

noncomputable section

namespace FiniteChains
namespace Comb

universe u

/-! ### Cancelling a common prefix and suffix from a homotopy -/

/-- A homotopy between two paths conjugated by a fixed prefix and suffix comes from a homotopy
between the paths themselves. -/
theorem htpy_of_congr_append {X : Complex2.{u}} {a b c d : X.V}
    {r s p q : List _}
    (hr : IsPath X.src X.tgt r c a) (hs : IsPath X.src X.tgt s b d)
    (hp : IsPath X.src X.tgt p a b) (hq : IsPath X.src X.tgt q a b)
    (h : Htpy X c d (r ++ p ++ s) (r ++ q ++ s)) : Htpy X a b p q := by
  have key : ∀ l : List _, IsPath X.src X.tgt l a b →
      Htpy X a b (revPath r ++ (r ++ l ++ s) ++ revPath s) l := by
    intro l hl
    have hss := hs.append (isPath_revPath hs)
    have e1 : revPath r ++ (r ++ l ++ s) ++ revPath s
        = (revPath r ++ r) ++ (l ++ (s ++ revPath s)) := by
      simp [List.append_assoc]
    have h1 :=
      Htpy.append_congr ((isPath_revPath hr).append hr) (hl.append hss) (htpy_revPath_append hr) (Htpy.refl _)
    have h2 :=
      Htpy.append_congr hl hss (Htpy.refl _) (htpy_append_revPath hs)
    rw [e1]
    refine h1.trans ?_
    simp_all
  exact ((key p hp).symm.trans (h.congr_append (isPath_revPath hr) (isPath_revPath hs))).trans (key q hq)

namespace SpanningTree

variable {K : Complex2.{u}} (T : SpanningTree K)
variable [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F]

/-- The relator subgroup of the collapsed presentation. -/
abbrev relTree := relSub (treeRel T)

/-- The universal cover of `K`, in the algebraic model: the cover attached to the relator
subgroup of the collapsed presentation. -/
abbrev treeUniv :=
  treeCover T _ (rel_mem_relSub _)

/-! ### The element of `π₁(K)` spelled by a vertex of the homotopy-theoretic cover -/

variable {T}

variable {x₀ : K.V}

/-- The element of `π₁(K) = ⟨E ∖ T | r⟩` spelled by a homotopy class of edge paths. -/
def uvQ : UV K x₀ → CovQ T (relTree T) :=
  Quotient.lift _
    (fun _ _ h => wordClass_htpy T h)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
@[simp] theorem uvQ_mk (p : PathFrom K x₀) :
    uvQ (UV.mk p) = wordQ T _ p.1 := rfl

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvQ_extend {c : UV K x₀} {eb : K.E × Bool}
    (h : endV c = germSrc K.src K.tgt eb) :
    uvQ (extend eb c) = uvQ c * germQ T _ eb := by
  induction c using UV.ind with
  | h p =>
      simp_all [extend_mk, uvQ_mk, extendP_pos, wordQ_append, wordQ_cons, wordQ_nil]

/-! ### The two-chain map is injective: `uvQ` separates classes with the same endpoint -/

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvQ_conjPath {x₀ b : K.V} {l : List _} (hl : IsPath K.src K.tgt l x₀ b) :
    pi1ToPres T (loopOf T hl) = wordQ T _ l := by
  show wordClass T (conjPath T l x₀ b) = _
  rw [conjPath, wordClass_append, wordClass_append]
  have h₁ : wordClass T (T.treePath x₀) = 1 := by
    show QuotientGroup.mk (pathWord T _) = 1
    simp
  have h₂ : wordClass T (revPath (T.treePath b)) = 1 := by
    show QuotientGroup.mk (pathWord T _) = 1
    simp [pathWord_revPath, pathWord_treePath]
  aesop

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- **Two homotopy classes of paths with the same endpoint spelling the same element of
`π₁(K)` are equal.**  This is the injectivity half of the computation of `π₁`. -/
theorem uvQ_injective {x₀ : K.V} {c d : UV K x₀} (hq : uvQ c = uvQ (T := T) d)
    (he : endV c = endV d) : c = d := by
  induction c using UV.ind with
  | h p =>
    induction d using UV.ind with
    | h q =>
      have hpe : endpt K x₀ p.1 = endpt K x₀ q.1 := he
      have hp := p.2
      have hq' : IsPath K.src K.tgt q.1 x₀ (endpt K x₀ p.1) := by
        rw [hpe]; exact q.2
      have hloop : loopOf T hp = loopOf T hq' := by
        refine (pi1EquivPres T).injective ?_
        show pi1ToPres T (loopOf T hp) = pi1ToPres T (loopOf T hq')
        simp_all [uvQ_conjPath]
      refine Quotient.sound ?_
      exact htpy_of_congr_append (T.treePath_isPath x₀)
        (isPath_revPath (T.treePath_isPath (endpt K x₀ p.1))) hp hq' (Quotient.exact hloop)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- **Every element of `π₁(K)` is spelled by a path to every vertex.** -/
theorem exists_uvQ (x₀ : K.V) (g : CovQ T _) (a : K.V) :
    ∃ c : UV K x₀, uvQ c = g ∧ endV c = a := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨L, hL, hLw⟩ := exists_loop_spelling T w
  set l : List _ := revPath (T.treePath x₀) ++ L ++ T.treePath a with hldef
  have hl :=
    ((isPath_revPath (T.treePath_isPath x₀)).append hL).append (T.treePath_isPath a)
  have hend := endpt_eq_of_isPath hl
  refine ⟨UV.mk ⟨l, by simp_all⟩, ?_, ?_⟩
  · show wordQ T _ l = _
    rw [hldef, wordQ_append, wordQ_append, wordQ_treePath]
    have hrev : wordQ T (relTree T) (revPath (T.treePath x₀)) = 1 := by
      show QuotientGroup.mk (pathWord T _) = 1
      simp [pathWord_revPath, pathWord_treePath]
    aesop
  · assumption

/-! ### The cellular map to the algebraic model -/

variable (T)

variable {x₀ : K.V}

/-- The map of edges: the edge `(c, e)` of the homotopy-theoretic cover goes to the edge
`(uvQ c, e)` of the algebraic one. -/
def uvEdge (E : UE K x₀) : (treeUniv T).E := (uvQ E.1.1, E.1.2)

/-- The map of two-cells. -/
def uvFace (F : UF K x₀) : (treeUniv T).F := (uvQ F.1.1, F.1.2)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- **The lifts of an edge path in the two models agree.** -/
theorem map_uLiftPath_tree : ∀ (L : List _) (c : UV K x₀) (w : K.V),
    IsPath K.src K.tgt L (endV c) w →
      (uLiftPath L c).map (fun Eb => (uvEdge T Eb.1, Eb.2))
        = liftK T _ L (uvQ c) := by
  intro L
  induction L with
  | nil => simp
  | cons eb t ih =>
      intro c w hL
      obtain ⟨e, b⟩ := eb
      cases b with
      | true =>
          have hc := hL.1
          have hnext : IsPath K.src K.tgt t (endV (extend (e, true) c)) w := by
            rw [endV_extend hc]; exact hL.2
          rw [uLiftPath_cons hc, List.map_cons, liftK_cons,
            ih _ w hnext, uvQ_extend hc] <;> rfl
      | false =>
          have hc := hL.1
          have hnext : IsPath K.src K.tgt t (endV (extend (e, false) c)) w := by
            rw [endV_extend hc]; exact hL.2
          rw [uLiftPath_cons hc, List.map_cons, liftK_cons,
            ih _ w hnext, uvQ_extend hc]
          congr 1
          show ((uvQ _, e), false)
            = SpanningTree.liftGerm T _ (uvQ c) _
          simp_all [uvQ_extend, SpanningTree.liftGerm]

/-- **The homotopy-theoretic universal cover of `K` is the algebraic one.** -/
def treeUnivHom (x₀ : K.V) : Hom (uCover K x₀) (treeUniv T) where
  onV c := (uvQ c, endV c)
  onE := uvEdge T
  onF := uvFace T
  src_onE E := by
    show (uvQ _, K.src E.1.2) = (uvQ E.1.1, endV E.1.1); rw [E.2]
  tgt_onE E := by
    show covTgt T _ (uvQ _, E.1.2)
      = (uvQ (extend (E.1.2, true) E.1.1), endV (extend (E.1.2, true) E.1.1))
    rw [uvQ_extend (eb := (E.1.2, true)) E.2, endV_extend (eb := (E.1.2, true)) E.2] <;> rfl
  base_onF F := by
    show (uvQ _, K.base F.1.2) = (uvQ F.1.1, endV F.1.1)
    simp [F.2]
  att_onF F := by
    have hatt : IsPath K.src K.tgt (K.att F.1.2) (endV F.1.1) (K.base F.1.2) := by
      rw [F.2]; apply K.att_isLoop
    show liftK T _ (K.att F.1.2) (uvQ _)
      = (uLiftPath _ _).map (fun Eb => (uvEdge T Eb.1, Eb.2))
    grind [map_uLiftPath_tree]

/-! ### The map is bijective -/

variable {x₀ : K.V}

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvEdge_injective : Function.Injective (uvEdge T (x₀ := x₀)) := by
  rintro ⟨⟨c, e⟩, hc⟩ ⟨⟨d, e'⟩, hd⟩ hEq
  have h1 : uvQ c = uvQ d := congrArg Prod.fst hEq
  have h2 : e = e' := congrArg Prod.snd hEq
  grind [uvQ_injective]

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvFace_injective : Function.Injective (uvFace T (x₀ := x₀)) := by
  rintro ⟨⟨c, f⟩, hc⟩ ⟨⟨d, f'⟩, hd⟩ hEq
  have h1 : uvQ c = uvQ d := congrArg Prod.fst hEq
  have h2 : f = f' := congrArg Prod.snd hEq
  grind [uvQ_injective]

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvFace_surjective :
    Function.Surjective (uvFace T (x₀ := x₀)) := by
  rintro ⟨g, f⟩
  obtain ⟨c, hc, hend⟩ := exists_uvQ x₀ g _
  exact ⟨⟨(c, f), hend⟩, by aesop⟩

/-! ### `π₂` is the same in the two models -/

variable {x₀ : K.V}

omit [Fintype (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- **A two-chain of the homotopy-theoretic universal cover of `K` is a cycle exactly when the
corresponding two-chain of the universal cover of the collapsed presentation complex is.**
Collapsing a spanning tree does not change `π₂`. -/
theorem mem_pi2_iff_bdry2_univCover (u : (uCover K x₀).F →₀ ℤ) :
    u ∈ Pi2 K x₀ ↔
      bdry2 (univCover (treeRel T)) (chain2 (treeUnivHom T x₀) u) = 0 := by
  classical
  have hkey : bdry2 (univCover (treeRel T)) (chain2 (treeUnivHom T x₀) u)
      = piE T _ (chain1 (treeUnivHom T x₀) (bdry2 (uCover K x₀) u)) := by
    rw [← bdry2_chain2 _ u]
    simp_all [piE_bdry2, rel_mem_relSub]
  constructor
  · intro hu
    have h0 : bdry2 _ u = 0 := hu
    simp_all
  · intro hu
    set z := chain1 _ _ with hz
    have hbz : bdry1 _ z = 0 := by
      rw [hz, ← bdry2_chain2 _ u]
      exact bdry1_bdry2 _
    have hzero :=
      treeChain_eq_zero (N := relTree T) (hN := rel_mem_relSub _)
        (support_isTree_of_piE_eq_zero (T := T) (N := relTree T) (by rw [hz, ← hkey]; exact hu)) hbz
    have hinj : Function.Injective (chain1 (treeUnivHom T x₀)) :=
      Finsupp.mapDomain_injective (uvEdge_injective T)
    solve_by_elim

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- Every two-chain of the universal cover of the collapsed presentation complex comes from a
two-chain of the homotopy-theoretic universal cover of `K`. -/
theorem chain2_treeUnivHom_surjective :
    Function.Surjective (chain2 (treeUnivHom T x₀)) := by
  classical
  intro v
  obtain ⟨u, hu⟩ := Finsupp.mapDomain_surjective (uvFace_surjective T (x₀ := x₀)) v <;> aesop

end SpanningTree
end Comb
end FiniteChains
