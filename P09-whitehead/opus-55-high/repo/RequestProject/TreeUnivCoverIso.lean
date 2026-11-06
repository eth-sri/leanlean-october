import RequestProject.TreeCoverAcyclic
import RequestProject.CombPi2
import RequestProject.UniversalCoverPi2
import RequestProject.Tac
noncomputable section


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

bwd

namespace FiniteChains.Comb

universe u

/-! ### Cancelling a common prefix and suffix from a homotopy -/

/-- A homotopy between two paths conjugated by a fixed prefix and suffix comes from a homotopy
between the paths themselves. -/
theorem htpy_of_congr_append {a b c d}
    {r s p q}
    (hr : IsPathX X r c a) (hs : IsPathX X s b d)
    (hp : IsPathX X p a b) (hq : IsPathX X q a b)
    (h : Htpy X c d (r ++ p ++ s) (r ++ q ++ s)) : Htpy X a b p q := by
  have key : ∀ l, IsPathX X l a b →
      Htpy X a b (revPath r ++ (r ++ l ++ s) ++ revPath s) l := by
    intro l hl
    have hrl := (isPath_revPath hr).append hr
    have hss := hs.append (isPath_revPath hs)
    have hlss := hl.append hss
    have e1 : revPath r ++ (r ++ l ++ s) ++ revPath s
        = (revPath r ++ r) ++ (l ++ (s ++ revPath s)) := by
      simp
    have h1 :=
      Htpy.append_congr hrl hlss (htpy_revPath_append hr) (Htpy.refl _)
    have h2 :=
      Htpy.append_congr hl hss (Htpy.refl _) (htpy_append_revPath hs)
    rw [e1]
    refine h1.trans ?_
    simpa using h2
  have h' := h.congr_append (isPath_revPath hr) (isPath_revPath hs)
  exact ((key p hp).symm.trans h').trans (key q hq)

namespace SpanningTree

variable {K : Complex2.{u}} (T : SpanningTree K)
variable [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F]

/-- The relator subgroup of the collapsed presentation. -/
abbrev relTree := relSub (treeRel T)

/-- The universal cover of `K`, in the algebraic model: the cover attached to the relator
subgroup of the collapsed presentation. -/
abbrev treeUniv :=
  treeCover T (relTree T) (rel_mem_relSub _)

/-! ### The element of `π₁(K)` spelled by a vertex of the homotopy-theoretic cover -/

variable {T}

/-- The element of `π₁(K) = ⟨E ∖ T | r⟩` spelled by a homotopy class of edge paths. -/
def uvQ : UV K x₀ → CovQ T (relTree T) :=
  Quotient.lift (wordQ T _ ·.1)
    (fun _ _ h => wordClass_htpy T h)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
@[simp] theorem uvQ_mk {x₀ : K.V} (p : PathFrom K x₀) :
    uvQ (T := T) (UV.mk p) = wordQ T (relTree T) p.1 := rfl

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvQ_extend {x₀ : K.V} {c : UV K x₀} {eb : K.E × Bool}
    (h : endV c = gSrcX K eb) :
    uvQ (T := T) (extend eb c) = uvQ (T := T) c * germQ T (relTree T) eb := by
  induction c using UV.ind with
  | h p =>
      have hp := h
      grind [extend_mk, uvQ_mk, extendP_pos hp, wordQ_append, wordQ_cons, wordQ_nil, mul_one]

/-! ### The two-chain map is injective: `uvQ` separates classes with the same endpoint -/

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvQ_conjPath {x₀ b : K.V} {l : List (K.E × Bool)} (hl : IsPathX K l x₀ b) :
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

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- **Two homotopy classes of paths with the same endpoint spelling the same element of
`π₁(K)` are equal.**  This is the injectivity half of the computation of `π₁`. -/
theorem uvQ_injective {x₀ : K.V} {c d : UV K x₀} (hq : uvQ (T := T) c = uvQ (T := T) d)
    (he : endV c = endV d) : c = d := by
  induction c using UV.ind with
  | h p =>
    induction d using UV.ind with
    | h q =>
      have hpe : endpt K x₀ p.1 = endpt K x₀ q.1 := he
      have hp := p.2
      have hq' : IsPathX K q.1 x₀ (endpt K x₀ p.1) := by
        grind
      have hloop : loopOf T hp = loopOf T hq' := by
        refine (pi1EquivPres T).injective ?_
        show pi1ToPres T (loopOf T hp) = pi1ToPres T (loopOf T hq')
        rw [uvQ_conjPath hp, uvQ_conjPath hq']
        exact hq
      have hhtpy := Quotient.exact hloop
      refine Quotient.sound ?_
      exact htpy_of_congr_append (T.treePath_isPath x₀)
        (isPath_revPath (T.treePath_isPath _)) hp hq' hhtpy

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- **Every element of `π₁(K)` is spelled by a path to every vertex.** -/
theorem exists_uvQ (x₀ : K.V) (g : CovQ T (relTree T)) (a : K.V) :
    ∃ c : UV K x₀, uvQ (T := T) c = g ∧ endV c = a := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective (s := relTree T) g
  obtain ⟨L, hL, hLw⟩ := exists_loop_spelling T w
  set l : List (K.E × Bool) := revPath (T.treePath x₀) ++ L ++ T.treePath a with hldef
  have hl :=
    ((isPath_revPath (T.treePath_isPath x₀)).append hL).append (T.treePath_isPath a)
  have hend := endpt_eq_of_isPath hl
  refine ⟨UV.mk ⟨l, by simp_all⟩, ?_, ?_⟩
  · show wordQ T _ l = _
    rw [hldef, wordQ_append, wordQ_append, wordQ_treePath]
    have hrev : wordQ T (relTree T) (revPath (T.treePath x₀)) = 1 := by
      show QuotientGroup.mk (pathWord T (revPath (T.treePath x₀))) = 1
      rw [pathWord_revPath, pathWord_treePath]
      simp
    aesop
  tauto

/-! ### The cellular map to the algebraic model -/

variable (T)

/-- The map of edges: the edge `(c, e)` of the homotopy-theoretic cover goes to the edge
`(uvQ c, e)` of the algebraic one. -/
def uvEdge (E : UE K x₀) : (treeUniv T).E := (uvQ (T := T) E.1.1, E.1.2)

/-- The map of two-cells. -/
def uvFace (F : UF K x₀) : (treeUniv T).F := (uvQ (T := T) F.1.1, F.1.2)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- **The lifts of an edge path in the two models agree.** -/
theorem map_uLiftPath_tree {x₀ : K.V} : ∀ (L : List (K.E × Bool)) (c : UV K x₀) (w : K.V),
    IsPathX K L (endV c) w →
      (uLiftPath L c).map (fun Eb => (uvEdge T Eb.1, Eb.2))
        = liftK T (relTree T) L (uvQ (T := T) c) := by
  intro L
  induction L with
  | nil => simp
  | cons eb t ih =>
      intro c w hL
      cases' eb with e b
      cases b with
      | true =>
          have hc := hL.1
          have hnext : IsPathX K t (endV (extend (e, true) c)) w := by
            simp_all [endV_extend hc]
          rw [uLiftPath_cons hc, List.map_cons, liftK_cons,
            ih _ w hnext, uvQ_extend hc]
          congr 1
      | false =>
          have hc := hL.1
          have hnext : IsPathX K t (endV (extend (e, false) c)) w := by
            simp_all [endV_extend hc]
          rw [uLiftPath_cons hc, List.map_cons, liftK_cons,
            ih _ w hnext, uvQ_extend hc]
          congr 1
          show ((uvQ (T := T) (extend (e, false) c), e), false)
            = T.liftGerm _ (uvQ (T := T) c) (e, false)
          rw [uvQ_extend hc]
          rfl

/-- **The homotopy-theoretic universal cover of `K` is the algebraic one.** -/
def treeUnivHom x₀ : Hom (uCover K x₀) (treeUniv T) where
  onV c := (uvQ (T := T) c, endV c)
  onE := uvEdge T
  onF := uvFace T
  src_onE E := by
    show (uvQ (T := T) E.1.1, K.src E.1.2) = (uvQ (T := T) E.1.1, endV E.1.1)
    grind
  tgt_onE E := by
    show covTgt T (relTree T) (uvQ (T := T) E.1.1, E.1.2)
      = (uvQ (T := T) (extend (E.1.2, true) E.1.1), endV (extend (E.1.2, true) E.1.1))
    rw [uvQ_extend (eb := (E.1.2, true)) E.2, endV_extend (eb := (E.1.2, true)) E.2]
    rfl
  base_onF F := by
    show (uvQ (T := T) F.1.1, K.base F.1.2) = (uvQ (T := T) F.1.1, endV F.1.1)
    grind
  att_onF F := by
    have hbase := F.2
    have hatt : IsPathX K (K.att F.1.2) (endV F.1.1) (K.base F.1.2) := by
      rw [hbase]; exact K.att_isLoop F.1.2
    show liftK T (relTree T) (K.att F.1.2) (uvQ (T := T) F.1.1)
      = (uLiftPath (K.att F.1.2) F.1.1).map (fun Eb => (uvEdge T Eb.1, Eb.2))
    rw [map_uLiftPath_tree T (K.att F.1.2) F.1.1 (K.base F.1.2) hatt]

/-! ### The map is bijective -/

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvEdge_injective {x₀ : K.V} : Function.Injective (uvEdge T (x₀ := x₀)) := by
  rintro ⟨⟨c, e⟩, hc⟩ ⟨⟨d, e'⟩, hd⟩ hEq
  have h1 := congrArg Prod.fst hEq
  have h2 : e = e' := congrArg Prod.snd hEq
  subst h2
  have hend : endV c = endV d := by simp_all
  exact Subtype.ext (Prod.ext (uvQ_injective h1 hend) rfl)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvFace_injective {x₀ : K.V} : Function.Injective (uvFace T (x₀ := x₀)) := by
  rintro ⟨⟨c, f⟩, hc⟩ ⟨⟨d, f'⟩, hd⟩ hEq
  have h1 := congrArg Prod.fst hEq
  have h2 : f = f' := congrArg Prod.snd hEq
  subst h2
  have hend : endV c = endV d := by simp_all
  exact Subtype.ext (Prod.ext (uvQ_injective h1 hend) rfl)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvFace_surjective {x₀ : K.V} :
    Function.Surjective (uvFace T (x₀ := x₀)) := by
  rintro ⟨g, f⟩
  obtain ⟨c, hc, hend⟩ := exists_uvQ x₀ g _
  exact ⟨⟨(c, f), hend⟩, by aesop⟩

/-! ### `π₂` is the same in the two models -/

omit [Fintype (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- **A two-chain of the homotopy-theoretic universal cover of `K` is a cycle exactly when the
corresponding two-chain of the universal cover of the collapsed presentation complex is.**
Collapsing a spanning tree does not change `π₂`. -/
theorem mem_pi2_iff_bdry2_univCover {x₀ : K.V} (u : (uCover K x₀).F →₀ ℤ) :
    u ∈ Pi2 K x₀ ↔
      bdry2 (univCover (treeRel T)) (chain2 (treeUnivHom T x₀) u) = 0 := by
  classical
  have hkey : bdry2 (univCover (treeRel T)) (chain2 (treeUnivHom T x₀) u)
      = piE T _ (chain1 (treeUnivHom T x₀) (bdry2 _ u)) := by
    rw [← bdry2_chain2 _ u]
    exact (piE_bdry2 (T := T) (N := relTree T) (hN := rel_mem_relSub _)
      _).symm
  constructor
  · intro hu
    have h0 : bdry2 _ u = 0 := hu
    simp_all
  · intro hu
    set z := chain1 (treeUnivHom T x₀) (bdry2 _ u) with hz
    have hze : piE T _ z = 0 := by simp_all
    have hbz : bdry1 _ z = 0 := by
      rw [hz, ← bdry2_chain2 _ u]
      exact bdry1_bdry2 _
    have hzero :=
      treeChain_eq_zero (T := T) (N := relTree T) (hN := rel_mem_relSub _)
        (support_isTree_of_piE_eq_zero (T := T) (N := relTree T) hze) hbz
    have hinj : Function.Injective (chain1 (treeUnivHom T x₀)) :=
      Finsupp.mapDomain_injective (uvEdge_injective T)
    tauto

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- Every two-chain of the universal cover of the collapsed presentation complex comes from a
two-chain of the homotopy-theoretic universal cover of `K`. -/
theorem chain2_treeUnivHom_surjective {x₀ : K.V} :
    Function.Surjective (chain2 (treeUnivHom T x₀)) := by
  classical
  intro v
  cases' Finsupp.mapDomain_surjective (M := ℤ) (uvFace_surjective T (x₀ := x₀)) v with u hu
  tauto
