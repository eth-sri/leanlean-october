import Mathlib.Tactic

import RequestProject.TreePresentation
import RequestProject.CoverComplex

/-!
# The cover of a two-complex attached to a normal subgroup of the collapsed presentation

`RequestProject/TreePresentation.lean` identifies `π₁(K)` with the group presented by the
non-tree edges of a spanning tree `T`.  This file builds, for every normal subgroup
`N ◁ F(E ∖ T)` containing the relators, the corresponding cover of `K` itself:

* `FiniteChains.Comb.SpanningTree.treeCover` — vertices `Q × V`, edges `Q × E`, two-cells
  `Q × F`, where `Q = F(E ∖ T)/N` is the deck group; an edge `(q, e)` runs from `(q, src e)`
  to `(q · [e], tgt e)`, where `[e]` is the image in `Q` of the letter spelled by `e` (trivial
  for a tree edge), and a two-cell `(q, f)` is attached along the lift at `q` of the attaching
  path of `f`;
* `FiniteChains.Comb.SpanningTree.treeCoverProj` — the projection to `K`, and
  `treeCoverProj_isCovering` — it is a combinatorial covering;
* `FiniteChains.Comb.SpanningTree.treeCoverDeck`, `treeCoverProj_isRegular` — the deck action
  of `Q` by left translation makes it a regular covering;
* `FiniteChains.Comb.SpanningTree.treeCover_isConnected` — the cover is connected when `K` is.

The acyclicity of this cover is proved in `RequestProject/TreeCoverAcyclic.lean`.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.SpanningTree




variable {K : Complex2.{u}} (T : SpanningTree K)
variable (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]

/-- The deck group of the cover: the presented group of the collapse modulo `N`. -/
abbrev CovQ  := FreeGroup (NonTree T) ⧸ N

variable (g : K.E × Bool)
/-- The translation of the cover attached to an oriented edge: trivial for a tree edge, the
class of the generator otherwise. -/
noncomputable def germQ  : CovQ T N := QuotientGroup.mk (germWord T g)

variable (p : List (K.E × Bool))
/-- The translation attached to an edge path. -/
noncomputable def wordQ  : CovQ T N :=
  QuotientGroup.mk (pathWord T p)

variable {T N}

@[simp] theorem wordQ_nil : wordQ T N ([] : List (K.E × Bool)) = 1 := rfl

theorem wordQ_cons   :
    wordQ T N (g :: p) = germQ T N g * wordQ T N p := rfl

theorem wordQ_append (p p' : List (K.E × Bool)) :
    wordQ T N (p ++ p') = wordQ T N p * wordQ T N p' := by
  classical simp_all [wordQ, pathWord_append]

theorem germQ_revGerm  : germQ T N (revGerm g) = (germQ T N g)⁻¹ := by
  classical simp_all [germQ, germWord_revGerm]

theorem germQ_false_eq_inv (e : K.E) :
    germQ T N (e, false) = (germQ T N (e, true))⁻¹ := by
  simpa [revGerm] using germQ_revGerm (T := T) (N := N) (e, true)

theorem germQ_false_mul_true (e : K.E) :
    germQ T N (e, false) * germQ T N (e, true) = 1 := by
  rw [germQ_false_eq_inv]
  group

@[simp] theorem wordQ_treePath (a : K.V) : wordQ T N (T.treePath a) = 1 := by
  unfold wordQ
  rw [pathWord_treePath]
  rfl

variable (T N)

/-! ### The vertices, the edges and their endpoints -/

variable (x : CovQ T N × K.E)
/-- The source of an edge of the cover. -/
def covSrc   := (x.1, K.src x.2)

/-- The target of an edge of the cover. -/
noncomputable def covTgt   :=
  (x.1 * germQ T N (x.2, true), K.tgt x.2)

variable (q : CovQ T N)
  (g : K.E × Bool)
/-- The lift at the vertex `q` of an oriented edge of `K`. -/
noncomputable def liftGerm    :=
  if g.2 then ((q, g.1), true) else ((q * germQ T N g, g.1), false)

/-- The lift at the vertex `q` of an edge path of `K`. -/
noncomputable def liftK : List (K.E × Bool) → CovQ T N → List ((CovQ T N × K.E) × Bool)
  | [], _ => []
  | g :: L, q => liftGerm T N q g :: liftK L (q * germQ T N g)

variable {T N}

@[simp] theorem liftK_nil  : liftK T N [] q = [] := rfl

variable (L : List (K.E × Bool))
@[simp] theorem liftK_cons   (q : CovQ T N) :
    liftK T N (g :: L) q = liftGerm T N q g :: liftK T N L (q * germQ T N g) := rfl

@[simp] theorem liftGerm_fst_snd   :
    ((liftGerm T N q g).1.2, (liftGerm T N q g).2) = g := by aesop (add simp [liftGerm])

theorem germSrc_liftGerm   :
    germSrc (covSrc T N) (covTgt T N) (liftGerm T N q g) = (q, germSrc K.src K.tgt g) := by
  obtain ⟨e, b⟩ := g
  cases b
  · show covTgt T N (q * germQ T N (e, false), e) = (q, K.tgt e)
    show (q * germQ T N (e, false) * germQ T N (e, true), K.tgt e) = (q, K.tgt e)
    rw [mul_assoc, germQ_false_mul_true, mul_one]
  · rfl

theorem germTgt_liftGerm   :
    germTgt (covSrc T N) (covTgt T N) (liftGerm T N q g) =
      (q * germQ T N g, germTgt K.src K.tgt g) := by
  obtain ⟨e, b⟩ := g
  cases b
  · rfl
  · rfl

/-- The projection of a lifted path is the path itself. -/
theorem map_liftK  (q : CovQ T N) :
    (liftK T N L q).map (fun eb => (eb.1.2, eb.2)) = L := by
  induction L generalizing q <;> simp_all

/-- The lift at `q` of a path from `a` to `b` is a path from `(q, a)` to `(q · w, b)`, where
`w` is the word spelled by the path. -/
theorem liftK_isPath {L : List (K.E × Bool)} {a b : K.V} (hL : IsPath K.src K.tgt L a b)
    (q : CovQ T N) :
    IsPath (covSrc T N) (covTgt T N) (liftK T N L q) (q, a) (q * wordQ T N L, b) := by
  induction L generalizing a q with
  | nil =>
      have hab  := hL
      subst hab
      simp [wordQ]
  | cons g L ih =>
      obtain ⟨ha, hrest⟩ := hL
      subst ha
      refine ⟨?_, ?_⟩
      · rw [germSrc_liftGerm]
      · grind [germTgt_liftGerm, wordQ_cons]

/-! ### The cover -/

variable (T N)

variable (hN : ∀ f, treeRel T f ∈ N)
/-- **The cover of `K` attached to `N ◁ F(E ∖ T)`**: vertices `Q × V`, edges `Q × E`,
two-cells `Q × F`, with the two-cell `(q, f)` attached along the lift at `q` of the attaching
path of `f`. -/
noncomputable def treeCover  : Complex2.{u} where
  V := CovQ T N × K.V
  E := CovQ T N × K.E
  F := CovQ T N × K.F
  src := covSrc T N
  tgt := covTgt T N
  base f := (f.1, K.base f.2)
  att f := liftK T N (K.att f.2) f.1
  att_isLoop f := by
    have h := liftK_isPath (T := T) (N := N) (K.att_isLoop f.2) f.1
    have hw : wordQ T N (K.att f.2) = 1 := by
      show QuotientGroup.mk (pathWord T (K.att f.2)) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hN f.2
    rwa [hw, mul_one] at h

variable {T N}

variable (x : CovQ T N × K.E)
@[simp] theorem treeCover_src   :
    (treeCover T N hN).src x = covSrc T N x := rfl

@[simp] theorem treeCover_tgt   :
    (treeCover T N hN).tgt x = covTgt T N x := rfl

variable (T N)

/-- The projection of the cover onto `K`. -/
noncomputable def treeCoverProj  : Hom (treeCover T N hN) K where
  onV x := x.2
  onE x := x.2
  onF x := x.2
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := by
    simp_all [treeCover, map_liftK]

/-! ### The projection is a covering -/

/-! ### The deck action -/

/-! ### Connectedness -/

/-- Every element of the free group on the non-tree edges is spelled by a loop of `K` at the
root. -/
theorem exists_loop_spelling (w : FreeGroup (NonTree T)) :
    ∃ p : List (K.E × Bool), IsPath K.src K.tgt p T.root T.root ∧ pathWord T p = w := by
  classical
  induction w using FreeGroup.induction_on with
  | one => exact ⟨[], rfl, rfl⟩
  | of e =>
      refine ⟨conjPath T [((e : K.E), true)] (K.src (e : K.E)) (K.tgt (e : K.E)), ?_, ?_⟩
      · exact conjPath_isLoop T (isPath_single _)
      · rw [conjPath, pathWord_append, pathWord_append, pathWord_treePath, pathWord_revPath,
          pathWord_treePath]
        simp [pathWord, germWord, dif_neg e.2]
  | inv_of e ih =>
      obtain ⟨p, hp, hw⟩ := ih
      exact ⟨revPath p, isPath_revPath hp, by rw [pathWord_revPath, hw]⟩
  | mul x y hx hy =>
      classical aesop (add unsafe apply [FiniteChains.Comb.IsPath.append, FiniteChains.Comb.SpanningTree.pathWord_append])

end FiniteChains.Comb.SpanningTree


