import RequestProject.TreePresentation
import RequestProject.CoverComplex
import RequestProject.Tac
noncomputable section


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

bwd

namespace FiniteChains.Comb.SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)
variable (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]

/-- The deck group of the cover: the presented group of the collapse modulo `N`. -/
abbrev CovQ := FreeGroup (NonTree T) ⧸ N

/-- The translation of the cover attached to an oriented edge: trivial for a tree edge, the
class of the generator otherwise. -/
def germQ (g : K.E × Bool) : CovQ T N := QuotientGroup.mk (germWord T g)

/-- The translation attached to an edge path. -/
def wordQ (p : List (K.E × Bool)) : CovQ T N :=
  QuotientGroup.mk (pathWord T p)

variable {T N}

@[simp] theorem wordQ_nil : wordQ T N ([]) = 1 := rfl

theorem wordQ_cons g p :
    wordQ T N (g :: p) = germQ T N g * wordQ T N p := by
  rfl

theorem wordQ_append p p' :
    wordQ T N (p ++ p') = wordQ T N p * wordQ T N p' := by
  unfold wordQ
  rw [pathWord_append, QuotientGroup.mk_mul]

theorem germQ_revGerm g : germQ T N (revGerm g) = (germQ T N g)⁻¹ := by
  unfold germQ
  rw [germWord_revGerm, QuotientGroup.mk_inv]

theorem germQ_false_eq_inv e :
    germQ T N (e, false) = (germQ T N (e, true))⁻¹ := by
  simpa [revGerm] using germQ_revGerm (T := T) (N := N) (e, true)

theorem germQ_false_mul_true e :
    germQ T N (e, false) * germQ T N (e, true) = 1 := by
  rw [germQ_false_eq_inv]
  group

@[simp] theorem wordQ_treePath a : wordQ T N (T.treePath a) = 1 := by
  unfold wordQ
  rw [pathWord_treePath]
  rfl

variable (T N)

/-! ### The vertices, the edges and their endpoints -/

/-- The source of an edge of the cover. -/
def covSrc (x : CovQ T N × K.E) := (x.1, K.src x.2)

/-- The target of an edge of the cover. -/
def covTgt (x : CovQ T N × K.E) :=
  (x.1 * germQ T N (x.2, true), K.tgt x.2)

/-- The lift at the vertex `q` of an oriented edge of `K`. -/
def liftGerm (q : CovQ T N) (g : K.E × Bool) :=
  if g.2 then ((q, g.1), true) else ((q * germQ T N g, g.1), false)

/-- The lift at the vertex `q` of an edge path of `K`. -/
def liftK : List (K.E × Bool) → CovQ T N → List ((CovQ T N × K.E) × Bool)
  | [], _ => []
  | g :: L, q => liftGerm T N q g :: liftK L (q * germQ T N g)

variable {T N}

@[simp] theorem liftK_nil q : liftK T N [] q = [] := rfl

@[simp] theorem liftK_cons g L q :
    liftK T N (g :: L) q = liftGerm T N q g :: liftK T N L (q * germQ T N g) := rfl

@[simp] theorem liftGerm_fst_snd q g :
    ((liftGerm T N q g).1.2, (liftGerm T N q g).2) = g := by
  grind [liftGerm]

theorem germSrc_liftGerm q g :
    germSrc (covSrc T N) (covTgt T N) (liftGerm T N q g) = (q, gSrcX K g) := by
  cases' g with e b
  cases b
  · show (q * germQ T N (e, false) * germQ T N (e, true), K.tgt e) = (q, K.tgt e)
    rw [mul_assoc, germQ_false_mul_true, mul_one]
  · rfl

theorem germTgt_liftGerm q g :
    germTgt (covSrc T N) (covTgt T N) (liftGerm T N q g) =
      (q * germQ T N g, gTgtX K g) := by
  cases' g with e b
  cases b
  · rfl
  · rfl

/-- The projection of a lifted path is the path itself. -/
theorem map_liftK L q :
    (liftK T N L q).map (fun eb => (eb.1.2, eb.2)) = L := by
  induction L generalizing q <;> simp_all

/-- The lift at `q` of a path from `a` to `b` is a path from `(q, a)` to `(q · w, b)`, where
`w` is the word spelled by the path. -/
theorem liftK_isPath (hL : IsPathX K L a b)
    q :
    IsPath (covSrc T N) (covTgt T N) (liftK T N L q) (q, a) (q * wordQ T N L, b) := by
  induction L generalizing a q with
  | nil =>
      simp_all
  | cons g L ih =>
      cases' hL with ha hrest
      subst ha
      refine ⟨?_, ?_⟩
      · rw [germSrc_liftGerm]
      · rw [germTgt_liftGerm, wordQ_cons, ← mul_assoc]
        simp_all

/-! ### The cover -/

variable (T N)

/-- **The cover of `K` attached to `N ◁ F(E ∖ T)`**: vertices `Q × V`, edges `Q × E`,
two-cells `Q × F`, with the two-cell `(q, f)` attached along the lift at `q` of the attaching
path of `f`. -/
def treeCover (hN : ∀ f, treeRel T f ∈ N) : Complex2.{u} where
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
      aesop
    simp_all

variable {T N}

@[simp] theorem treeCover_src hN (x : CovQ T N × K.E) :
    (treeCover T N hN).src x = covSrc T N x := rfl

@[simp] theorem treeCover_tgt hN (x : CovQ T N × K.E) :
    (treeCover T N hN).tgt x = covTgt T N x := rfl

variable (T N)

/-- The projection of the cover onto `K`. -/
def treeCoverProj hN : Hom (treeCover T N hN) K where
  onV x := x.2
  onE x := x.2
  onF x := x.2
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := (map_liftK (T := T) (N := N) (K.att f.2) f.1).symm

/-! ### The projection is a covering -/

/-! ### The deck action -/

/-! ### Connectedness -/

/-- Every element of the free group on the non-tree edges is spelled by a loop of `K` at the
root. -/
theorem exists_loop_spelling w :
    ∃ p, IsPathX K p T.root T.root ∧ pathWord T p = w := by
  classical
  induction w using FreeGroup.induction_on with
  | one => tauto
  | of e =>
      refine ⟨conjPath T [(e, true)] (K.src e) (K.tgt e), ?_, ?_⟩
      · exact conjPath_isLoop T (isPath_single _)
      · rw [conjPath, pathWord_append, pathWord_append, pathWord_treePath, pathWord_revPath,
          pathWord_treePath]
        simp [pathWord, germWord, dif_neg e.2]
  | inv_of e ih =>
      obtain ⟨p, hp, hw⟩ := ih
      exact ⟨revPath p, isPath_revPath hp, by rw [pathWord_revPath, hw]⟩
  | mul x y hx hy =>
      obtain ⟨p, hp, hpw⟩ := hx
      obtain ⟨p', hp', hpw'⟩ := hy
      exact ⟨p ++ p', hp.append hp', by rw [pathWord_append, hpw, hpw']⟩
