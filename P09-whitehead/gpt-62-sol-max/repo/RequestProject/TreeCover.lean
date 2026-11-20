module

public import RequestProject.TreeVoltage
public import RequestProject.CoverComplex

@[expose] public section

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


namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)
variable (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]

/-- The deck group of the cover: the presented group of the collapse modulo `N`. -/
abbrev CovQ : Type u := FreeGroup (NonTree T) ⧸ N

/-- The translation of the cover attached to an oriented edge: trivial for a tree edge, the
class of the generator otherwise. -/
noncomputable def germQ (g : K.E × Bool) : CovQ T N := QuotientGroup.mk (germWord T g)

/-- The translation attached to an edge path. -/
noncomputable def wordQ (p : List (K.E × Bool)) : CovQ T N :=
  QuotientGroup.mk (pathWord T p)

variable {T N}

@[simp] theorem wordQ_nil : wordQ T N ([] : List (K.E × Bool)) = 1 := rfl

theorem wordQ_cons (g : K.E × Bool) (p : List (K.E × Bool)) :
    wordQ T N (g :: p) = germQ T N g * wordQ T N p := rfl

theorem wordQ_append (p p' : List (K.E × Bool)) :
    wordQ T N (p ++ p') = wordQ T N p * wordQ T N p' := by
  unfold wordQ
  rw [pathWord_append, QuotientGroup.mk_mul]

theorem germQ_revGerm (g : K.E × Bool) : germQ T N (revGerm g) = (germQ T N g)⁻¹ := by
  unfold germQ
  rw [germWord_revGerm, QuotientGroup.mk_inv]

theorem germQ_false_eq_inv (e : K.E) :
    germQ T N (e, false) = (germQ T N (e, true))⁻¹ := by
  simpa [revGerm] using germQ_revGerm (T := T) (N := N) (e, true)

@[simp] theorem wordQ_treePath (a : K.V) : wordQ T N (T.treePath a) = 1 := by
  unfold wordQ
  simp

variable (T N)

/-! ### The vertices, the edges and their endpoints -/

abbrev covSrc : CovQ T N × K.E → CovQ T N × K.V := TreeVoltage.src

noncomputable abbrev covTgt := TreeVoltage.tgt T (QuotientGroup.mk' N)

noncomputable abbrev liftGerm := TreeVoltage.liftGerm T (QuotientGroup.mk' N)

noncomputable abbrev liftK := TreeVoltage.liftPath T (QuotientGroup.mk' N)

variable {T N}

@[simp] theorem liftK_cons (g : K.E × Bool) (L : List (K.E × Bool)) (q : CovQ T N) :
    liftK T N (g :: L) q = liftGerm T N q g :: liftK T N L (q * germQ T N g) := rfl

/-- The projection of a lifted path is the path itself. -/
theorem map_liftK (L : List (K.E × Bool)) (q : CovQ T N) :
    (liftK T N L q).map (fun eb => (eb.1.2, eb.2)) = L :=
  TreeVoltage.liftPath_projection T (QuotientGroup.mk' N) L q

/-- The lifted path ends on the sheet specified by its tree word. -/
theorem liftK_isPath {L : List (K.E × Bool)} {a b : K.V} (hL : IsPath K.src K.tgt L a b)
    (q : CovQ T N) :
    IsPath (covSrc T N) (covTgt T N) (liftK T N L q) (q, a) (q * wordQ T N L, b) :=
  TreeVoltage.liftPath_isPath T (QuotientGroup.mk' N) hL q

/-! ### The cover -/

variable (T N)

theorem treeCover_word (hN : ∀ f, treeRel T f ∈ N) (f : K.F) :
    wordQ T N (K.att f) = 1 := (QuotientGroup.eq_one_iff _).2 (hN f)

/-- The cover attached to a normal subgroup containing the attaching words. -/
noncomputable def treeCover (hN : ∀ f, treeRel T f ∈ N) : Complex2.{u} :=
  TreeVoltage.cover T (QuotientGroup.mk' N) (treeCover_word T N hN)

variable {T N}

@[simp] theorem treeCover_src (hN : ∀ f, treeRel T f ∈ N) (x : CovQ T N × K.E) :
    (treeCover T N hN).src x = covSrc T N x := rfl

@[simp] theorem treeCover_tgt (hN : ∀ f, treeRel T f ∈ N) (x : CovQ T N × K.E) :
    (treeCover T N hN).tgt x = covTgt T N x := rfl

variable (T N)

/-- The projection of the cover onto `K`. -/
noncomputable def treeCoverProj (hN : ∀ f, treeRel T f ∈ N) : Hom (treeCover T N hN) K :=
  TreeVoltage.projection T (QuotientGroup.mk' N) (treeCover_word T N hN)

/-! ### Connectedness -/

/-- Every element of the free group on the non-tree edges is spelled by a loop of `K` at the
root. -/
theorem exists_loop_spelling (w : FreeGroup (NonTree T)) :
    ∃ p : List (K.E × Bool), IsPath K.src K.tgt p T.root T.root ∧ pathWord T p = w := by
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

end SpanningTree
end Comb
end FiniteChains
