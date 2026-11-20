module

public import RequestProject.SpanningTree
public import RequestProject.PresentationDictionary

@[expose] public section

/-!
# The presentation of `π₁` read off a spanning tree

Let `K` be a combinatorial two-complex and `T` a spanning tree of its one-skeleton
(`RequestProject/SpanningTree.lean`).  Collapsing `T` turns `K` into a presentation complex,
whose generators are the edges outside the tree and whose relators are the attaching words of
the two-cells with the tree letters deleted.  This file proves the group-theoretic half of
that statement, without any finiteness assumption:

* `FiniteChains.Comb.SpanningTree.NonTree` — the edges outside the tree;
* `FiniteChains.Comb.SpanningTree.pathWord` — the word in the non-tree edges spelled by an edge
  path (tree letters are deleted; this is the retraction `F(E) → F(E ∖ T)`);
* `FiniteChains.Comb.SpanningTree.treeRel` — the relator of a two-cell;
* `FiniteChains.Comb.SpanningTree.pi1EquivPres` — **the fundamental group of `K` at the root is
  the group presented by `⟨E ∖ T | attaching words⟩`**.

The proof is the classical one.  One homomorphism reads off the word spelled by an edge loop;
it is well defined because a backtrack spells a trivial word and an attaching path spells a
relator.  The other sends a non-tree edge `e` to the loop "tree path to the source of `e`, then
`e`, then back along the tree path from the target"; the verification that the relators die is
`freeToPi1_pathWord`, which computes the image of an arbitrary path.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)

/-! ### The word spelled by an edge path -/

/-- The edges of `K` outside the spanning tree: the generators of the presentation. -/
abbrev NonTree (T : SpanningTree K) := {e : K.E // ¬ T.isTree e}

open Classical in
/-- The letter contributed by an oriented edge: nothing for a tree edge, the generator (or its
inverse) for an edge outside the tree. -/
def germWord (g : K.E × Bool) :=
  if h : T.isTree g.1 then 1 else
    if g.2 then FreeGroup.of (⟨g.1, h⟩) else (FreeGroup.of (⟨g.1, h⟩ : NonTree T))⁻¹

/-- The word in the non-tree edges spelled by an edge path. -/
def pathWord (l : List _) :=
  (l.map (germWord T)).prod

/-- The relator of a two-cell: the word spelled by its attaching path. -/
def treeRel (f : K.F) := pathWord T (K.att f)

@[simp] theorem pathWord_nil : pathWord T [] = 1 := rfl

theorem pathWord_cons (g : K.E × Bool) (l : List _) :
    pathWord T (g :: l) = germWord T g * pathWord T l := rfl

theorem pathWord_append (l l' : List _) :
    pathWord T (l ++ l') = pathWord T l * pathWord T l' := by
  simp [pathWord]

theorem germWord_revGerm (g : K.E × Bool) :
    germWord T (revGerm g) = (germWord T g)⁻¹ := by
  classical
  obtain ⟨e, b⟩ := g
  by_cases h : T.isTree e
  · simp [germWord, revGerm, h]
  · cases b <;> simp [germWord, revGerm, h]

theorem pathWord_revPath (l : List _) :
    pathWord T (revPath l) = (pathWord T l)⁻¹ := by
  induction l <;> simp_all [revPath_cons, pathWord_append, pathWord_cons, germWord_revGerm]

theorem germWord_of_isTree {g : K.E × Bool} (h : T.isTree g.1) : germWord T g = 1 := by
  simp [germWord, h]

theorem pathWord_eq_one_of_tree {l : List _} (hl : ∀ g ∈ l, T.isTree g.1) :
    pathWord T l = 1 := by
  induction l <;> simp_all [pathWord_cons, germWord_of_isTree]

/-- Tree paths spell the empty word. -/
@[simp] theorem pathWord_treePath (a : K.V) : pathWord T (T.treePath a) = 1 :=
  pathWord_eq_one_of_tree T (fun _ hg => T.isTree_of_mem_treePath a hg)

/-! ### From edge loops to the presented group -/

/-- The class of the word spelled by an edge path, in the presented group. -/
def wordClass (l : List (K.E × Bool)) : PresGroup (treeRel T) :=
  QuotientGroup.mk (pathWord T l)

theorem wordClass_append (l l' : List _) :
    wordClass T (l ++ l') = wordClass T l * wordClass T l' := by
  unfold wordClass
  solve_by_elim [pathWord_append]

theorem wordClass_att (f : K.F) : wordClass T (K.att f) = 1 := by
  simp [show wordClass T _ = QuotientGroup.mk (treeRel T f) from rfl]
  exact Subgroup.subset_normalClosure ⟨f, rfl⟩

theorem wordClass_cancels {l l' : List _} (h : Cancels K l l') :
    wordClass T l = wordClass T l' := by
  rcases h with ⟨p, q, g, hl, hl'⟩ | ⟨p, q, f, hl, hl'⟩
  · subst hl; subst hl'
    rw [wordClass_append, wordClass_append]
    congr 1
    show QuotientGroup.mk (pathWord T _) = QuotientGroup.mk (pathWord T q)
    simp [pathWord_cons, germWord_revGerm]
  · simp_all [wordClass_append, wordClass_att]

theorem wordClass_htpy {a b : K.V} {l l' : List _} (h : Htpy K a b l l') :
    wordClass T l = wordClass T l' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rcases hstep with hs | hs
      · exact ih.trans (wordClass_cancels T hs.2.2)
      · exact ih.trans (wordClass_cancels T hs.2.2).symm

/-- The homomorphism `π₁(K) → ⟨E ∖ T | r⟩` reading off the word spelled by an edge loop. -/
def pi1ToPres : Pi1 K T.root →* PresGroup (treeRel T) where
  toFun := Quotient.lift _ (fun _ _ h => wordClass_htpy T h)
  map_one' := rfl
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    apply wordClass_append

@[simp] theorem pi1ToPres_mk (p : Loop K T.root) :
    pi1ToPres T (Pi1.mk p) = wordClass T p.1 := rfl

/-! ### From the presented group to edge loops -/

/-- The loop obtained from a path by prefixing and suffixing tree paths. -/
def conjPath (l : List _) (a b : K.V) :=
  T.treePath a ++ l ++ revPath (T.treePath b)

section

variable {l : List (K.E × Bool)} {a b : K.V} (hl : IsPath K.src K.tgt l a b)
include hl

theorem conjPath_isLoop :
    IsPath K.src K.tgt (conjPath T l a b) T.root T.root :=
  isPath_append_iff.mpr ⟨b, isPath_append_iff.mpr ⟨a, T.treePath_isPath a, hl⟩,
    isPath_revPath (T.treePath_isPath b)⟩

/-- The class in `π₁(K, root)` of a path, conjugated into a loop by the tree paths. -/
def loopOf :=
  Pi1.mk ⟨conjPath T l a b, conjPath_isLoop T hl⟩

end

@[simp] theorem loopOf_nil (a : K.V) :
    loopOf T (l := []) (b := a) rfl = 1 := by
  refine Quotient.sound ?_
  show Htpy K T.root T.root _ []
  simpa [conjPath] using htpy_append_revPath (T.treePath_isPath a)

/-- Concatenation of paths corresponds to multiplication of their classes. -/
theorem loopOf_mul {p q : List _} {a m b : K.V}
    (hp : IsPath K.src K.tgt p a m) (hq : IsPath K.src K.tgt q m b) :
    loopOf T hp * loopOf T hq = loopOf T (hp.append hq) := by
  refine Quotient.sound ?_
  show Htpy K T.root T.root _ _
  have hmain := (htpy_revPath_append (T.treePath_isPath m)).congr_append (isPath_append_iff.mpr ⟨a, T.treePath_isPath a, hp⟩) (isPath_append_iff.mpr ⟨b, hq, isPath_revPath (T.treePath_isPath b)⟩)
  simp_all [conjPath]

/-- Reversing a path inverts its class. -/
theorem loopOf_rev {l : List _} {a b : K.V} (hl : IsPath K.src K.tgt l a b) :
    loopOf T (isPath_revPath hl) = (loopOf T hl)⁻¹ := by
  refine Quotient.sound ?_
  show Htpy K T.root T.root _ (revPath (conjPath T l a b))
  have hrw : revPath (conjPath T l a b) = conjPath T (revPath l) b a := by
    simp [conjPath, revPath_append]
  rw [hrw]
  exact Htpy.refl _

/-- `loopOf` depends only on the path and its endpoints. -/
theorem loopOf_eq {l l' : List _} {a b a' b' : K.V}
    (hl : IsPath K.src K.tgt l a b) (hl' : IsPath K.src K.tgt l' a' b')
    (hll : l = l') (ha : a = a') (hb : b = b') : loopOf T hl = loopOf T hl' := by
  simp_all

/-- The loop of a single non-tree edge: the generator of the presentation. -/
def genLoop (e : NonTree T) :=
  loopOf T (isPath_single (e, true))

/-- The homomorphism from the free group on the non-tree edges to `π₁(K)`. -/
def freeToPi1 :=
  FreeGroup.lift (genLoop T)

@[simp] theorem freeToPi1_of (e : NonTree T) :
    freeToPi1 T (FreeGroup.of e) = genLoop T e := by
  simp [freeToPi1]

/-- A tree edge, traversed from the vertex towards the root, gives the trivial class. -/
theorem loopOf_up {a : K.V} (ha : a ≠ T.root) :
    loopOf T (isPath_single (T.up a ha)) = 1 := by
  set u := T.up a ha with hu
  set m := T.parent a ha with hm
  have htgt : germTgt K.src K.tgt u = m := rfl
  have hpar : T.treePath a = T.treePath m ++ [revGerm u] := T.treePath_of_ne ha
  refine Quotient.sound ?_
  show Htpy K T.root T.root
    (conjPath T [u] (germSrc K.src K.tgt u) (germTgt K.src K.tgt u)) []
  have hrw : conjPath T [u] (germSrc K.src K.tgt u) (germTgt K.src K.tgt u) =
      (T.treePath m ++ [revGerm u, u]) ++ revPath (T.treePath m) := by
    rw [conjPath, (T.up_src a ha), htgt, hpar]
    simp
  rw [hrw]
  have hpath : IsPath K.src K.tgt [revGerm u, u] m m := by
    refine ⟨?_, ?_, ?_⟩
    · simp_all
    · simp
    · exact htgt
  have hstep : Htpy K m m [revGerm u, u] [] := by
    refine Htpy.of_step ⟨hpath, rfl, Or.inl ⟨[], [], revGerm u, ?_, rfl⟩⟩
    simp
  refine (hstep.congr_append (T.treePath_isPath m) (isPath_revPath (T.treePath_isPath m))).trans ?_
  simpa using htpy_append_revPath (T.treePath_isPath m)

/-- A tree edge, traversed in either direction, gives the trivial class. -/
theorem loopOf_single_eq_one_of_isTree {g : K.E × Bool} (hg : T.isTree g.1) :
    loopOf T (isPath_single g) = 1 := by
  classical
  obtain ⟨a, ha, hae⟩ := (T.isTree_iff g.1).1 hg
  by_cases hb : g.2 = (T.up a ha).2
  · grind [loopOf_up]
  · have hgeq : g = revGerm (T.up a ha) := by
      refine Prod.ext hae.symm ?_
      show g.2 = !(T.up a ha).2
      grind
    have h := loopOf_rev T (isPath_single (T.up a ha))
    simp_all [loopOf_up]

theorem freeToPi1_germWord (g : K.E × Bool) :
    freeToPi1 T (germWord T g) = loopOf T (isPath_single g) := by
  classical
  by_cases h : T.isTree g.1
  · simp_all [germWord_of_isTree, loopOf_single_eq_one_of_isTree]
  · obtain ⟨e, b⟩ := g
    cases b
    · have hgw : germWord T (e, false) = (FreeGroup.of (⟨e, h⟩))⁻¹ := by
        simp [germWord, h]
      simp [hgw, genLoop]
      have h1 := loopOf_rev T (isPath_single ((e, true)))
      simp_all
    · have hgw : germWord T (e, true) = FreeGroup.of (⟨e, h⟩) := by
        simp [germWord, h]
      aesop

/-- **The image of an arbitrary edge path**: the free group element it spells is sent to the
class of the path, conjugated into a loop by the tree paths. -/
theorem freeToPi1_pathWord {l : List _} {a b : K.V}
    (hl : IsPath K.src K.tgt l a b) :
    freeToPi1 T (pathWord T l) = loopOf T hl := by
  induction l generalizing a with
  | nil =>
      cases hl
      simp
  | cons g l ih =>
      obtain ⟨ha, hrest⟩ := hl
      grind [pathWord_cons, freeToPi1_germWord, loopOf_mul]

theorem freeToPi1_treeRel (f : K.F) : freeToPi1 T (treeRel T f) = 1 := by
  have hf := K.att_isLoop f
  rw [show treeRel T f = pathWord T _ from rfl, freeToPi1_pathWord T hf]
  refine Quotient.sound ?_
  have hstep : Htpy K _ _ _ [] :=
    Htpy.of_step ⟨hf, rfl, Or.inr ⟨[], [], f, by simp, rfl⟩⟩
  let isPath := T.treePath_isPath (K.base f)
  have hbig := hstep.congr_append isPath
    (isPath_revPath isPath)
  refine hbig.trans ?_; simpa using htpy_append_revPath isPath

theorem relSub_le_ker_freeToPi1 : relSub (treeRel T) ≤ (freeToPi1 T).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨f, rfl⟩
  exact freeToPi1_treeRel T f

/-- The homomorphism `⟨E ∖ T | r⟩ → π₁(K)`. -/
def presToPi1 :=
  QuotientGroup.lift _ _
    (fun _ hx => relSub_le_ker_freeToPi1 T hx)

@[simp] theorem presToPi1_mk (w : FreeGroup _) :
    presToPi1 T (QuotientGroup.mk w) = freeToPi1 T w := rfl

/-! ### The isomorphism -/

theorem presToPi1_pi1ToPres (x : Pi1 K T.root) : presToPi1 T (pi1ToPres T x) = x := by
  induction x using Quotient.inductionOn with
  | h p =>
      obtain ⟨l, hl⟩ := p
      show presToPi1 T (wordClass T l) = Pi1.mk _
      simp [show wordClass T l = QuotientGroup.mk (pathWord T l) from rfl, presToPi1_mk, freeToPi1_pathWord T hl]
      refine Quotient.sound ?_
      simp [conjPath]

theorem pi1ToPres_presToPi1 (g : PresGroup _) :
    pi1ToPres T (presToPi1 T g) = g := by
  induction g using QuotientGroup.induction_on with
  | H w =>
      simp
      induction w using FreeGroup.induction_on with
      | of e =>
          rw [freeToPi1_of, genLoop]
          show wordClass T (conjPath T [(e, true)] _ _) = _
          rw [conjPath, wordClass_append, wordClass_append]
          have h1 : wordClass T (T.treePath (germSrc K.src K.tgt (e, true))) = 1 := by
            simp [wordClass]
          have h2 : wordClass T
              (revPath (T.treePath (germTgt K.src K.tgt (e, true)))) = 1 := by
            simp [wordClass, pathWord_revPath]
          rw [h1, h2, one_mul, mul_one]
          show QuotientGroup.mk (pathWord T _) = _
          have hw : pathWord T [(e, true)] = FreeGroup.of e := by
            classical
            simp [pathWord, germWord, dif_neg e.2]
          simp_all
      | _ => simp_all

/-- **The fundamental group of a two-complex is presented by the non-tree edges and the
attaching words.**  For any spanning tree `T` of the one-skeleton, `π₁(K, root)` is isomorphic
to `⟨E ∖ T | the attaching words of the two-cells, with the tree letters deleted⟩`. -/
def pi1EquivPres : Pi1 K T.root ≃* PresGroup (treeRel T) where
  toFun := pi1ToPres T
  invFun := presToPi1 T
  left_inv := presToPi1_pi1ToPres T
  right_inv := pi1ToPres_presToPi1 T
  map_mul' := (pi1ToPres T).map_mul

end SpanningTree
end Comb
end FiniteChains
