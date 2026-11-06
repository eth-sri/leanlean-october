import Mathlib.Tactic

import RequestProject.SpanningTree
import RequestProject.PresentationDictionary

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

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.SpanningTree




variable {K : Complex2.{u}} (T : SpanningTree K)

/-! ### The word spelled by an edge path -/

/-- The edges of `K` outside the spanning tree: the generators of the presentation. -/
abbrev NonTree (T : SpanningTree K)  := {e : K.E // ¬ T.isTree e}

variable (g : K.E × Bool)
open Classical in
/-- The letter contributed by an oriented edge: nothing for a tree edge, the generator (or its
inverse) for an edge outside the tree. -/
noncomputable def germWord   :=
  if h : T.isTree g.1 then 1 else
    if g.2 then FreeGroup.of (⟨g.1, h⟩ : NonTree T) else (FreeGroup.of (⟨g.1, h⟩ : NonTree T))⁻¹

/-- The word in the non-tree edges spelled by an edge path. -/
noncomputable def pathWord (l : List (K.E × Bool))  :=
  (l.map (germWord T)).prod

variable (f : K.F)
/-- The relator of a two-cell: the word spelled by its attaching path. -/
noncomputable def treeRel   := pathWord T (K.att f)

@[simp] theorem pathWord_nil : pathWord T [] = 1 := rfl

theorem pathWord_cons  (l : List (K.E × Bool)) :
    pathWord T (g :: l) = germWord T g * pathWord T l := by
  simp [pathWord]

theorem pathWord_append (l l' : List (K.E × Bool)) :
    pathWord T (l ++ l') = pathWord T l * pathWord T l' := by
  simp [pathWord]

theorem germWord_revGerm  :
    germWord T (revGerm g) = (germWord T g)⁻¹ := by
  aesop (add simp [germWord, revGerm])

theorem pathWord_revPath (l : List (K.E × Bool)) :
    pathWord T (revPath l) = (pathWord T l)⁻¹ := by
  induction l <;> simp_all [germWord_revGerm, pathWord]

variable {g : K.E × Bool}
theorem germWord_of_isTree  (h : T.isTree g.1) : germWord T g = 1 := by
  simp [germWord, h]

variable {l : List (K.E × Bool)}
theorem pathWord_eq_one_of_tree  (hl : ∀ g ∈ l, T.isTree g.1) :
    pathWord T l = 1 := by
  induction l <;> simp_all [pathWord_cons, germWord_of_isTree]

variable (a : K.V)
/-- Tree paths spell the empty word. -/
@[simp] abbrev pathWord_treePath   :=
  pathWord_eq_one_of_tree T (fun _ hg => T.isTree_of_mem_treePath a hg)

/-! ### From edge loops to the presented group -/

/-- The class of the word spelled by an edge path, in the presented group. -/
noncomputable def wordClass (l : List (K.E × Bool)) : PresGroup (treeRel T) :=
  QuotientGroup.mk (pathWord T l)

theorem wordClass_append (l l' : List (K.E × Bool)) :
    wordClass T (l ++ l') = wordClass T l * wordClass T l' := by
  simp_all [wordClass, pathWord_append]

theorem wordClass_att  : wordClass T (K.att f) = 1 := by
  rw [show wordClass T (K.att f) = QuotientGroup.mk (treeRel T f) from rfl,
    QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure ⟨f, rfl⟩

theorem wordClass_cancels {l l' : List (K.E × Bool)} (h : Cancels K l l') :
    wordClass T l = wordClass T l' := by
  rcases h with ⟨p, q, g, hl, hl'⟩ | ⟨p, q, f, hl, hl'⟩
  · subst hl; subst hl'
    rw [wordClass_append, wordClass_append]
    congr 1
    show QuotientGroup.mk (pathWord T (g :: revGerm g :: q)) = QuotientGroup.mk (pathWord T q)
    rw [pathWord_cons, pathWord_cons, germWord_revGerm]
    group
  · simp_all [wordClass_append, wordClass_att]

variable {a b : K.V}
theorem wordClass_htpy  {l l' : List (K.E × Bool)} (h : Htpy K a b l l') :
    wordClass T l = wordClass T l' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rcases hstep with hs | hs
      · exact ih.trans (wordClass_cancels T hs.2.2)
      · exact ih.trans (wordClass_cancels T hs.2.2).symm

/-- The homomorphism `π₁(K) → ⟨E ∖ T | r⟩` reading off the word spelled by an edge loop. -/
noncomputable def pi1ToPres : Pi1 K T.root →* PresGroup (treeRel T) where
  toFun := Quotient.lift (fun p => wordClass T p.1) (fun _ _ h => wordClass_htpy T h)
  map_one' := rfl
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    exact wordClass_append T p.1 q.1



/-! ### From the presented group to edge loops -/

/-- The loop obtained from a path by prefixing and suffixing tree paths. -/
noncomputable def conjPath (l : List (K.E × Bool)) (a b : K.V)  :=
  T.treePath a ++ l ++ revPath (T.treePath b)

variable (hl : IsPath K.src K.tgt l a b)
abbrev conjPath_isLoop  
      :=
  isPath_append_iff.mpr ⟨b, isPath_append_iff.mpr ⟨a, T.treePath_isPath a, hl⟩,
    isPath_revPath (T.treePath_isPath b)⟩

/-- The class in `π₁(K, root)` of a path, conjugated into a loop by the tree paths. -/
noncomputable def loopOf  
      :=
  Pi1.mk ⟨conjPath T l a b, conjPath_isLoop T hl⟩

@[simp] theorem loopOf_nil  :
    loopOf T (l := []) (a := a) (b := a) rfl = 1 := by
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T [] a a) []
  simpa [conjPath] using htpy_append_revPath (T.treePath_isPath a)

/-- Concatenation of paths corresponds to multiplication of their classes. -/
theorem loopOf_mul {p q : List (K.E × Bool)} {a m b : K.V}
    (hp : IsPath K.src K.tgt p a m) (hq : IsPath K.src K.tgt q m b) :
    loopOf T hp * loopOf T hq = loopOf T (hp.append hq) := by
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T p a m ++ conjPath T q m b) (conjPath T (p ++ q) a b)
  have hcancel  :=
    htpy_revPath_append (T.treePath_isPath m)
  have hleft  :=
    isPath_append_iff.mpr ⟨a, T.treePath_isPath a, hp⟩
  have hright  :=
    isPath_append_iff.mpr ⟨b, hq, isPath_revPath (T.treePath_isPath b)⟩
  have hmain := hcancel.congr_append hleft hright
  simp_all [conjPath]

/-- Reversing a path inverts its class. -/
theorem loopOf_rev    :
    loopOf T (isPath_revPath hl) = (loopOf T hl)⁻¹ := by
  refine Quotient.sound ?_
  simp_all [conjPath, revPath_append]



variable (e : NonTree T)
/-- The loop of a single non-tree edge: the generator of the presentation. -/
noncomputable def genLoop   :=
  loopOf T (isPath_single ((e : K.E), true))

/-- The homomorphism from the free group on the non-tree edges to `π₁(K)`. -/
noncomputable def freeToPi1  :=
  FreeGroup.lift (genLoop T)

@[simp] theorem freeToPi1_of  :
    freeToPi1 T (FreeGroup.of e) = genLoop T e := by
  simp [freeToPi1]

/-- A tree edge, traversed from the vertex towards the root, gives the trivial class. -/
theorem loopOf_up {a : K.V} (ha : a ≠ T.root) :
    loopOf T (isPath_single (T.up a ha)) = 1 := by
  set u := T.up a ha with hu
  set m := T.parent a ha with hm
  have hsrc  := T.up_src a ha
  have htgt : germTgt K.src K.tgt u = m := rfl
  have hpar : T.treePath a = T.treePath m ++ [revGerm u] := T.treePath_of_ne ha
  refine Quotient.sound ?_
  show Htpy K T.root T.root
    (conjPath T [u] (germSrc K.src K.tgt u) (germTgt K.src K.tgt u)) []
  have hrw : conjPath T [u] (germSrc K.src K.tgt u) (germTgt K.src K.tgt u) =
      (T.treePath m ++ [revGerm u, u]) ++ revPath (T.treePath m) := by
    rw [conjPath, hsrc, htgt, hpar]
    simp
  rw [hrw]
  have hpath : IsPath K.src K.tgt [revGerm u, u] m m := by
    simp_all
  have hstep : Htpy K m m [revGerm u, u] [] := by
    refine Htpy.of_step ⟨hpath, rfl, Or.inl ⟨[], [], revGerm u, ?_, rfl⟩⟩
    simp
  have hbig := hstep.congr_append (T.treePath_isPath m) (isPath_revPath (T.treePath_isPath m))
  refine hbig.trans ?_
  simpa using htpy_append_revPath (T.treePath_isPath m)

/-- A tree edge, traversed in either direction, gives the trivial class. -/
theorem loopOf_single_eq_one_of_isTree  (hg : T.isTree g.1) :
    loopOf T (isPath_single g) = 1 := by
  classical
  obtain ⟨a, ha, hae⟩ := (T.isTree_iff g.1).1 hg
  by_cases hb : g.2 = (T.up a ha).2
  · aesop (add simp [loopOf_up])
  · have hgeq : g = revGerm (T.up a ha) := by
      refine Prod.ext hae.symm ?_
      show g.2 = !(T.up a ha).2
      cases hg2 : g.2 <;> cases hu2 : (T.up a ha).2 <;> simp_all
    subst hgeq
    have h := loopOf_rev T (isPath_single (T.up a ha))
    aesop (add unsafe apply [loopOf_up])

theorem freeToPi1_germWord  :
    freeToPi1 T (germWord T g) = loopOf T (isPath_single g) := by
  by_cases h : T.isTree g.1
  · simp_all [germWord_of_isTree, loopOf_single_eq_one_of_isTree]
  · obtain ⟨e, b⟩ := g
    cases b
    · have hgw : germWord T (e, false) = (FreeGroup.of (⟨e, h⟩ : NonTree T))⁻¹ := by
        simp [germWord, h]
      rw [hgw, map_inv, freeToPi1_of, genLoop]
      have h1 := loopOf_rev T (isPath_single ((e, true) : K.E × Bool))
      rw [← h1]
      all_goals rfl
    · simp_all [germWord, genLoop]

/-- **The image of an arbitrary edge path**: the free group element it spells is sent to the
class of the path, conjugated into a loop by the tree paths. -/
theorem freeToPi1_pathWord  
     :
    freeToPi1 T (pathWord T l) = loopOf T hl := by
  induction l generalizing a with
  | nil =>
      cases hl
      simp [pathWord]
  | cons g l ih =>
      obtain ⟨ha, hrest⟩ := hl
      grind [pathWord_cons, freeToPi1_germWord, loopOf_mul]

theorem freeToPi1_treeRel  : freeToPi1 T (treeRel T f) = 1 := by
  have hf := K.att_isLoop f
  rw [show treeRel T f = pathWord T (K.att f) from rfl, freeToPi1_pathWord T hf]
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T (K.att f) (K.base f) (K.base f)) []
  have hstep : Htpy K (K.base f) (K.base f) (K.att f) [] :=
    Htpy.of_step ⟨hf, rfl, Or.inr ⟨[], [], f, by simp, rfl⟩⟩
  have hbig := hstep.congr_append (T.treePath_isPath (K.base f))
    (isPath_revPath (T.treePath_isPath (K.base f)))
  rw [conjPath]
  refine hbig.trans ?_
  simpa using htpy_append_revPath (T.treePath_isPath (K.base f))

theorem relSub_le_ker_freeToPi1 : relSub (treeRel T) ≤ (freeToPi1 T).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨f, rfl⟩
  exact freeToPi1_treeRel T f

/-- The homomorphism `⟨E ∖ T | r⟩ → π₁(K)`. -/
noncomputable def presToPi1  :=
  QuotientGroup.lift (relSub (treeRel T)) (freeToPi1 T)
    (fun _ hx => relSub_le_ker_freeToPi1 T hx)

@[simp] theorem presToPi1_mk (w : FreeGroup (NonTree T)) :
    presToPi1 T (QuotientGroup.mk w) = freeToPi1 T w := rfl

/-! ### The isomorphism -/

theorem presToPi1_pi1ToPres (x : Pi1 K T.root) : presToPi1 T (pi1ToPres T x) = x := by
  induction x using Quotient.inductionOn with
  | h p =>
      obtain ⟨l, hl⟩ := p
      show presToPi1 T (wordClass T l) = Pi1.mk ⟨l, hl⟩
      rw [show wordClass T l = QuotientGroup.mk (pathWord T l) from rfl, presToPi1_mk,
        freeToPi1_pathWord T hl]
      refine Quotient.sound ?_
      simp_all [conjPath]

theorem pi1ToPres_presToPi1 (g : PresGroup (treeRel T)) :
    pi1ToPres T (presToPi1 T g) = g := by
  induction g using QuotientGroup.induction_on with
  | H w =>
      rw [presToPi1_mk]
      induction w using FreeGroup.induction_on with
      | one => simp
      | of e =>
          rw [freeToPi1_of, genLoop]
          show wordClass T (conjPath T [((e : K.E), true)] _ _) = _
          rw [conjPath, wordClass_append, wordClass_append]
          have h1 : wordClass T (T.treePath (germSrc K.src K.tgt ((e : K.E), true))) = 1 := by
            simp [wordClass]
          have h2 : wordClass T
              (revPath (T.treePath (germTgt K.src K.tgt ((e : K.E), true)))) = 1 := by
            simp [wordClass, pathWord_revPath]
          rw [h1, h2, one_mul, mul_one]
          show QuotientGroup.mk (pathWord T [((e : K.E), true)]) = _
          aesop (add simp [pathWord, germWord])
      | inv_of e ih =>
          simp_all
      | mul x y hx hy =>
          simp_all

/-- **The fundamental group of a two-complex is presented by the non-tree edges and the
attaching words.**  For any spanning tree `T` of the one-skeleton, `π₁(K, root)` is isomorphic
to `⟨E ∖ T | the attaching words of the two-cells, with the tree letters deleted⟩`. -/
noncomputable def pi1EquivPres : Pi1 K T.root ≃* PresGroup (treeRel T) where
  toFun := pi1ToPres T
  invFun := presToPi1 T
  left_inv := presToPi1_pi1ToPres T
  right_inv := pi1ToPres_presToPi1 T
  map_mul' := (pi1ToPres T).map_mul

end FiniteChains.Comb.SpanningTree


