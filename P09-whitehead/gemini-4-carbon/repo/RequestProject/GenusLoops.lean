module

public import RequestProject.CombPi1
public import RequestProject.PresPosetReading
public import Mathlib

@[expose] public section
noncomputable section
namespace FiniteChains
namespace Comb

universe u

variable {K : Complex2.{u}}

/-- A **spanning tree** of the one-skeleton of a combinatorial two-complex, described by the
data used in the collapse: a root, a height function vanishing exactly at the root, and for
every non-root vertex `a` an oriented edge `up a` starting at `a` and ending one step lower.
The predicate `isTree` marks the edges used, and the last axiom says that these are exactly
the edges `up a`. -/
structure SpanningTree (K : Complex2.{u}) where
  /-- The base vertex. -/
  root : K.V
  /-- The distance to the root. -/
  ht : K.V → ℕ
  /-- The edges of the tree. -/
  isTree : K.E → Prop
  /-- The oriented edge from a non-root vertex towards the root. -/
  up : ∀ a : K.V, a ≠ root → K.E × Bool
  /-- The root has height zero. -/
  ht_root : ht root = 0
  /-- Only the root has height zero. -/
  ht_eq_zero : ∀ a, ht a = 0 → a = root
  /-- `up a` starts at `a`. -/
  up_src : ∀ (a : K.V) (ha : a ≠ root), germSrc K.src K.tgt (up a ha) = a
  /-- `up a` ends one step closer to the root. -/
  up_ht : ∀ (a : K.V) (ha : a ≠ root), ht (germTgt K.src K.tgt (up a ha)) + 1 = ht a
  /-- The tree edges are exactly the edges `up a`, `a ≠ root`. -/
  isTree_iff : ∀ e, isTree e ↔ ∃ (a : K.V) (ha : a ≠ root), (up a ha).1 = e

namespace SpanningTree

variable (T : SpanningTree K)

/-- The parent of a non-root vertex: the other endpoint of its tree edge. -/
def parent (a : K.V) (ha : a ≠ T.root) : K.V := germTgt K.src K.tgt (T.up a ha)

theorem ht_parent {a : K.V} (ha : a ≠ T.root) : T.ht (T.parent a ha) + 1 = T.ht a :=
  T.up_ht a ha

theorem isTree_up {a : K.V} (ha : a ≠ T.root) : T.isTree (T.up a ha).1 :=
  (T.isTree_iff _).2 ⟨a, ha, rfl⟩

open Classical in
/-- The tree path from the root to a vertex. -/
def treePath (T : SpanningTree K) (a : K.V) : List (K.E × Bool) :=
  if h : a = T.root then [] else
    treePath T (T.parent a h) ++ [revGerm (T.up a h)]
  termination_by T.ht a
  decreasing_by
    have h' := T.ht_parent h
    omega

@[simp] theorem treePath_root : T.treePath T.root = [] := by
  rw [treePath]
  simp

theorem treePath_of_ne {a : K.V} (ha : a ≠ T.root) :
    T.treePath a = T.treePath (T.parent a ha) ++ [revGerm (T.up a ha)] := by
  rw [treePath]
  simp [ha]

/-- The tree path from the root to `a` is an edge path from the root to `a`. -/
theorem treePath_isPath (a : K.V) : IsPath K.src K.tgt (T.treePath a) T.root a := by
  induction hn : T.ht a using Nat.strong_induction_on generalizing a with
  | _ n ih =>
      by_cases ha : a = T.root
      · subst ha
        simp
      · have hp  := T.ht_parent ha
        have hlt : T.ht (T.parent a ha) < n := by omega
        have hrest := ih _ hlt (T.parent a ha) rfl
        rw [T.treePath_of_ne ha]
        refine isPath_append_iff.mpr ⟨T.parent a ha, hrest, ?_⟩
        have h1 : germSrc K.src K.tgt (revGerm (T.up a ha)) = T.parent a ha := by
          simp [parent]
        have h2 : germTgt K.src K.tgt (revGerm (T.up a ha)) = a := by
          simpa using T.up_src a ha
        exact ⟨h1.symm, by simp [h2]⟩

/-- Every edge of a tree path is a tree edge. -/
theorem isTree_of_mem_treePath (a : K.V) {g : K.E × Bool} (hg : g ∈ T.treePath a) :
    T.isTree g.1 := by
  induction hn : T.ht a using Nat.strong_induction_on generalizing a g with
  | _ n ih =>
      by_cases ha : a = T.root
      · simp_all
      · have hp  := T.ht_parent ha
        have hlt : T.ht (T.parent a ha) < n := by omega
        rw [T.treePath_of_ne ha, List.mem_append] at hg
        rcases hg with hg | hg
        · exact ih _ hlt (a := T.parent a ha) hg rfl
        · simp at hg
          subst hg
          exact T.isTree_up ha

/-! ### Existence -/

section Existence

/-- The lengths of edge paths from a fixed vertex. -/
def reach (K : Complex2.{u}) (r a : K.V) : Set ℕ := {n | ∃ p : List (K.E × Bool),
  p.length = n ∧ IsPath K.src K.tgt p r a}


/-- **Every connected two-complex has a spanning tree**, rooted at any prescribed vertex. -/
theorem exists_of_isConnected (hconn : IsConnected K) (r : K.V) :
    ∃ T : SpanningTree K, T.root = r := by
  set d : K.V → ℕ := fun a => sInf (reach K r a) with hd
  have hmem : ∀ a, d a ∈ reach K r a := fun a =>
    Nat.sInf_mem (by
      obtain ⟨p, hp⟩ := hconn r a
      exact ⟨p.length, p, rfl, hp⟩)
  have hle : ∀ a p, IsPath K.src K.tgt p r a → d a ≤ p.length :=
    fun a p hp => Nat.sInf_le ⟨p, rfl, hp⟩
  have hd_root  := Nat.le_antisymm (hle r [] rfl) (Nat.zero_le _)
  have hd_eq_zero : ∀ a, d a = 0 → a = r := by
    intro a ha
    obtain ⟨p, hlen, hp⟩ := hmem a
    rw [ha, List.length_eq_zero_iff] at hlen
    subst hlen
    exact hp.symm
  have hstep : ∀ a : K.V, a ≠ r → ∃ g : K.E × Bool,
      germSrc K.src K.tgt g = a ∧ d (germTgt K.src K.tgt g) + 1 = d a := by
    intro a ha
    obtain ⟨p, hlen, hp⟩ := hmem a
    have hne : p ≠ [] := by
      intro h
      subst h
      exact ha (hd_eq_zero a (by simpa using hlen.symm))
    obtain ⟨q, g, rfl⟩ : ∃ q g, p = q ++ [g] :=
      ⟨p.dropLast, p.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    obtain ⟨m, hq, hg⟩ := isPath_append_iff.1 hp
    have hgs : germSrc K.src K.tgt g = m := hg.1.symm
    have hgt : germTgt K.src K.tgt g = a := by
      have := hg.2
      simpa using this
    refine ⟨revGerm g, by simpa using hgt, ?_⟩
    have h1 : d m ≤ q.length := hle m q hq
    have h2 : d a ≤ d m + 1 := by
      obtain ⟨q', hlen', hq'⟩ := hmem m
      have hpath : IsPath K.src K.tgt (q' ++ [g]) r a :=
        isPath_append_iff.mpr ⟨m, hq', hg⟩
      have := hle a _ hpath
      simpa [hlen'] using this
    have h3 : q.length + 1 = d a := by
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have hmt : germTgt K.src K.tgt (revGerm g) = m := by simpa using hgs
    rw [hmt]
    omega
  choose upg hupsrc hupht using hstep
  exact ⟨{ root := r
           ht := d
           isTree := fun e => ∃ a ha, (upg a ha).1 = e
           up := upg
           ht_root := hd_root
           ht_eq_zero := hd_eq_zero
           up_src := hupsrc
           up_ht := hupht
           isTree_iff := fun _ => Iff.rfl }, rfl⟩

end Existence

end SpanningTree
end Comb
end FiniteChains

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)

/-! ### The word spelled by an edge path -/

/-- The edges of `K` outside the spanning tree: the generators of the presentation. -/
abbrev NonTree (T : SpanningTree K) : Type u := {e : K.E // ¬ T.isTree e}

open Classical in
/-- The letter contributed by an oriented edge: nothing for a tree edge, the generator (or its
inverse) for an edge outside the tree. -/
def germWord (g : K.E × Bool) : FreeGroup (NonTree T) :=
  if h : T.isTree g.1 then 1 else
    if g.2 then FreeGroup.of (⟨g.1, h⟩ : NonTree T) else (FreeGroup.of (⟨g.1, h⟩ : NonTree T))⁻¹

/-- The word in the non-tree edges spelled by an edge path. -/
def pathWord (l : List (K.E × Bool)) : FreeGroup (NonTree T) :=
  (l.map (germWord T)).prod

/-- The relator of a two-cell: the word spelled by its attaching path. -/
def treeRel (f : K.F) : FreeGroup (NonTree T) := pathWord T (K.att f)

@[simp] theorem pathWord_nil : pathWord T [] = 1 := rfl

theorem pathWord_cons (g : K.E × Bool) (l : List (K.E × Bool)) :
    pathWord T (g :: l) = germWord T g * pathWord T l := rfl

theorem pathWord_append (l l' : List (K.E × Bool)) :
    pathWord T (l ++ l') = pathWord T l * pathWord T l' := by
  simp [pathWord, List.prod_append]

theorem germWord_revGerm (g : K.E × Bool) :
    germWord T (revGerm g) = (germWord T g)⁻¹ := by
  obtain ⟨e, b⟩ := g
  by_cases h : T.isTree e
  · simp [germWord, revGerm, h]
  · cases b <;> simp [germWord, revGerm, h]

theorem pathWord_revPath (l : List (K.E × Bool)) :
    pathWord T (revPath l) = (pathWord T l)⁻¹ := by
  induction l with
  | nil => rfl
  | cons g l ih =>
      rw [revPath_cons, pathWord_append, ih, pathWord_cons, germWord_revGerm]
      simp [pathWord]

theorem germWord_of_isTree {g : K.E × Bool} (h : T.isTree g.1) : germWord T g = 1 := by
  simp [germWord, h]

theorem pathWord_eq_one_of_tree {l : List (K.E × Bool)} (hl : ∀ g ∈ l, T.isTree g.1) :
    pathWord T l = 1 := by
  induction l with
  | nil => simp
  | cons g l ih =>
      rw [pathWord_cons, germWord_of_isTree T (hl g (by simp)), one_mul]
      exact ih (fun g' hg' => hl g' (by simp [hg']))

/-- Tree paths spell the empty word. -/
@[simp] theorem pathWord_treePath (a : K.V) : pathWord T (T.treePath a) = 1 :=
  pathWord_eq_one_of_tree T (fun _ hg => T.isTree_of_mem_treePath a hg)

/-! ### From edge loops to the presented group -/

/-- The class of the word spelled by an edge path, in the presented group. -/
def wordClass (l : List (K.E × Bool)) : PresGroup (treeRel T) :=
  QuotientGroup.mk (pathWord T l)

theorem wordClass_append (l l' : List (K.E × Bool)) :
    wordClass T (l ++ l') = wordClass T l * wordClass T l' := by
  unfold wordClass
  rw [pathWord_append, QuotientGroup.mk_mul]


theorem wordClass_cancels {l l' : List (K.E × Bool)} (h : Cancels K l l') :
    wordClass T l = wordClass T l' := by
  rcases h with ⟨p, q, g, hl, hl'⟩ | ⟨p, q, f, hl, hl'⟩
  · subst hl; subst hl'
    rw [wordClass_append, wordClass_append]
    congr 1
    show QuotientGroup.mk (pathWord T (g :: revGerm g :: q)) = QuotientGroup.mk (pathWord T q)
    rw [pathWord_cons, pathWord_cons, germWord_revGerm]
    group
  · subst hl; subst hl'
    rw [wordClass_append, wordClass_append, wordClass_append, (show wordClass T (K.att f) = 1 by
      rw [show wordClass T (K.att f) = QuotientGroup.mk (treeRel T f) from rfl,
        QuotientGroup.eq_one_iff]
      exact Subgroup.subset_normalClosure ⟨f, rfl⟩), mul_one]

theorem wordClass_htpy {a b : K.V} {l l' : List (K.E × Bool)} (h : Htpy K a b l l') :
    wordClass T l = wordClass T l' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rcases hstep with hs | hs
      · exact ih.trans (wordClass_cancels T hs.2.2)
      · exact ih.trans (wordClass_cancels T hs.2.2).symm

/-- The homomorphism `π₁(K) → ⟨E ∖ T | r⟩` reading off the word spelled by an edge loop. -/
def pi1ToPres : Pi1 K T.root →* PresGroup (treeRel T) where
  toFun := Quotient.lift (fun p => wordClass T p.1) (fun _ _ h => wordClass_htpy T h)
  map_one' := rfl
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    exact wordClass_append T p.1 q.1

@[simp] theorem pi1ToPres_mk (p : Loop K T.root) :
    pi1ToPres T (Pi1.mk p) = wordClass T p.1 := rfl

/-! ### From the presented group to edge loops -/

/-- The loop obtained from a path by prefixing and suffixing tree paths. -/
def conjPath (l : List (K.E × Bool)) (a b : K.V) : List (K.E × Bool) :=
  T.treePath a ++ l ++ revPath (T.treePath b)

theorem conjPath_isLoop {l : List (K.E × Bool)} {a b : K.V}
    (hl : IsPath K.src K.tgt l a b) :
    IsPath K.src K.tgt (conjPath T l a b) T.root T.root :=
  isPath_append_iff.mpr ⟨b, isPath_append_iff.mpr ⟨a, T.treePath_isPath a, hl⟩,
    isPath_revPath (T.treePath_isPath b)⟩

/-- The class in `π₁(K, root)` of a path, conjugated into a loop by the tree paths. -/
def loopOf {l : List (K.E × Bool)} {a b : K.V}
    (hl : IsPath K.src K.tgt l a b) : Pi1 K T.root :=
  Pi1.mk ⟨conjPath T l a b, conjPath_isLoop T hl⟩

@[simp] theorem loopOf_nil (a : K.V) :
    loopOf T (l := []) (a := a) (b := a) rfl = 1 := by
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T [] a a) []
  simpa [conjPath] using htpy_append_revPath (T.treePath_isPath a)

/-- Concatenation of paths corresponds to multiplication of their classes. -/
theorem loopOf_mul {p q : List (K.E × Bool)} {a m b : K.V}
    (hp : IsPath K.src K.tgt p a m) (hq : IsPath K.src K.tgt q m b) :
    loopOf T hp * loopOf T hq = loopOf T (hp.append hq) := by
  refine Quotient.sound ?_
  have hcancel  :=
    htpy_revPath_append (T.treePath_isPath m)
  have hleft  :=
    isPath_append_iff.mpr ⟨a, T.treePath_isPath a, hp⟩
  have hright  :=
    isPath_append_iff.mpr ⟨b, hq, isPath_revPath (T.treePath_isPath b)⟩
  have hmain := hcancel.congr_append hleft hright
  have hrw₁ : (T.treePath a ++ p) ++ (revPath (T.treePath m) ++ T.treePath m) ++
      (q ++ revPath (T.treePath b)) = conjPath T p a m ++ conjPath T q m b := by
    simp [conjPath, List.append_assoc]
  have hrw₂ : (T.treePath a ++ p) ++ [] ++
      (q ++ revPath (T.treePath b)) = conjPath T (p ++ q) a b := by
    simp [conjPath, List.append_assoc]
  rw [hrw₁, hrw₂] at hmain
  exact hmain

/-- Reversing a path inverts its class. -/
theorem loopOf_rev {l : List (K.E × Bool)} {a b : K.V} (hl : IsPath K.src K.tgt l a b) :
    loopOf T (isPath_revPath hl) = (loopOf T hl)⁻¹ := by
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T (revPath l) b a) (revPath (conjPath T l a b))
  have hrw : revPath (conjPath T l a b) = conjPath T (revPath l) b a := by
    simp [conjPath, revPath_append, List.append_assoc, revPath_revPath]
  rw [hrw]
  exact Htpy.refl _

/-- `loopOf` depends only on the path and its endpoints. -/
theorem loopOf_eq {l l' : List (K.E × Bool)} {a b a' b' : K.V}
    (hl : IsPath K.src K.tgt l a b) (hl' : IsPath K.src K.tgt l' a' b')
    (hll : l = l') (ha : a = a') (hb : b = b') : loopOf T hl = loopOf T hl' := by simp_all

/-- The loop of a single non-tree edge: the generator of the presentation. -/
def genLoop (e : NonTree T) : Pi1 K T.root :=
  loopOf T (isPath_single ((e : K.E), true))

/-- The homomorphism from the free group on the non-tree edges to `π₁(K)`. -/
def freeToPi1 : FreeGroup (NonTree T) →* Pi1 K T.root :=
  FreeGroup.lift (genLoop T)

@[simp] theorem freeToPi1_of (e : NonTree T) :
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
    refine ⟨?_, ?_, ?_⟩
    · simp_all
    · simp
    · exact htgt
  have hstep : Htpy K m m [revGerm u, u] [] := by
    refine Htpy.of_step ⟨hpath, rfl, Or.inl ⟨[], [], revGerm u, ?_, rfl⟩⟩
    simp
  have hbig := hstep.congr_append (T.treePath_isPath m) (isPath_revPath (T.treePath_isPath m))
  refine hbig.trans ?_
  simpa using htpy_append_revPath (T.treePath_isPath m)

/-- A tree edge, traversed in either direction, gives the trivial class. -/
theorem loopOf_single_eq_one_of_isTree {g : K.E × Bool} (hg : T.isTree g.1) :
    loopOf T (isPath_single g) = 1 := by
  obtain ⟨a, ha, hae⟩ := (T.isTree_iff g.1).1 hg
  by_cases hb : g.2 = (T.up a ha).2
  · have hgeq  := Prod.ext hae.symm hb
    subst hgeq
    exact loopOf_up T ha
  · have hgeq : g = revGerm (T.up a ha) := by
      refine Prod.ext hae.symm ?_
      show g.2 = !(T.up a ha).2
      cases hg2 : g.2 <;> cases hu2 : (T.up a ha).2 <;> simp_all
    subst hgeq
    have h := loopOf_rev T (isPath_single (T.up a ha))
    rw [loopOf_up T ha, inv_one] at h
    rw [loopOf_eq T (isPath_single (revGerm (T.up a ha)))
      (isPath_revPath (isPath_single (T.up a ha))) (by simp [revPath]) (by simp) (by simp)]
    exact h


/-- **The image of an arbitrary edge path**: the free group element it spells is sent to the
class of the path, conjugated into a loop by the tree paths. -/
theorem freeToPi1_pathWord {l : List (K.E × Bool)} {a b : K.V}
    (hl : IsPath K.src K.tgt l a b) :
    freeToPi1 T (pathWord T l) = loopOf T hl := by
  induction l generalizing a with
  | nil =>
      cases hl
      simp [pathWord]
  | cons g l ih =>
      obtain ⟨ha, hrest⟩ := hl
      subst ha
      rw [pathWord_cons, map_mul, (show freeToPi1 T (germWord T g) = loopOf T (isPath_single g) by
        by_cases h : T.isTree g.1
        · rw [germWord_of_isTree T h, map_one, loopOf_single_eq_one_of_isTree T h]
        · obtain ⟨e, b⟩ := g
          cases b
          · have hgw : germWord T (e, false) = (FreeGroup.of ⟨e, h⟩)⁻¹ := by
              simp [germWord, h]
            rw [hgw, map_inv, freeToPi1_of, genLoop]
            have h1 := loopOf_rev T (isPath_single (e, true))
            rw [← h1]
            all_goals rfl
          · have hgw : germWord T (e, true) = FreeGroup.of ⟨e, h⟩ := by
              simp [germWord, h]
            rw [hgw, freeToPi1_of, genLoop]), ih hrest]
      exact loopOf_mul T (isPath_single g) hrest

theorem freeToPi1_treeRel (f : K.F) : freeToPi1 T (treeRel T f) = 1 := by
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
def presToPi1 : PresGroup (treeRel T) →* Pi1 K T.root :=
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
      show Htpy K T.root T.root (conjPath T l T.root T.root) l
      simpa [conjPath] using Htpy.refl l

theorem pi1ToPres_presToPi1 (g : PresGroup (treeRel T)) :
    pi1ToPres T (presToPi1 T g) = g := by
  induction g using QuotientGroup.induction_on with
  | H w =>
      rw [presToPi1_mk]
      induction w using FreeGroup.induction_on with
      | one => simp
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
          show QuotientGroup.mk (pathWord T [(e, true)]) = _
          have hw : pathWord T [(e, true)] = FreeGroup.of e := by
            simp [pathWord, germWord, dif_neg e.2]
          rw [hw]
      | inv_of e ih => simp_all
      | mul x y hx hy => simp_all

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

namespace FiniteChains
namespace Davis

open RACG Mirror

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- **The marked mirror `(F_s)_w`** of the chamber `F_w`: the cells of `F_w` whose mirror type
contains the generator `s`. -/
def MarkedMirror (w : CayGroup A) (s : V) (p : Sph A) : Prop :=
  InChamber w p ∧ s ∈ p.spx

/-- **`J_w = ⋃_{s ∈ D(w)} (F_s)_w`**: the union of the *descending* marked mirrors of the
chamber `F_w`. -/
def JSet (w : CayGroup A) (p : Sph A) : Prop :=
  ∃ s ∈ rdescFinset A w, MarkedMirror w s p

theorem jSet_iff {w : CayGroup A} {p : Sph A} :
    JSet w p ↔ (InChamber w p ∧ (p.spx ∩ rdescFinset A w).Nonempty) := by
  constructor
  · rintro ⟨s, hs, hp, hsp⟩
    exact ⟨hp, ⟨s, Finset.mem_inter.2 ⟨hsp, hs⟩⟩⟩
  · rintro ⟨hp, s, hs⟩
    obtain ⟨hsp, hsd⟩ := Finset.mem_inter.1 hs
    exact ⟨s, hsd, hp, hsp⟩

/-- **The corrected intersection formula.**  For a cell of the chamber `F_w`, lying in some
other chamber `F_v` with `ℓ(v) ≤ ℓ(w)` — ties included — is equivalent to lying in
`J_w = ⋃_{s ∈ D(w)} (F_s)_w`.  So
`F_w ∩ ⋃_{v earlier} F_v = J_w`, *not* the whole outer boundary. -/
theorem mem_earlier_chamber_iff_jSet {w : CayGroup A} {p : Sph A} (hp : InChamber w p) :
    (∃ v : CayGroup A, v ≠ w ∧ RACG.clen A v ≤ RACG.clen A w ∧ InChamber v p) ↔ JSet w p := by grind [jSet_iff, mem_earlier_chamber_iff, JSet]

/-- The same formula with strictly shorter chambers. -/
theorem mem_shorter_chamber_iff_jSet {w : CayGroup A} {p : Sph A} (hp : InChamber w p) :
    (∃ v : CayGroup A, RACG.clen A v < RACG.clen A w ∧ InChamber v p) ↔ JSet w p := by grind [jSet_iff, mem_shorter_chamber_iff, JSet]

/-! ### The apex of a chamber -/

omit [Fintype V] in
theorem specialSub_empty : specialSub A (∅ : Set V) = ⊥ := by
  rw [specialSub, Set.image_empty, Subgroup.closure_empty]

omit [Fintype V] in
/-- The apex of the chamber `F_g` is the cell `{g}`: its representative is `g` itself. -/
theorem chamberPt_empty_rep (g : CayGroup A) :
    (chamberPt g (isSimplex_empty (A := A))).rep = g := by
  have h := chamberPt_inChamber g (isSimplex_empty)
  have h1 : (chamberPt g (isSimplex_empty)).rep⁻¹ * g ∈
      specialSub A (∅ : Finset V) := h
  rw [Finset.coe_empty, specialSub_empty, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.1 h1

/-! ### The outer boundary is strictly bigger than `J_w` -/

omit [DecidableEq V] [Fintype V] in
theorem isSimplex_singleton (s : V) : IsSimplex A {s} := by
  intro a ha b hb hab
  simp_all

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb Nerve

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V} {X : Type u} [Preorder X]

/-- The nonempty simplices of `L`, ordered by inclusion: the domain of the attaching map.  The
attaching map is **not** required to be defined on the empty simplex: the cone point of a
chamber is exactly what is removed.

The domain consists of the nonempty **simplices** of `L` and not of all nonempty finite sets of
vertices: the order complex of the latter poset is a cone (any finite family of finite sets has
an upper bound, namely their union), so an attaching map defined on it would be null-homotopic
on every loop of the boundary of a chamber and could never realise a nontrivial attaching word.
This is `FiniteChains.Davis.pi1_trivial_of_directed_domain` in
`RequestProject/ChamberAttachingTrivial.lean`. -/
abbrev NeSpx (A : CommRel V) : Type u := {σ : Finset V // σ.Nonempty ∧ IsSimplex A σ}

/-- A cell of the model is a **marked apex** if it is the apex `{w}` of a chamber that is to be
modified. -/
def IsMarkedApex (M : CayGroup A → Prop) (p : Sph A) : Prop := p.spx = ∅ ∧ M p.rep

/-- The cells of the model that are retained: everything but the marked apexes. -/
def Zold (A : CommRel V) (M : CayGroup A → Prop) : Type u := {p : Sph A // ¬ IsMarkedApex M p}

/-- The adjoined copies of the base poset, one for each marked chamber. -/
def Znew (A : CommRel V) (M : CayGroup A → Prop) (X : Type u) : Type u :=
  {w : CayGroup A // M w} × X

/-- **The poset `Z` of modified chambers.** -/
def Zpos (A : CommRel V) (X : Type u) [Preorder X] (M : CayGroup A → Prop)
    (_att : NeSpx A →o X) : Type u :=
  Zold A M ⊕ Znew A M X

variable {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-- The old cells of `Z`. -/
def zOld (p : Sph A) (hp : ¬ IsMarkedApex M p) : Zpos A X M att := Sum.inl ⟨p, hp⟩

/-- The new cells of `Z`: the elements of the copy of `X` replacing the apex of the chamber
`F_w`. -/
def zNew (w : {w : CayGroup A // M w}) (x : X) : Zpos A X M att := Sum.inr (w, x)

/-- The order of `Z`. -/
protected def Zle : Zpos A X M att → Zpos A X M att → Prop
  | Sum.inl p, Sum.inl q => p.1 ≤ q.1
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr wx, Sum.inl q =>
      InChamber wx.1.1 q.1 ∧ ∃ h : q.1.spx.Nonempty, wx.2 ≤ att ⟨q.1.spx, h, q.1.isSimplex⟩
  | Sum.inr wx, Sum.inr vy => wx.1 = vy.1 ∧ wx.2 ≤ vy.2

instance zposPreorder : Preorder (Zpos A X M att) where
  le := Davis.Zle
  le_refl z := by
    cases z with
    | inl p => exact le_refl p.1
    | inr wx => exact ⟨rfl, le_refl wx.2⟩
  le_trans z z' z'' hzz' hz'z'' := by
    cases z with
    | inl p =>
        cases z' with
        | inl q =>
            cases z'' with
            | inl r => exact le_trans hzz' hz'z''
            | inr wy => exact hz'z''.elim
        | inr wy => exact hzz'.elim
    | inr wx =>
        cases z' with
        | inl q =>
            cases z'' with
            | inl r =>
                obtain ⟨hne, hx⟩ := hzz'.2
                refine ⟨inChamber_of_le hz'z'' hzz'.1,
                  Finset.Nonempty.mono hz'z''.1 hne, ?_⟩
                exact le_trans hx (att.monotone (show (⟨q.1.spx, hne, q.1.isSimplex⟩ : NeSpx A) ≤
                  ⟨r.1.spx, Finset.Nonempty.mono hz'z''.1 hne, r.1.isSimplex⟩ from hz'z''.1))
            | inr wy => exact hz'z''.elim
        | inr wy =>
            cases z'' with
            | inl r =>
                obtain ⟨hne, hy⟩ := hz'z''.2
                exact ⟨hzz'.1 ▸ hz'z''.1, hne, le_trans hzz'.2 hy⟩
            | inr wz =>
                exact ⟨hzz'.1.trans hz'z''.1, le_trans hzz'.2 hz'z''.2⟩



/-! ### The chambers of `Z` -/

/-- **The chambers of `Z`.**  For a marked `w` this is the modified chamber (the copy of `X`
together with the outer face poset `B_w`); for an unmarked `w` it is the ordinary chamber. -/
def InZChamber (w : CayGroup A) : Zpos A X M att → Prop
  | Sum.inl p => InChamber w p.1
  | Sum.inr vx => vx.1.1 = w

/-- The old cells of the chamber of a marked `w` all have nonempty type: the apex was removed. -/
theorem spx_nonempty_of_marked {w : CayGroup A} (hw : M w) {p : Sph A}
    (hp : ¬ IsMarkedApex M p) (hpw : InChamber w p) : p.spx.Nonempty := by
  rcases Finset.eq_empty_or_nonempty p.spx with hemp | hne
  · refine absurd ?_ hp
    refine ⟨hemp, ?_⟩
    have h1 : p.rep⁻¹ * w ∈ specialSub A p.spx := hpw
    rw [hemp, Finset.coe_empty, specialSub_empty, Subgroup.mem_bot] at h1
    rw [inv_mul_eq_one.1 h1]
    exact hw
  · exact hne

/-- **Every chamber of `Z` is upward closed.** -/
theorem inZChamber_of_le {w : CayGroup A} {z z' : Zpos A X M att}
    (h : z ≤ z') (hz : InZChamber w z) : InZChamber w z' := by
  cases z with
  | inl p =>
      cases z' with
      | inl q => exact inChamber_of_le h hz
      | inr wy => exact h.elim
  | inr wx =>
      cases z' with
      | inl q =>
          rw [← hz]
          exact h.1
      | inr wy =>
          show wy.1.1 = w
          rw [← hz, h.1]

/-- Every element of `Z` lies in a chamber. -/
theorem exists_inZChamber (z : Zpos A X M att) : ∃ w : CayGroup A, InZChamber w z := by
  cases z with
  | inl p => exact ⟨p.1.rep, inChamber_rep p.1⟩
  | inr wx => exact ⟨wx.1.1, rfl⟩

/-! ### Intersections of chambers -/

/-- **A new cell lies in only one chamber.** -/
theorem eq_of_inZChamber_new {w v : CayGroup A} {u : {w : CayGroup A // M w}} {x : X}
    (hw : InZChamber (att := att) w (zNew u x)) (hv : InZChamber (att := att) v (zNew u x)) :
    w = v := by
  rw [← hw, ← hv]

section Fintype

variable [Fintype V]

/-- **The attaching subcomplex of the chamber of `w` inside `Z`**: the old cells of `J_w`.  The
new cells — the copy of `X` — never belong to it. -/
def ZJSet (w : CayGroup A) : Zpos A X M att → Prop
  | Sum.inl p => JSet w p.1
  | Sum.inr _ => False

theorem zJSet_imp_inZChamber {w : CayGroup A} {z : Zpos A X M att} (h : ZJSet w z) :
    InZChamber w z := by
  cases z with
  | inl p => exact h.choose_spec.2.1
  | inr wx => exact h.elim

/-- **The attaching intersection of a chamber of `Z`.**  A cell of the chamber of `w` lies in
some other chamber of `Z` of length at most that of `w` exactly when it is an old cell of
`J_w = ⋃_{s ∈ D(w)} (F_s)_w`.  In particular the new cells — the copy of `X` — are attached
along nothing but `J_w`, and the intersection is the already-studied contractible subcomplex. -/
theorem mem_earlier_zchamber_iff {w : CayGroup A} {z : Zpos A X M att} (hz : InZChamber w z) :
    (∃ v : CayGroup A, v ≠ w ∧ RACG.clen A v ≤ RACG.clen A w ∧ InZChamber v z) ↔ ZJSet w z := by
  cases z with
  | inl p =>
      constructor
      · rintro ⟨v, hvw, hlen, hv⟩
        exact (mem_earlier_chamber_iff_jSet hz).1 ⟨v, hvw, hlen, hv⟩
      · intro hJ
        exact (mem_earlier_chamber_iff_jSet hz).2 hJ
  | inr wx =>
      constructor
      · rintro ⟨v, hvw, -, hv⟩
        exact absurd (eq_of_inZChamber_new hv hz) hvw
      · intro h
        exact h.elim

/-- The same intersection formula with strictly shorter chambers. -/
theorem mem_shorter_zchamber_iff {w : CayGroup A} {z : Zpos A X M att} (hz : InZChamber w z) :
    (∃ v : CayGroup A, RACG.clen A v < RACG.clen A w ∧ InZChamber v z) ↔ ZJSet w z := by
  cases z with
  | inl p =>
      constructor
      · rintro ⟨v, hlen, hv⟩
        exact (mem_shorter_chamber_iff_jSet hz).1 ⟨v, hlen, hv⟩
      · intro hJ
        exact (mem_shorter_chamber_iff_jSet hz).2 hJ
  | inr wx =>
      constructor
      · rintro ⟨v, hlen, hv⟩
        have : v = w := eq_of_inZChamber_new hv hz
        subst this
        omega
      · intro h
        exact h.elim

end Fintype

/-! ### Collapsing the copies of the base -/

/-! ### The modified chamber is the mapping cylinder of `att` -/

section ModifiedChamber

variable (M att) (w : CayGroup A)

/-- The modified chamber of `w`, as a subposet of `Z`. -/
abbrev ZChamber : Type u := {z : Zpos A X M att // InZChamber w z}

variable {M att w}

/-- The retraction of the modified chamber onto its copy of `X`: an old cell of type `σ` goes to
`att σ`, a new cell stays where it is. -/
def zChamberRetr (hw : M w) : ZChamber M att w → ZChamber M att w := fun z =>
  match z with
  | ⟨Sum.inl p, hp⟩ =>
      ⟨zNew ⟨w, hw⟩ (att ⟨p.1.spx, spx_nonempty_of_marked hw p.2 hp, p.1.isSimplex⟩), rfl⟩
  | ⟨Sum.inr wx, hwx⟩ => ⟨Sum.inr wx, hwx⟩

/-- The retraction lands in the copy of `X`. -/
theorem zChamberRetr_mem (hw : M w) (z : ZChamber M att w) :
    ∃ x : X, (zChamberRetr hw z).1 = zNew (att := att) ⟨w, hw⟩ x := by
  rcases z with ⟨p | ⟨u, x⟩, hz⟩
  · exact ⟨att ⟨p.1.spx, spx_nonempty_of_marked hw p.2 hz, p.1.isSimplex⟩, rfl⟩
  · refine ⟨x, ?_⟩
    show Sum.inr (u, x) = Sum.inr (⟨w, hw⟩, x)
    have hu : u = ⟨w, hw⟩ := Subtype.ext hz
    rw [hu]

/-- **The retraction lies below the identity**: this is the mapping cylinder identity `i r ≤ id`
of the chosen orientation, and it turns the prism operator into a chain homotopy. -/
theorem zChamberRetr_le (hw : M w) (z : ZChamber M att w) : zChamberRetr hw z ≤ z := by
  rcases z with ⟨p | wx, hz⟩
  · exact ⟨hz, spx_nonempty_of_marked hw p.2 hz, le_refl _⟩
  · rfl

/-- The retraction is monotone. -/
theorem zChamberRetr_monotone (hw : M w) :
    Monotone (zChamberRetr (att := att) hw) := by
  rintro ⟨p | ⟨u, x⟩, hz⟩ ⟨q | ⟨v, y⟩, hz'⟩ h
  · exact ⟨rfl, att.monotone (show (⟨p.1.spx, spx_nonempty_of_marked hw p.2 hz,
      p.1.isSimplex⟩ : NeSpx A) ≤
      ⟨q.1.spx, spx_nonempty_of_marked hw q.2 hz', q.1.isSimplex⟩ from h.1)⟩
  · exact h.elim
  · obtain ⟨hne, hx⟩ := h.2
    exact ⟨Subtype.ext hz, hx⟩
  · exact h

end ModifiedChamber

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb Nerve

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V} {X : Type u} [Preorder X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-- **The base subcomplex of `Z`**: the union of the adjoined copies of the base poset. -/
def InZBase : Zpos A X M att → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

/-! ### Ordinary chambers -/

omit [Fintype V] in
theorem not_isMarkedApex_apex {w : CayGroup A} (hw : ¬ M w) :
    ¬ IsMarkedApex M (chamberPt w (isSimplex_empty (A := A))) := by
  rintro ⟨-, h⟩
  rw [chamberPt_empty_rep] at h
  exact hw h

/-- The apex of an unmarked chamber, as a cell of `Z`. -/
def zApex {w : CayGroup A} (hw : ¬ M w) : Zpos A X M att :=
  zOld (chamberPt w (isSimplex_empty (A := A))) (not_isMarkedApex_apex hw)

omit [Fintype V] in
theorem inZChamber_zApex {w : CayGroup A} (hw : ¬ M w) :
    InZChamber w (zApex (X := X) (att := att) hw) :=
  chamberPt_inChamber w (isSimplex_empty (A := A))

omit [Fintype V] in
/-- The apex is the least cell of an unmarked chamber. -/
theorem zApex_le {w : CayGroup A} (hw : ¬ M w) {z : Zpos A X M att} (hz : InZChamber w z) :
    zApex (X := X) (att := att) hw ≤ z := by
  cases z with
  | inl p =>
      exact le_of_inChamber (chamberPt_inChamber w (isSimplex_empty)) hz
        (Finset.empty_subset _)
  | inr wx =>
      exact absurd (hz ▸ wx.1.2) hw

/-! ### Modified chambers -/

/-! ### The attaching intersection -/

/-- The attaching subcomplex of the chamber of `w` inside `Z` is the attaching subcomplex of the
chamber `F_w` of the Davis poset. -/
def zJSetOrderIso (w : CayGroup A) :
    {z : Zpos A X M att // ZJSet w z} ≃o ChamberInter A w where
  toFun z :=
    match z with
    | ⟨Sum.inl p, h⟩ => ⟨p.1, (jSet_iff.1 h).1, (jSet_iff.1 h).2⟩
    | ⟨Sum.inr _, h⟩ => h.elim
  invFun q :=
    ⟨zOld q.1 (by
        rintro ⟨hemp, -⟩
        obtain ⟨s, hs⟩ := q.2.2
        rw [hemp] at hs
        simp at hs),
      show JSet w q.1 from jSet_iff.2 ⟨q.2.1, q.2.2⟩⟩
  left_inv z := by
    rcases z with ⟨p | wx, h⟩
    · rfl
    · exact h.elim
  right_inv q := rfl
  map_rel_iff' {z z'} := by
    rcases z with ⟨p | wx, h⟩
    · rcases z' with ⟨q | wy, h'⟩
      · exact Iff.rfl
      · exact h'.elim
    · exact h.elim

/-! ### The filtration by word length -/

/-- The union of the chambers of `Z` of length at most `n`. -/
def ZUpto (n : ℕ) (z : Zpos A X M att) : Prop := ∃ y : CayGroup A, RACG.clen A y ≤ n ∧ InZChamber y z

omit [Fintype V] in
theorem zUpto_up {n : ℕ} {z z' : Zpos A X M att} (h : z ≤ z') (hz : ZUpto n z) : ZUpto n z' := by
  obtain ⟨y, hy, hyz⟩ := hz
  exact ⟨y, hy, inZChamber_of_le h hyz⟩

omit [Fintype V] in
theorem zUpto_zero_iff (z : Zpos A X M att) : ZUpto 0 z ↔ InZChamber (1 : CayGroup A) z := by simp_all [RACG.clen_eq_zero_iff, ZUpto]

/-! ### The whole complex -/

/-- The length of the chamber a cell of `Z` belongs to. -/
def zlen : Zpos A X M att → ℕ
  | Sum.inl p => RACG.clen A p.1.rep
  | Sum.inr wx => RACG.clen A wx.1.1

omit [Fintype V] in
theorem zUpto_zlen (z : Zpos A X M att) : ZUpto (zlen z) z := by
  cases z with
  | inl p => exact ⟨p.1.rep, le_refl _, inChamber_rep p.1⟩
  | inr wx => exact ⟨wx.1.1, le_refl _, rfl⟩

end Davis
end FiniteChains

namespace FiniteChains

open MonoidAlgebra

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The ring homomorphism of group rings induced by a map of generating sets. -/
def freeRingMap (f : α → β) : FreeGroupRing α →+* FreeGroupRing β :=
  MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map f)

omit [DecidableEq α] [DecidableEq β] in
@[simp] theorem freeRingMap_grp (f : α → β) (w : FreeGroup α) :
    freeRingMap f (grp w) = grp (FreeGroup.map f w) := MonoidAlgebra.mapDomain_single


/-- **Naturality of the Fox derivative.**  For an injective map of generating sets the
derivative of the image word with respect to the image generator is the image of the
derivative. -/
theorem fox_map (f : α → β) (hf : Function.Injective f) (i : α) (w : FreeGroup α) :
    fox (f i) (FreeGroup.map f w) = freeRingMap f (fox i w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => by_cases h : i = k <;> simp [h, hf.eq_iff]
  | inv_of k ih =>
      rw [map_inv, fox_inv, fox_inv, map_neg, map_mul, ih, freeRingMap_grp, map_inv]
  | mul u v hu hv =>
      rw [map_mul, fox_mul, fox_mul, map_add, hu, hv, map_mul, freeRingMap_grp]

omit [DecidableEq α] in
/-- The derivative of an old word with respect to a new generator vanishes. -/
theorem fox_map_of_not_mem_range (f : α → β) {b : β} (hb : ∀ i, b ≠ f i) (w : FreeGroup α) :
    fox b (FreeGroup.map f w) = 0 := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => simp_all
  | inv_of k ih => rw [map_inv, fox_inv, ih, mul_zero, neg_zero]
  | mul u v hu hv => rw [map_mul, fox_mul, hu, hv, mul_zero, add_zero]

end FiniteChains

namespace FiniteChains

/-- Infinite order is detected by any monoid homomorphism. -/
theorem not_isOfFinOrder_of_map {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {x : M}
    (h : ¬ IsOfFinOrder (f x)) : ¬ IsOfFinOrder x := by
  intro hx
  obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.1 hx
  exact h (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [← map_pow, hxn, map_one]⟩)

/-- A generator of `ℤ` has infinite order. -/
theorem not_isOfFinOrder_ofAdd_one : ¬ IsOfFinOrder (Multiplicative.ofAdd (1 : ℤ)) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  simp

section FreeProduct

variable {G : Type*} [Group G]

/-- The retraction of `G * ℤ` onto `ℤ` that kills `G`. -/
def killBase : Monoid.Coprod G (Multiplicative ℤ) →* Multiplicative ℤ :=
  Monoid.Coprod.lift 1 (MonoidHom.id _)

@[simp] theorem killBase_inl (g : G) :
    killBase (Monoid.Coprod.inl g : Monoid.Coprod G (Multiplicative ℤ)) = 1 := rfl

@[simp] theorem killBase_inr (n : Multiplicative ℤ) :
    killBase (Monoid.Coprod.inr n : Monoid.Coprod G (Multiplicative ℤ)) = n := rfl

/-- The adjoined free generator `b` of `G * ℤ`. -/
def freeGen : Monoid.Coprod G (Multiplicative ℤ) :=
  Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))

/-- **`b` has infinite order in `G * ℤ`.** -/
theorem not_isOfFinOrder_freeGen : ¬ IsOfFinOrder (freeGen (G := G)) := by
  refine not_isOfFinOrder_of_map killBase ?_
  rw [freeGen, killBase_inr]
  exact not_isOfFinOrder_ofAdd_one

/-- **`z·b` has infinite order in `G * ℤ`**, for every `z` in the old group: kill the old
group, and what is left is a generator of `ℤ`. -/
theorem not_isOfFinOrder_mul_freeGen (z : G) :
    ¬ IsOfFinOrder (Monoid.Coprod.inl z * freeGen : Monoid.Coprod G (Multiplicative ℤ)) := by
  refine not_isOfFinOrder_of_map killBase ?_
  rw [map_mul, killBase_inl, freeGen, killBase_inr, one_mul]
  exact not_isOfFinOrder_ofAdd_one

end FreeProduct

section HNN

variable {G : Type*} [Group G]

/-- An element of infinite order generates an infinite cyclic subgroup. -/
def zpowersEquivInt {x : G} (hx : ¬ IsOfFinOrder x) :
    Multiplicative ℤ ≃* Subgroup.zpowers x := by
  refine MulEquiv.ofBijective ((zpowersHom G x).codRestrict (Subgroup.zpowers x)
    (fun n => Subgroup.zpow_mem_zpowers x _)) ⟨?_, ?_⟩
  · intro a b hab
    have hval : x ^ (Multiplicative.toAdd a) = x ^ (Multiplicative.toAdd b) :=
      congrArg Subtype.val hab
    exact Multiplicative.toAdd.injective (injective_zpow_iff_not_isOfFinOrder.2 hx hval)
  · rintro ⟨g, n, rfl⟩
    exact ⟨Multiplicative.ofAdd n, rfl⟩

/-- Two infinite cyclic subgroups are isomorphic. -/
def zpowersEquivZpowers {x y : G} (hx : ¬ IsOfFinOrder x) (hy : ¬ IsOfFinOrder y) :
    Subgroup.zpowers x ≃* Subgroup.zpowers y :=
  (zpowersEquivInt hx).symm.trans (zpowersEquivInt hy)

/-- The form in which the paper uses it: an HNN extension identifying two infinite cyclic
subgroups contains the old group. -/
theorem hnn_infiniteCyclic_of_injective {x y : G} (hx : ¬ IsOfFinOrder x)
    (hy : ¬ IsOfFinOrder y) :
    Function.Injective (HNNExtension.of :
      G →* HNNExtension G (Subgroup.zpowers x) (Subgroup.zpowers y)
        (zpowersEquivZpowers hx hy)) :=
  HNNExtension.of_injective _

/-- **Rule 1 of Section 3.4.**  Adjoin a free generator `b` to `G`, and then a stable letter
conjugating `b` to `z·b`.  The associated subgroups are infinite cyclic, and the old group
`G` still embeds in the result. -/
theorem rule_one_embedding (z : G) :
    Function.Injective
      ((HNNExtension.of : Monoid.Coprod G (Multiplicative ℤ) →*
          HNNExtension (Monoid.Coprod G (Multiplicative ℤ))
            (Subgroup.zpowers (freeGen (G := G)))
            (Subgroup.zpowers (Monoid.Coprod.inl z * freeGen))
            (zpowersEquivZpowers not_isOfFinOrder_freeGen
              (not_isOfFinOrder_mul_freeGen z))).comp
        (Monoid.Coprod.inl : G →* Monoid.Coprod G (Multiplicative ℤ))) := by
  rw [MonoidHom.coe_comp]
  exact (hnn_infiniteCyclic_of_injective _ _).comp Monoid.Coprod.inl_injective

end HNN

end FiniteChains

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-! ### The parity of a word -/

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by grind

/-- The indicator vector of a generator. -/
def eVec (s : V) : V → ZMod 2 := fun v => if v = s then 1 else 0

/-- The parity vector of a word: the number of occurrences of each letter, modulo two. -/
def parList (l : List V) : V → ZMod 2 := fun v => (l.count v : ZMod 2)

@[simp] theorem parList_nil : parList ([] : List V) = fun _ => 0 := rfl

@[simp] theorem parList_cons (s : V) (l : List V) :
    parList (s :: l) = eVec s + parList l := by
  funext v
  by_cases h : v = s
  · subst h
    simp [parList, eVec, add_comm]
  · simp [parList, eVec, h, Ne.symm h]


omit [DecidableEq V] in
/-- A commutation of adjacent letters permutes the word. -/
theorem Swap.perm {Cm : V → V → Prop} {l m : List V} (h : Swap Cm l m) : l.Perm m := by
  induction h with
  | head _ q => exact List.Perm.swap _ _ q
  | cons x _ ih => simp_all

theorem parList_ceq {l m : List V} (h : CEq A.rel l m) : parList l = parList m := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      refine ih.trans ?_
      funext v
      exact congrArg (Nat.cast) (Swap.perm hstep |>.count_eq v)

/-- The parity vector of a reduced trace. -/
def parTr : Tr A → V → ZMod 2 :=
  Quotient.lift (fun l : {l : List V // IsRed A.rel l} => parList l.1)
    (fun _ _ h => parList_ceq A h)

@[simp] theorem parTr_mkTr (l : List V) (h : IsRed A.rel l) :
    parTr A (mkTr A l h) = parList l := rfl

/-- An elementary move changes the parity vector by the corresponding generator. -/
theorem parTr_act (s : V) (t : Tr A) : parTr A (act A s t) = eVec s + parTr A t := by
  induction t using Quotient.inductionOn with
  | _ l =>
      by_cases hc : canStart A.rel s l.1
      · have hpop  := actRep_of_canStart A hc
        have hceq  :=
          ceq_popStart A.rel_symm hc
        have h1 : parList l.1 = eVec s + parList (popStart s l.1) := by
          rw [parList_ceq A hceq, parList_cons]
        have h2 : parTr A (act A s (Quotient.mk (redSetoid A) l)) = parList (popStart s l.1) := by
          show parList (actRep A s l).1 = _
          rw [hpop]
        rw [h2]
        show parList (popStart s l.1) = eVec s + parList l.1
        rw [h1]
        funext v
        simp only [Pi.add_apply]
        have h0 : eVec s v + eVec s v = 0 := zmod2_add_self _
        linear_combination -h0
      · have hact : (actRep A s l).1 = s :: l.1 := actRep_of_not_canStart A hc
        have h2 : parTr A (act A s (Quotient.mk (redSetoid A) l)) = parList (s :: l.1) := by
          show parList (actRep A s l).1 = _
          rw [hact]
        rw [h2, parList_cons]
        rfl

/-! ### The parity homomorphism of the group -/

/-- The parity homomorphism `W_L → (ℤ/2)^{L⁰}`: the abelianisation of the right-angled Coxeter
group, read on reduced traces. -/
def phi (x : CayGroup A) : V → ZMod 2 :=
  parTr A ((x : Equiv.Perm (Tr A)) (oneTr A))

theorem cword_append (l m : List V) : cword A (l ++ m) = cword A l * cword A m :=
  Subtype.ext (by simpa using wordPerm_append A l m)

theorem phi_cword (l : List V) : phi A (cword A l) = parList l := by
  induction l with
  | nil => rfl
  | cons s t ih =>
      have hval : ((cword A (s :: t) : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A)
          = act A s (((cword A t : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A)) := by
        rw [cword_cons]
        show (actPerm A s) _ = _
        rw [actPerm_apply]
      show parTr A _ = _
      rw [hval, parTr_act, parList_cons]
      exact congrArg (fun z => eVec s + z) ih

theorem phi_mul (x y : CayGroup A) : phi A (x * y) = phi A x + phi A y := by
  obtain ⟨l, _, rfl⟩ := exists_cword A x
  obtain ⟨m, _, rfl⟩ := exists_cword A y
  rw [← cword_append, phi_cword, phi_cword, phi_cword, (show parList (l ++ m) = parList l + parList m by
    funext v
    simp only [parList, List.count_append, Pi.add_apply, Nat.cast_add])]

/-! ### The one-skeleton of `C(L)` and the covering property -/

/-! ### The deck transformations -/

@[simp] theorem phi_one : phi A (1 : CayGroup A) = 0 := rfl

theorem phi_inv (x : CayGroup A) : phi A x⁻¹ = phi A x := by
  have h : phi A x + phi A x⁻¹ = 0 := by
    rw [← phi_mul, mul_inv_cancel, phi_one]
  funext v
  have hv : phi A x v + phi A x⁻¹ v = 0 := congrFun h v
  grind

end RACG
end FiniteChains

namespace FiniteChains

open RACG Mirror Comb

universe u

namespace RACG

variable {V : Type u} [DecidableEq V] [Fintype V] (A : CommRel V)

/-- **The parity map is onto the vertices of `C(L)`.** -/
theorem phi_surjective : Function.Surjective (phi A) := by
  intro t
  refine ⟨cword A ((Finset.univ.filter (fun s : V => t s = 1)).toList), ?_⟩
  rw [phi_cword]
  funext v
  have hcount : ((Finset.univ.filter (fun s : V => t s = 1)).toList).count v =
      if t v = 1 then 1 else 0 := by
    by_cases h : t v = 1
    · rw [if_pos h]
      rw [List.count_eq_one_of_mem (Finset.nodup_toList _)]
      simp [h]
    · rw [if_neg h]
      refine List.count_eq_zero_of_not_mem ?_
      simp [h]
  rw [parList, hcount]
  by_cases h : t v = 1
  · simp_all
  · have : t v = 0 := by
      revert h
      generalize t v = a
      revert a
      decide
    simp [this]

end RACG
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V} {X : Type u} [Preorder X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-- The inclusion of a copy of the base is monotone. -/
theorem zNew_monotone (w : {w : CayGroup A // M w}) :
    Monotone (zNew (A := A) (X := X) (M := M) (att := att) w) :=
  fun _ _ h => ⟨rfl, h⟩

end Davis
end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V} {X : Type u} [Preorder X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-! ### The copy of the base attached at a marked chamber -/

/-- The copy of the base poset glued into the modified chamber of `w`. -/
def InZBaseAt (w : CayGroup A) : Zpos A X M att → Prop
  | Sum.inl _ => False
  | Sum.inr wx => wx.1.1 = w

omit [Fintype V] in
theorem inZBaseAt_imp_inZChamber {w : CayGroup A} {z : Zpos A X M att}
    (h : InZBaseAt w z) : InZChamber w z := by
  cases z with
  | inl p => exact h.elim
  | inr wx => exact h

omit [Fintype V] in
@[simp] theorem inZBaseAt_zNew (w : {w : CayGroup A // M w}) (x : X) :
    InZBaseAt (att := att) w.1 (zNew w x) := rfl

/-- The retraction of the copy of the base onto the base poset itself. -/
def zBaseRetr (w : CayGroup A) : {z : Zpos A X M att // InZBaseAt w z} → X
  | ⟨Sum.inl _, h⟩ => h.elim
  | ⟨Sum.inr wx, _⟩ => wx.2

omit [Fintype V] in
@[simp] theorem zBaseRetr_zNew (w : {w : CayGroup A // M w}) (x : X) :
    zBaseRetr (att := att) w.1 ⟨zNew w x, inZBaseAt_zNew w x⟩ = x := rfl

omit [Fintype V] in
theorem zBaseRetr_monotone (w : CayGroup A) :
    Monotone (zBaseRetr (A := A) (X := X) (M := M) (att := att) w) := by
  rintro ⟨p | ⟨u, x⟩, hz⟩ ⟨q | ⟨v, y⟩, hz'⟩ h
  · exact hz.elim
  · exact hz.elim
  · exact hz'.elim
  · exact h.2

/-! ### The attaching intersection of a chamber of `Z` -/

/-- `J_w` inside `Z` is connected. -/
theorem connectedIn_zJSet {w : CayGroup A} (hw : w ≠ 1) :
    ConnectedIn (ZJSet (A := A) (X := X) (M := M) (att := att) w) :=
  connectedIn_of_isConnected
    (isConnected_orderCx_of_orderIso (zJSetOrderIso (X := X) (att := att) w)
      (chamberInter_isConnected hw))

/-- `J_w` inside `Z` is simply connected. -/
theorem simplyConnectedIn_zJSet {w : CayGroup A} (hw : w ≠ 1) :
    SimplyConnectedIn (ZJSet (A := A) (X := X) (M := M) (att := att) w) :=
  simplyConnectedIn_of_simplyConnected
    (simplyConnected_orderCx_of_orderIso (zJSetOrderIso (X := X) (att := att) w)
      (chamberInter_simplyConnected hw))

/-- `J_w` inside `Z` is nonempty. -/
theorem exists_zJSet {w : CayGroup A} (hw : w ≠ 1) :
    ∃ z : Zpos A X M att, ZJSet w z :=
  ⟨((zJSetOrderIso (X := X) (att := att) w).symm (interTop hw)).1,
    ((zJSetOrderIso (X := X) (att := att) w).symm (interTop hw)).2⟩

/-! ### The initial step: the modified chamber retracts onto its copy of the base -/

omit [Fintype V] in
/-- **Inside a modified chamber, the copy of the base is injective on path classes.**  This is
the monotone retraction of the mapping cylinder; it involves no extension of the attaching map
over the cone point. -/
theorem injIn_zchamber_base {w : CayGroup A} (hw : M w) :
    InjIn (InZChamber (A := A) (X := X) (M := M) (att := att) w) (InZBaseAt w) := by
  refine injIn_of_monotone_retraction (fun z hz => inZBaseAt_imp_inZChamber hz)
    (fun z => (zChamberRetr hw z).1)
    (fun z z' h => zChamberRetr_monotone hw h) ?_ ?_
  · intro z
    obtain ⟨x, hx⟩ := zChamberRetr_mem hw z
    rw [hx]
    exact rfl
  · rintro ⟨p | ⟨u, x⟩, hz⟩ hb
    · exact hb.elim
    · rfl

/-! ### The filtration by word length -/

omit [Fintype V] in
theorem inZBaseAt_imp_zUpto {w : CayGroup A} {n : ℕ} (hn : RACG.clen A w ≤ n)
    {z : Zpos A X M att} (h : InZBaseAt w z) : ZUpto n z :=
  ⟨w, hn, inZBaseAt_imp_inZChamber h⟩

/-- **One chamber of the filtration is added.** -/
theorem injIn_zupto_insert {w0 : CayGroup A} (hw0 : M w0) (n : ℕ)
    (hprev : RACG.clen A w0 ≤ n → InjIn (ZUpto (A := A) (X := X) (M := M) (att := att) n)
      (InZBaseAt w0)) :
    ∀ S : Set (CayGroup A), S.Finite → (∀ y ∈ S, RACG.clen A y = n + 1) →
      (RACG.clen A w0 ≤ n ∨ w0 ∈ S) →
      InjIn (fun z : Zpos A X M att => ZUpto n z ∨ ∃ y ∈ S, InZChamber y z) (InZBaseAt w0) := by
  intro S hS
  induction S, hS using Set.Finite.induction_on with
  | empty => simp_all
  | @insert x S hxS hSfin ih =>
      intro hlen hbase
      have hxlen  := hlen x (Set.mem_insert _ _)
      have hx1 : x ≠ 1 := by
        intro h
        rw [h, clen_one] at hxlen
        omega
      set Prev : Zpos A X M att → Prop :=
        fun z => ZUpto n z ∨ ∃ y ∈ S, InZChamber y z with hPrevDef
      have hup : ∀ z z' : Zpos A X M att, z ≤ z' → Prev z → Prev z' := by
        rintro z z' hzz' (h | ⟨y, hy, hyz⟩)
        · exact Or.inl (zUpto_up hzz' h)
        · exact Or.inr ⟨y, hy, inZChamber_of_le hzz' hyz⟩
      have hinter : ∀ z : Zpos A X M att, (Prev z ∧ InZChamber x z) ↔ ZJSet x z := by
        intro z
        constructor
        · rintro ⟨hprev', hzx⟩
          rcases hprev' with ⟨y, hy, hyz⟩ | ⟨y, hyS, hyz⟩
          · exact (mem_shorter_zchamber_iff hzx).1 ⟨y, by omega, hyz⟩
          · refine (mem_earlier_zchamber_iff hzx).1 ⟨y, ?_, ?_, hyz⟩
            · intro hxy
              exact hxS (hxy ▸ hyS)
            · rw [hlen y (Set.mem_insert_of_mem _ hyS), hxlen]
        · intro hJ
          have hzx  := zJSet_imp_inZChamber hJ
          obtain ⟨y, hylt, hyz⟩ := (mem_shorter_zchamber_iff hzx).2 hJ
          exact ⟨Or.inl ⟨y, by omega, hyz⟩, hzx⟩
      obtain ⟨j0, hj0⟩ := exists_zJSet (att := att) hx1
      have hmixPrev : ∀ a b : Zpos A X M att, a ≤ b →
          (fun z => Prev z ∨ InZChamber x z) a → (fun z => Prev z ∨ InZChamber x z) b →
          (Prev a ∧ Prev b) ∨ (InZChamber x a ∧ InZChamber x b) := by
        rintro a b hab (ha | ha) _
        · exact Or.inl ⟨ha, hup a b hab ha⟩
        · exact Or.inr ⟨ha, inZChamber_of_le hab ha⟩
      have hmain : InjIn (fun z : Zpos A X M att => Prev z ∨ InZChamber x z) (InZBaseAt w0) := by
        by_cases hin : RACG.clen A w0 ≤ n ∨ w0 ∈ S
        · -- the copy of the base is already inside the earlier union
          have hPrevInj  := ih (fun y hy =>
            hlen y (Set.mem_insert_of_mem _ hy)) hin
          have hcopy : ∀ z : Zpos A X M att, InZBaseAt w0 z → Prev z := by
            intro z hz
            rcases hin with h | h
            · exact Or.inl (inZBaseAt_imp_zUpto h hz)
            · exact Or.inr ⟨w0, h, inZBaseAt_imp_inZChamber hz⟩
          refine injIn_trans hcopy ?_ hPrevInj
          exact injIn_union_of_unmixed hmixPrev
            (fun z => (hinter z).symm) (connectedIn_zJSet hx1) (simplyConnectedIn_zJSet hx1) hj0
        · -- the chamber added now is the marked chamber carrying the copy
          have hw0x : w0 = x := by
            rcases hbase with h | h
            · exact absurd (Or.inl h) hin
            · rcases Set.mem_insert_iff.1 h with rfl | h
              · rfl
              · exact absurd (Or.inr h) hin
          subst hw0x
          have hchamber : InjIn (fun z : Zpos A X M att => Prev z ∨ InZChamber w0 z)
              (InZChamber w0) := by
            refine injIn_union_of_unmixed (B := Prev) (J := ZJSet w0) ?_
              (fun z => by
                rw [← hinter z]
                exact and_comm)
              (connectedIn_zJSet hx1) (simplyConnectedIn_zJSet hx1) hj0
            rintro a b hab (ha | ha) _
            · exact Or.inr ⟨ha, hup a b hab ha⟩
            · exact Or.inl ⟨ha, inZChamber_of_le hab ha⟩
          exact injIn_trans (fun z hz => inZBaseAt_imp_inZChamber hz) hchamber
            (injIn_zchamber_base hw0)
      refine injIn_congr_left (fun z => ?_) hmain
      constructor
      · rintro ((h | ⟨y, hy, hyz⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨y, Set.mem_insert_of_mem _ hy, hyz⟩
        · exact Or.inr ⟨x, Set.mem_insert _ _, h⟩
      · rintro (h | ⟨y, hy, hyz⟩)
        · exact Or.inl (Or.inl h)
        · rcases Set.mem_insert_iff.1 hy with rfl | hy
          · exact Or.inr hyz
          · exact Or.inl (Or.inr ⟨y, hy, hyz⟩)

/-- **A copy of the base is injective on path classes inside every initial union of chambers.** -/
theorem injIn_zupto {w0 : CayGroup A} (hw0 : M w0) :
    ∀ n : ℕ, RACG.clen A w0 ≤ n →
      InjIn (ZUpto (A := A) (X := X) (M := M) (att := att) n) (InZBaseAt w0) := by
  intro n
  induction n with
  | zero =>
      intro h
      have hw1  := (RACG.clen_eq_zero_iff A).1 (Nat.le_zero.1 h)
      subst hw1
      exact injIn_congr_left (fun z => (zUpto_zero_iff z).symm) (injIn_zchamber_base hw0)
  | succ n ih =>
      intro h
      have hcond : RACG.clen A w0 ≤ n ∨ w0 ∈ {x : CayGroup A | RACG.clen A x = n + 1} := by
        rcases Nat.lt_or_ge (RACG.clen A w0) (n + 1) with h' | h'
        · exact Or.inl (by omega)
        · exact Or.inr (by simp; omega)
      have hstep := injIn_zupto_insert hw0 n ih {x : CayGroup A | RACG.clen A x = n + 1}
        (level_finite A (n + 1)) (fun _ hy => hy) hcond
      refine injIn_congr_left (fun z => ?_) hstep
      constructor
      · rintro (⟨y, hy, hyz⟩ | ⟨y, hy, hyz⟩)
        · exact ⟨y, by omega, hyz⟩
        · exact ⟨y, le_of_eq hy, hyz⟩
      · rintro ⟨y, hy, hyz⟩
        rcases Nat.lt_or_ge (RACG.clen A y) (n + 1) with h' | h'
        · exact Or.inl ⟨y, by omega, hyz⟩
        · exact Or.inr ⟨y, le_antisymm hy h', hyz⟩

/-- **A copy of the base is injective on path classes inside the whole of `Z`.**  A homotopy is a
finite derivation, so it involves only finitely many cells and therefore lies in some initial
union of chambers. -/
theorem injIn_zpos {w0 : CayGroup A} (hw0 : M w0) :
    InjIn (fun _ : Zpos A X M att => True) (InZBaseAt w0) := by
  intro v l hv hp hl hnull
  obtain ⟨n, hn⟩ := exists_htpyIn_of_htpy
    (D := fun n => ZUpto (A := A) (X := X) (M := M) (att := att) n)
    (fun m n hmn z hz => by
      obtain ⟨y, hy, hyz⟩ := hz
      exact ⟨y, le_trans hy hmn, hyz⟩)
    (fun z => ⟨zlen z, zUpto_zlen z⟩) (htpyIn_true_iff.mp hnull)
  refine injIn_zupto hw0 (max n (RACG.clen A w0)) (le_max_right _ _) v l hv hp hl ?_
  refine HtpyIn.mono (fun z hz => ?_) hn
  obtain ⟨y, hy, hyz⟩ := hz
  exact ⟨y, le_trans hy (le_max_left _ _), hyz⟩

/-! ### The conclusion for the fundamental group -/

/-- **Unconditional injectivity of a copy of the base in `π₁(Z)`.**  For every marked chamber
`w` of the model `Z` of modified chambers, and for every base point of the base poset `X`, the
inclusion of the copy of `X` glued into the chamber of `w` induces an injective homomorphism
`π₁(X) → π₁(Z)`.

No extension of the attaching map over the cone point of a chamber is assumed: the attaching map
`att` is the given monotone map on nonempty simplices only. -/
theorem pi1Map_zNew_injective_uncond (w : {w : CayGroup A // M w}) (x : X) :
    Function.Injective
      (Comb.pi1Map (orderCxMap (zNew (A := A) (X := X) (M := M) (att := att) w)
        (zNew_monotone w)) x) :=
  pi1Map_injective_of_injIn (Bp := InZBaseAt w.1) (injIn_zpos w.2)
    (zNew_monotone w) (fun y => inZBaseAt_zNew w y)
    (zBaseRetr_monotone (A := A) (X := X) (M := M) (att := att) w.1)
    (fun y => zBaseRetr_zNew w y) x

/-- **Composing with a covering.**  If `Z` covers a complex `W`, the copy of the base is still
injective on fundamental groups after pushing down to `W`, because a covering is injective on
fundamental groups.  This is the covering step of the comparison with the article's complex; the
identification of `W` with the presentation complex of the substituted presentation is a
separate statement, and is not proved here. -/
theorem pi1Map_zNew_covering_injective {W : Comb.Complex2}
    (q : Comb.Hom (orderCx (Zpos A X M att)) W) (hq : Comb.IsCovering q)
    (w : {w : CayGroup A // M w}) (x : X) :
    Function.Injective
      ((Comb.pi1Map q (zNew (A := A) (X := X) (M := M) (att := att) w x)).comp
        (Comb.pi1Map (orderCxMap (zNew (A := A) (X := X) (M := M) (att := att) w)
          (zNew_monotone w)) x)) :=
  (Comb.pi1Map_injective_of_isCovering hq _).comp (pi1Map_zNew_injective_uncond w x)

end Davis
end FiniteChains
end

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- An element of the special subgroup `W_T` has trivial parity outside `T`. -/
theorem phi_eq_zero_of_mem_specialSub {T : Set V} {u : CayGroup A} (hu : u ∈ specialSub A T)
    {v : V} (hv : v ∉ T) : phi A u v = 0 := by
  obtain ⟨l, hl, rfl⟩ := exists_cword_of_mem_specialSub A hu
  rw [phi_cword]
  have : l.count v = 0 := List.count_eq_zero_of_not_mem (fun hmem => hv (hl v hmem))
  simp [parList, this]

/-- An element of `W_T` with trivial parity is trivial. -/
theorem eq_one_of_mem_specialSub_of_phi_eq_zero {T : Set V} (hT : Commuting A T)
    {u : CayGroup A} (hu : u ∈ specialSub A T) (hphi : phi A u = 0) : u = 1 := by
  obtain ⟨l, hl, hnd, rfl⟩ := exists_nodup_cword A hT hu
  have hnil : l = [] := by
    cases l with
    | nil => rfl
    | cons a t =>
        exfalso
        have hcount : (a :: t).count a = 1 := List.count_eq_one_of_mem hnd (by simp)
        have h0 : phi A (cword A (a :: t)) a = 0 := congrFun hphi a
        rw [phi_cword] at h0
        simp only [parList, hcount, Nat.cast_one] at h0
        exact absurd h0 (by decide)
  rw [hnil, cword_nil]

/-- **`phi` is injective on the special subgroup of a simplex.** -/
theorem phi_injOn_specialSub {T : Set V} (hT : Commuting A T) {u u' : CayGroup A}
    (hu : u ∈ specialSub A T) (hu' : u' ∈ specialSub A T) (h : phi A u = phi A u') : u = u' := by
  have hmem  := Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hu'
  have hzero : phi A (u⁻¹ * u') = 0 := by
    rw [phi_mul, phi_inv, h]
    funext v
    exact zmod2_add_self _
  have := eq_one_of_mem_specialSub_of_phi_eq_zero A hT hmem hzero
  have h2 : u * (u⁻¹ * u') = u * 1 := by rw [this]
  simpa using h2.symm

/-- **`phi` maps `W_T` onto the sign vectors supported in `T`.** -/
theorem exists_mem_specialSub_phi_eq (T : Finset V) (t : V → ZMod 2)
    (ht : ∀ v : V, v ∉ T → t v = 0) :
    ∃ u : CayGroup A, u ∈ specialSub A (T : Set V) ∧ phi A u = t := by
  set l : List V := (T.filter (fun v : V => t v = 1)).toList with hldef
  have hlmem : ∀ a ∈ l, a ∈ (T : Set V) := by
    intro a ha
    rw [hldef, Finset.mem_toList, Finset.mem_filter] at ha
    exact ha.1
  refine ⟨cword A l, cword_mem_specialSub A hlmem, ?_⟩
  rw [phi_cword]
  funext v
  have hcount : l.count v = if v ∈ T ∧ t v = 1 then 1 else 0 := by
    by_cases h : v ∈ T ∧ t v = 1
    · rw [if_pos h]
      refine List.count_eq_one_of_mem (Finset.nodup_toList _) ?_
      rw [hldef, Finset.mem_toList, Finset.mem_filter]
      exact h
    · rw [if_neg h]
      refine List.count_eq_zero_of_not_mem ?_
      rw [hldef, Finset.mem_toList, Finset.mem_filter]
      exact h
  rw [parList, hcount]
  by_cases h : v ∈ T ∧ t v = 1
  · simp_all
  · have h0 : t v = 0 := by
      by_cases hv : v ∈ T
      · by_contra hne
        refine h ⟨hv, ?_⟩
        revert hne
        generalize t v = a
        revert a
        decide
      · exact ht v hv
    rw [if_neg h, h0, Nat.cast_zero]

end RACG
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V} {X : Type u} [Preorder X]

/-! ### The marking by `Γ` -/

/-- The marked chambers of the article: those indexed by `Γ = ker(W → (ℤ/2)^S)`. -/
def IsGamma (A : CommRel V) (w : CayGroup A) : Prop := phi A w = 0

theorem isGamma_one : IsGamma A (1 : CayGroup A) := rfl

/-! ### The cubes of `C(L)` -/

/-- **A closed cube of `C(L)`**: a simplex `T` of `L` (the directions in which the cube is not
degenerate) together with the signs of the remaining coordinates; the signs on `T` are
normalised to zero. -/
structure QCube (A : CommRel V) : Type u where
  /-- The set of directions of the cube: a simplex of `L`. -/
  spx : Finset V
  /-- The fixed signs of the cube. -/
  sgn : V → ZMod 2
  /-- The directions form a simplex of `L`. -/
  isSimplex : IsSimplex A spx
  /-- The signs in the directions of the cube are normalised to zero. -/
  sgn_eq_zero : ∀ v ∈ spx, sgn v = 0

/-- Two cubes with the same directions and the same signs outside them are equal. -/
theorem QCube.ext' {c d : QCube A} (hs : c.spx = d.spx)
    (hv : ∀ v, v ∉ d.spx → c.sgn v = d.sgn v) : c = d := by
  have hsgn : c.sgn = d.sgn := by
    funext v
    by_cases h : v ∈ d.spx
    · rw [c.sgn_eq_zero v (by rw [hs]; exact h), d.sgn_eq_zero v h]
    · simp_all
  obtain ⟨s, e, h1, h2⟩ := c
  simp_all

/-- **The face order of the cubes**: a face has fewer directions and agrees with the signs of
the bigger cube outside it. -/
instance : PartialOrder (QCube A) where
  le c d := c.spx ⊆ d.spx ∧ ∀ v, v ∉ d.spx → c.sgn v = d.sgn v
  le_refl c := ⟨Finset.Subset.refl _, fun _ _ => rfl⟩
  le_trans c d e hcd hde :=
    ⟨hcd.1.trans hde.1, fun v hv =>
      (hcd.2 v (fun h => hv (hde.1 h))).trans (hde.2 v hv)⟩
  le_antisymm c d hcd hdc :=
    QCube.ext' (Finset.Subset.antisymm hcd.1 hdc.1) hcd.2

/-! ### The quotient poset -/

/-- The cubes of `C(L)` other than the all-positive vertex: the vertex `(∅,0)` is removed and
replaced by the copy of the base poset. -/
def QOld (A : CommRel V) : Type u := {c : QCube A // ¬ (c.spx = ∅ ∧ c.sgn = 0)}

/-- **The quotient poset `Q = Z/Γ`**: the retained cubes of `C(L)` together with one copy of the
base poset `X`, glued along the same attaching map as in `Z`. -/
def Qpos (A : CommRel V) (X : Type u) [Preorder X] (_att : NeSpx A →o X) : Type u :=
  QOld A ⊕ X

variable {att : NeSpx A →o X}

/-- A retained cube of `Q`. -/
def qOld (c : QCube A) (hc : ¬ (c.spx = ∅ ∧ c.sgn = 0)) : Qpos A X att := Sum.inl ⟨c, hc⟩

/-- An element of the copy of the base poset in `Q`. -/
def qNew (x : X) : Qpos A X att := Sum.inr x

/-- The order of `Q`, the same mapping-cylinder orientation as in `Z`. -/
protected def Qle : Qpos A X att → Qpos A X att → Prop
  | Sum.inl c, Sum.inl d => c.1 ≤ d.1
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr x, Sum.inl d =>
      d.1.sgn = 0 ∧ ∃ h : d.1.spx.Nonempty, x ≤ att ⟨d.1.spx, h, d.1.isSimplex⟩
  | Sum.inr x, Sum.inr y => x ≤ y

instance qposPreorder : Preorder (Qpos A X att) where
  le := Davis.Qle
  le_refl q := by
    cases q with
    | inl c => exact le_refl c.1
    | inr x => exact le_refl x
  le_trans q q' q'' hqq' hq'q'' := by
    cases q with
    | inl c =>
        cases q' with
        | inl d =>
            cases q'' with
            | inl e => exact le_trans hqq' hq'q''
            | inr y => exact hq'q''.elim
        | inr y => exact hqq'.elim
    | inr x =>
        cases q' with
        | inl d =>
            cases q'' with
            | inl e =>
                obtain ⟨hne, hx⟩ := hqq'.2
                have hsgn : e.1.sgn = 0 := by
                  funext v
                  show e.1.sgn v = 0
                  by_cases hv : v ∈ e.1.spx
                  · exact e.1.sgn_eq_zero v hv
                  · have hd : d.1.sgn v = 0 := by
                      simpa using congrFun (show d.1.sgn = 0 from hqq'.1) v
                    rw [← hq'q''.2 v hv, hd]
                refine ⟨hsgn, Finset.Nonempty.mono hq'q''.1 hne, ?_⟩
                exact le_trans hx (att.monotone (show (⟨d.1.spx, hne, d.1.isSimplex⟩ : NeSpx A) ≤
                  ⟨e.1.spx, Finset.Nonempty.mono hq'q''.1 hne, e.1.isSimplex⟩ from hq'q''.1))
            | inr y => exact hq'q''.elim
        | inr y =>
            cases q'' with
            | inl e =>
                obtain ⟨hne, hy⟩ := hq'q''.2
                exact ⟨hq'q''.1, hne, le_trans hqq' hy⟩
            | inr z => exact le_trans hqq' hq'q''

/-- The inclusion of the copy of the base poset in `Q` is monotone. -/
theorem qNew_monotone : Monotone (qNew (A := A) (X := X) (att := att)) := fun _ _ h => h

/-! ### Parity of the representative of a spherical coset -/

/-- The parity of the representative of a spherical coset is well defined outside its type. -/
theorem phi_rep_eq_of_inChamber {x : CayGroup A} {p : Sph A} (h : InChamber x p) {v : V}
    (hv : v ∉ p.spx) : phi A p.rep v = phi A x v := by
  have hmul : phi A x = phi A p.rep + phi A (p.rep⁻¹ * x) := by
    have := phi_mul A p.rep (p.rep⁻¹ * x)
    rwa [mul_inv_cancel_left] at this
  have hzero  :=
    phi_eq_zero_of_mem_specialSub A h (by simpa using hv)
  simp_all

/-- `p ≤ q` puts the representative of `p` in the coset of `q`. -/
theorem inChamber_rep_of_le {p q : Sph A} (h : p ≤ q) : InChamber p.rep q := by
  have := Subgroup.inv_mem _ h.2
  rwa [mul_inv_rev, inv_inv] at this

/-- **Two cells of one chamber with the same type coincide.** -/
theorem eq_of_inChamber_spx_eq {x : CayGroup A} {r r' : Sph A} (hr : InChamber x r)
    (hr' : InChamber x r') (hs : r.spx = r'.spx) : r = r' := by
  have hT  := commuting_of_isSimplex r.isSimplex
  have huniq := existsUnique_shortest_coset A hT x
  refine Sph.ext' (huniq.unique ?_ ?_) hs
  · refine ⟨?_, fun s hs' => r.no_rdesc s (Finset.mem_coe.1 hs')⟩
    have := Subgroup.inv_mem _ hr
    rwa [mul_inv_rev, inv_inv] at this
  · refine ⟨?_, fun s hs' => r'.no_rdesc s (Finset.mem_coe.1 (by rw [← hs]; exact hs'))⟩
    have := Subgroup.inv_mem _ hr'
    rw [mul_inv_rev, inv_inv] at this
    rw [show r.spx = r'.spx by rw [hs]]
    exact this

/-! ### The projection -/

/-- The signs of the cube under a spherical coset. -/
def qProjSgn (p : Sph A) : V → ZMod 2 :=
  fun v => if v ∈ p.spx then 0 else phi A p.rep v

/-- **The cube under a spherical coset**: `w W_T ↦ (T, phi w |_{S∖T})`. -/
def qProjCube (p : Sph A) : QCube A where
  spx := p.spx
  sgn := qProjSgn p
  isSimplex := p.isSimplex
  sgn_eq_zero v hv := by simp [qProjSgn, hv]

@[simp] theorem qProjCube_spx (p : Sph A) : (qProjCube p).spx = p.spx := rfl

theorem qProjCube_sgn_of_not_mem {p : Sph A} {v : V} (hv : v ∉ p.spx) :
    (qProjCube p).sgn v = phi A p.rep v := by simp [qProjCube, qProjSgn, hv]

/-- The formula for the cube under a spherical coset is independent of the representative. -/
theorem qProjCube_eq_iff {p : Sph A} {c : QCube A} :
    qProjCube p = c ↔ p.spx = c.spx ∧ ∀ v, v ∉ c.spx → phi A p.rep v = c.sgn v := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun v hv => (qProjCube_sgn_of_not_mem hv).symm⟩
  · rintro ⟨hs, hv⟩
    refine QCube.ext' hs (fun v hvc => ?_)
    rw [qProjCube_sgn_of_not_mem (show v ∉ p.spx by rw [hs]; exact hvc)]
    exact hv v hvc

/-- A cell whose cube is retained is not a marked apex. -/
theorem not_isMarkedApex_of_qProjCube_eq {r : Sph A} {c : QCube A}
    (hc : ¬ (c.spx = ∅ ∧ c.sgn = 0)) (h : qProjCube r = c) :
    ¬ IsMarkedApex (IsGamma A) r := by
  rintro ⟨hemp, hrep⟩
  refine hc ⟨by rw [← h]; exact hemp, ?_⟩
  funext v
  have hv : v ∉ r.spx := by rw [show r.spx = ∅ from hemp]; simp
  rw [← h, qProjCube_sgn_of_not_mem hv]
  simpa using congrFun (show phi A r.rep = 0 from hrep) v

theorem not_vplus_qProjCube {p : Sph A} (hp : ¬ IsMarkedApex (IsGamma A) p) :
    ¬ ((qProjCube p).spx = ∅ ∧ (qProjCube p).sgn = 0) := by
  rintro ⟨hemp, hsgn⟩
  refine hp ⟨hemp, ?_⟩
  funext v
  have hv : v ∉ p.spx := by rw [show p.spx = ∅ from hemp]; simp
  rw [← qProjCube_sgn_of_not_mem hv]
  simpa using congrFun hsgn v

/-- **The projection `Z → Q`.** -/
def zProj : Zpos A X (IsGamma A) att → Qpos A X att
  | Sum.inl p => qOld (qProjCube p.1) (not_vplus_qProjCube p.2)
  | Sum.inr wx => qNew wx.2

@[simp] theorem zProj_zNew (w : {w : CayGroup A // IsGamma A w}) (x : X) :
    zProj (A := A) (att := att) (zNew w x) = qNew x := rfl

/-- **The projection is monotone.** -/
theorem zProj_monotone : Monotone (zProj (A := A) (X := X) (att := att)) := by
  rintro (p | ⟨u, x⟩) (q | ⟨v, y⟩) h
  · refine ⟨h.1, fun w hw => ?_⟩
    have hwp  := fun hc => hw (h.1 hc)
    rw [qProjCube_sgn_of_not_mem hwp, qProjCube_sgn_of_not_mem hw]
    exact (phi_rep_eq_of_inChamber (inChamber_rep_of_le h) hw).symm
  · exact h.elim
  · obtain ⟨hne, hx⟩ := h.2
    refine ⟨?_, hne, hx⟩
    funext w
    by_cases hw : w ∈ q.1.spx
    · exact (qProjCube q.1).sgn_eq_zero w hw
    · rw [qProjCube_sgn_of_not_mem hw, phi_rep_eq_of_inChamber h.1 hw]
      simpa using congrFun (show phi A u.1 = 0 from u.2) w
  · exact h.2

/-! ### Surjectivity -/

section Surjective

variable [Fintype V]

/-- **Every cube of the quotient is the image of a cell of `Z`.** -/
theorem exists_zOld_qProjCube (c : QCube A) :
    ∃ p : Sph A, qProjCube p = c := by
  obtain ⟨w, hw⟩ := phi_surjective A c.sgn
  refine ⟨chamberPt w c.isSimplex, ?_⟩
  rw [qProjCube_eq_iff]
  refine ⟨rfl, fun v hv => ?_⟩
  rw [phi_rep_eq_of_inChamber (chamberPt_inChamber w c.isSimplex) (by simpa using hv), hw]

/-- **The projection is onto.** -/
theorem zProj_surjective : Function.Surjective (zProj (A := A) (X := X) (att := att)) := by
  rintro (⟨c, hc⟩ | x)
  · obtain ⟨p, hp⟩ := exists_zOld_qProjCube c
    refine ⟨zOld p (not_isMarkedApex_of_qProjCube_eq hc hp), ?_⟩
    exact congrArg Sum.inl (Subtype.ext hp)
  · exact ⟨zNew ⟨1, isGamma_one⟩ x, rfl⟩

end Surjective

/-! ### `Γ`-invariance and the fibres -/

variable {k : CayGroup A}

end Davis
end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V} {X : Type u} [Preorder X]
  {att : NeSpx A →o X}

/-! ### The unique element of `Γ` in a coset with vanishing outer signs -/

omit [Fintype V] in
/-- **A coset whose signs outside its type vanish contains exactly one element of `Γ`.** -/
theorem existsUnique_isGamma_inChamber {p : Sph A}
    (h : ∀ v, v ∉ p.spx → phi A p.rep v = 0) :
    ∃! g : CayGroup A, IsGamma A g ∧ InChamber g p := by
  obtain ⟨u, hu, hphiu⟩ := exists_mem_specialSub_phi_eq A p.spx
    (fun v => if v ∈ p.spx then phi A p.rep v else 0) (fun v hv => by simp [hv])
  refine ⟨p.rep * u, ⟨?_, ?_⟩, ?_⟩
  · show phi A (p.rep * u) = 0
    funext v
    simp only [phi_mul, Pi.add_apply, Pi.zero_apply, hphiu]
    by_cases hv : v ∈ p.spx
    · rw [if_pos hv, zmod2_add_self]
    · rw [if_neg hv, add_zero, h v hv]
  · show p.rep⁻¹ * (p.rep * u) ∈ specialSub A p.spx
    rw [inv_mul_cancel_left]
    exact hu
  · rintro g ⟨hg, hgp⟩
    have hmem : (p.rep * u)⁻¹ * g ∈ specialSub A p.spx := by
      have h1 : (p.rep * u)⁻¹ * g = u⁻¹ * (p.rep⁻¹ * g) := by group
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hgp
    have hzero : phi A ((p.rep * u)⁻¹ * g) = 0 := by
      funext v
      have hpu : phi A (p.rep * u) = 0 := by
        funext w
        simp only [phi_mul, Pi.add_apply, Pi.zero_apply, hphiu]
        by_cases hw : w ∈ p.spx
        · grind
        · simp_all
      simp only [phi_mul, phi_inv, Pi.add_apply, Pi.zero_apply, hpu,
        show phi A g = 0 from hg]
      simp
    have := eq_one_of_mem_specialSub_of_phi_eq_zero A
      (commuting_of_isSimplex p.isSimplex) hmem hzero
    exact (inv_mul_eq_one.mp this).symm

/-! ### Unique lifts of the cofaces and the faces of an old cell -/

omit [Fintype V] in
/-- **Unique lift of a coface of an old cell.** -/
theorem existsUnique_up_old {p : Sph A} {c : QCube A} (hle : qProjCube p ≤ c) :
    ∃! r : Sph A, p ≤ r ∧ qProjCube r = c := by
  refine ⟨chamberPt p.rep c.isSimplex, ⟨⟨hle.1, ?_⟩, ?_⟩, ?_⟩
  · have hin  :=
      chamberPt_inChamber p.rep c.isSimplex
    have := Subgroup.inv_mem _ hin
    rw [mul_inv_rev, inv_inv] at this
    exact this
  · rw [qProjCube_eq_iff]
    refine ⟨rfl, fun v hv => ?_⟩
    have hv' : v ∉ (chamberPt p.rep c.isSimplex).spx := by simpa using hv
    rw [phi_rep_eq_of_inChamber (chamberPt_inChamber p.rep c.isSimplex) hv']
    have hvp  := fun hc => hv (hle.1 hc)
    rw [← qProjCube_sgn_of_not_mem hvp]
    exact hle.2 v hv
  · rintro r ⟨hpr, hrc⟩
    refine eq_of_inChamber_spx_eq (inChamber_rep_of_le hpr)
      (chamberPt_inChamber p.rep c.isSimplex) ?_
    rw [(qProjCube_eq_iff.1 hrc).1]
    rfl

omit [Fintype V] in
/-- **Unique lift of a cube inside a chamber**: a cube of the quotient with vanishing signs has
exactly one lift in the chamber of a given element of `Γ`. -/
theorem existsUnique_up_inChamber {w : CayGroup A} (hw : IsGamma A w) {c : QCube A}
    (hsgn : c.sgn = 0) :
    ∃! r : Sph A, InChamber w r ∧ qProjCube r = c := by
  refine ⟨chamberPt w c.isSimplex, ⟨chamberPt_inChamber w c.isSimplex, ?_⟩, ?_⟩
  · rw [qProjCube_eq_iff]
    refine ⟨rfl, fun v hv => ?_⟩
    have hv' : v ∉ (chamberPt w c.isSimplex).spx := by simpa using hv
    rw [phi_rep_eq_of_inChamber (chamberPt_inChamber w c.isSimplex) hv']
    rw [show phi A w v = 0 from by simpa using congrFun (show phi A w = 0 from hw) v]
    exact (congrFun hsgn v).symm
  · rintro r ⟨hwr, hrc⟩
    refine eq_of_inChamber_spx_eq hwr (chamberPt_inChamber w c.isSimplex) ?_
    rw [(qProjCube_eq_iff.1 hrc).1]
    rfl

omit [Fintype V] in
/-- **Unique lift of a face of an old cell.**  The face directions fix the element of `W_T`
modulo the special subgroup of the face, by the parity description of `W_T`. -/
theorem existsUnique_down_old {p : Sph A} {c : QCube A} (hle : c ≤ qProjCube p) :
    ∃! r : Sph A, r ≤ p ∧ qProjCube r = c := by
  have hUT  := hle.1
  have hout : ∀ v, v ∉ p.spx → c.sgn v = phi A p.rep v := by
    intro v hv
    rw [hle.2 v hv, qProjCube_sgn_of_not_mem hv]
  -- the element of `W_T` correcting the parities inside `T`
  obtain ⟨u, hu, hphiu⟩ := exists_mem_specialSub_phi_eq A p.spx
    (fun v => if v ∈ p.spx then c.sgn v + phi A p.rep v else 0) (fun v hv => by simp [hv])
  set r : Sph A := chamberPt (p.rep * u) c.isSimplex with hrdef
  have hinr : InChamber (p.rep * u) r := chamberPt_inChamber _ _
  have hrspx : r.spx = c.spx := rfl
  have hrc : qProjCube r = c := by
    rw [qProjCube_eq_iff]
    refine ⟨hrspx, fun v hv => ?_⟩
    have hv' : v ∉ r.spx := by rw [hrspx]; exact hv
    rw [phi_rep_eq_of_inChamber hinr hv']
    simp only [phi_mul, Pi.add_apply, hphiu]
    by_cases hvT : v ∈ p.spx
    · grind
    · simp_all
  have hrp : r ≤ p := by
    refine ⟨by rw [hrspx]; exact hUT, ?_⟩
    have h1 : r.rep⁻¹ * (p.rep * u) ∈ specialSub A r.spx := hinr
    have h2 : r.rep⁻¹ * (p.rep * u) ∈ specialSub A p.spx :=
      specialSub_mono (by exact_mod_cast (show r.spx ⊆ p.spx by rw [hrspx]; exact hUT)) h1
    have h3 : r.rep⁻¹ * p.rep = (r.rep⁻¹ * (p.rep * u)) * u⁻¹ := by group
    rw [h3]
    exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hu)
  refine ⟨r, ⟨hrp, hrc⟩, ?_⟩
  rintro r' ⟨hr'p, hr'c⟩
  have hspx : r.spx = r'.spx := by rw [hrspx, (qProjCube_eq_iff.1 hr'c).1]
  -- the two lifts differ by an element of `W_T` with parity supported in the face
  set k : CayGroup A := r.rep⁻¹ * r'.rep with hkdef
  have hkT : k ∈ specialSub A p.spx := by
    have h1 : r.rep⁻¹ * p.rep ∈ specialSub A p.spx := hrp.2
    have h2 : p.rep⁻¹ * r'.rep ∈ specialSub A p.spx := by
      have := Subgroup.inv_mem _ hr'p.2
      rwa [mul_inv_rev, inv_inv] at this
    have h3 : k = (r.rep⁻¹ * p.rep) * (p.rep⁻¹ * r'.rep) := by rw [hkdef]; group
    rw [h3]
    exact Subgroup.mul_mem _ h1 h2
  have hkout : ∀ v, v ∉ c.spx → phi A k v = 0 := by
    intro v hv
    have h1 : phi A r.rep v = c.sgn v := (qProjCube_eq_iff.1 hrc).2 v hv
    have h2 : phi A r'.rep v = c.sgn v := (qProjCube_eq_iff.1 hr'c).2 v hv
    have : phi A k v = phi A r.rep v + phi A r'.rep v := by
      rw [hkdef]
      simp only [phi_mul, phi_inv, Pi.add_apply]
    rw [this, h1, h2, zmod2_add_self]
  obtain ⟨k0, hk0U, hk0⟩ := exists_mem_specialSub_phi_eq A c.spx (phi A k)
    (fun v hv => hkout v hv)
  have hk0T : k0 ∈ specialSub A p.spx :=
    specialSub_mono (by exact_mod_cast hUT) hk0U
  have hkk0 : k = k0 :=
    phi_injOn_specialSub A (commuting_of_isSimplex p.isSimplex) hkT hk0T hk0.symm
  have hinr' : InChamber r'.rep r := by
    show r.rep⁻¹ * r'.rep ∈ specialSub A r.spx
    rw [← hkdef, hkk0, hrspx]
    exact hk0U
  exact (eq_of_inChamber_spx_eq hinr' (inChamber_rep r') hspx).symm

/-! ### The projection is a covering of posets -/

omit [Fintype V] in
/-- **Unique lifting of the cells above a cell of `Z`.** -/
theorem zProj_up (z : Zpos A X (IsGamma A) att) (q : Qpos A X att)
    (h : zProj z ≤ q) : ∃! b : Zpos A X (IsGamma A) att, z ≤ b ∧ zProj b = q := by
  cases z with
  | inl p =>
      cases q with
      | inl cc =>
          obtain ⟨c, hc⟩ := cc
          obtain ⟨r, ⟨hpr, hrc⟩, huniq⟩ := existsUnique_up_old h
          refine ⟨zOld r (not_isMarkedApex_of_qProjCube_eq hc hrc), ⟨hpr, ?_⟩, ?_⟩
          · exact congrArg Sum.inl (Subtype.ext hrc)
          · rintro (r' | ⟨v, y⟩) ⟨hle, hproj⟩
            · have hr'c  := congrArg Subtype.val (Sum.inl.inj hproj)
              have : r'.1 = r := huniq r'.1 ⟨hle, hr'c⟩
              exact congrArg Sum.inl (Subtype.ext this)
            · exact absurd hproj (fun hcon => by cases hcon)
      | inr y => exact h.elim
  | inr wx =>
      cases q with
      | inl cc =>
          obtain ⟨c, hc⟩ := cc
          obtain ⟨hsgn, hne, hx⟩ := h
          obtain ⟨r, ⟨hwr, hrc⟩, huniq⟩ :=
            existsUnique_up_inChamber wx.1.2 hsgn
          have hspx  := (qProjCube_eq_iff.1 hrc).1
          refine ⟨zOld r (not_isMarkedApex_of_qProjCube_eq hc hrc), ⟨⟨hwr, ?_⟩, ?_⟩, ?_⟩
          · simp_all
          · exact congrArg Sum.inl (Subtype.ext hrc)
          · rintro (r' | ⟨v, y⟩) ⟨hle, hproj⟩
            · have hr'c  := congrArg Subtype.val (Sum.inl.inj hproj)
              have : r'.1 = r := huniq r'.1 ⟨hle.1, hr'c⟩
              exact congrArg Sum.inl (Subtype.ext this)
            · exact absurd hproj (fun hcon => by cases hcon)
      | inr y =>
          refine ⟨zNew wx.1 y, ⟨⟨rfl, h⟩, rfl⟩, ?_⟩
          rintro (r' | ⟨v, y'⟩) ⟨hle, hproj⟩
          · exact absurd hproj (fun hcon => by cases hcon)
          · have hy  := Sum.inr.inj hproj
            refine congrArg Sum.inr (Prod.ext ?_ hy)
            exact hle.1.symm

omit [Fintype V] in
/-- **Unique lifting of the cells below a cell of `Z`.** -/
theorem zProj_down (z : Zpos A X (IsGamma A) att) (q : Qpos A X att)
    (h : q ≤ zProj z) : ∃! b : Zpos A X (IsGamma A) att, b ≤ z ∧ zProj b = q := by
  cases z with
  | inl p =>
      cases q with
      | inl cc =>
          obtain ⟨c, hc⟩ := cc
          obtain ⟨r, ⟨hrp, hrc⟩, huniq⟩ := existsUnique_down_old h
          refine ⟨zOld r (not_isMarkedApex_of_qProjCube_eq hc hrc), ⟨hrp, ?_⟩, ?_⟩
          · exact congrArg Sum.inl (Subtype.ext hrc)
          · rintro (r' | ⟨v, y⟩) ⟨hle, hproj⟩
            · have hr'c  := congrArg Subtype.val (Sum.inl.inj hproj)
              have : r'.1 = r := huniq r'.1 ⟨hle, hr'c⟩
              exact congrArg Sum.inl (Subtype.ext this)
            · exact absurd hproj (fun hcon => by cases hcon)
      | inr y =>
          obtain ⟨hsgn, hne, hy⟩ := h
          have hzero : ∀ v, v ∉ p.1.spx → phi A p.1.rep v = 0 := by
            intro v hv
            rw [← qProjCube_sgn_of_not_mem hv]
            simpa using congrFun hsgn v
          obtain ⟨g, ⟨hg, hgp⟩, huniq⟩ := existsUnique_isGamma_inChamber hzero
          refine ⟨zNew ⟨g, hg⟩ y, ⟨⟨hgp, hne, hy⟩, rfl⟩, ?_⟩
          rintro (r' | ⟨v, y'⟩) ⟨hle, hproj⟩
          · exact absurd hproj (fun hcon => by cases hcon)
          · have hy'  := Sum.inr.inj hproj
            refine congrArg Sum.inr (Prod.ext (Subtype.ext ?_) hy')
            exact huniq v.1 ⟨v.2, hle.1⟩
  | inr wx =>
      cases q with
      | inl cc => exact h.elim
      | inr y =>
          refine ⟨zNew wx.1 y, ⟨⟨rfl, h⟩, rfl⟩, ?_⟩
          rintro (r' | ⟨v, y'⟩) ⟨hle, hproj⟩
          · exact absurd hproj (fun hcon => by cases hcon)
          · have hy  := Sum.inr.inj hproj
            refine congrArg Sum.inr (Prod.ext ?_ hy)
            exact hle.1

/-- **The projection `Z → Q` is a covering of posets.** -/
theorem zProj_isPosetCover :
    Comb.IsPosetCover (zProj (A := A) (X := X) (att := att)) where
  mono := zProj_monotone
  surj := zProj_surjective
  up := zProj_up
  down := zProj_down

/-- **The projection induces a combinatorial covering of the order complexes.** -/
theorem isCovering_orderCxMap_zProj :
    Comb.IsCovering (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone) :=
  Comb.isCovering_orderCxMap zProj_isPosetCover

/-! ### The copy of the base is injective in `π₁(Q)` -/


omit [Fintype V] in
/-- The inclusion of the base in the quotient factors as the inclusion of a copy of the base in
`Z` followed by the covering projection. -/
theorem pi1Map_qNew_eq_comp (w : {w : CayGroup A // IsGamma A w}) (x : X) :
    Comb.pi1Map (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) x
      = (Comb.pi1Map (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone)
          (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w x)).comp
        (Comb.pi1Map (orderCxMap (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w)
          (zNew_monotone w)) x) := by
  ext g
  induction g using Quotient.inductionOn with
  | h l =>
      refine Quotient.sound ?_
      show Comb.Htpy (orderCx (Qpos A X att)) (qNew (att := att) x)
        (qNew (att := att) x)
        (Comb.mapPath (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) l.1)
        (Comb.mapPath (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone)
          (Comb.mapPath (orderCxMap (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w)
            (zNew_monotone w)) l.1))
      rw [(show Comb.mapPath (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone)
        (Comb.mapPath (orderCxMap (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w)
          (zNew_monotone w)) (l.1))
      = Comb.mapPath (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) (l.1) by
        induction (l.1) with
        | nil => rfl
        | cons a t ih =>
            simp only [Comb.mapPath, List.map_cons] at ih ⊢
            rw [ih]
            congr 1)]
      exact Comb.Htpy.refl _

/-- **The inclusion of the base poset in the quotient is injective on fundamental groups.**
The covering datum comes from the construction: `Z → Q` is the covering
`isCovering_orderCxMap_zProj`, and a copy of the base is injective in `π₁(Z)` by
`pi1Map_zNew_injective_uncond`. -/
theorem pi1Map_qNew_injective (x : X) :
    Function.Injective
      (Comb.pi1Map (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) x) := by
  rw [pi1Map_qNew_eq_comp ⟨1, isGamma_one⟩ x]
  exact pi1Map_zNew_covering_injective
    (orderCxMap (zProj) zProj_monotone)
    isCovering_orderCxMap_zProj ⟨1, isGamma_one⟩ x

end Davis
end FiniteChains
end

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α] {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-- The augmentation `ℤ[G] → ℤ` of the group ring of the presented group. -/
abbrev augPres : MonoidAlgebra ℤ (PresGroup ρ) →+* ℤ := augQ (relSub ρ)

/-- The entries `M_{ij}` of the exponent-sum matrix of the presentation: the exponent sum of
`x_i` in the relator `r_j`. -/
def expEntry (i : α) (j : J) : ℤ := Multiplicative.toAdd (expSum i (ρ j))

omit [Fintype α] [Fintype J] in
/-- Augmenting the Fox matrix gives the exponent-sum matrix. -/
theorem augPres_foxMatrixPres (i : α) (j : J) :
    augPres ρ (foxMatrixPres ρ i j) = expEntry ρ i j := by
  have h : foxMatrixPres ρ i j = proj (relSub ρ) (fox i (ρ j)) := rfl
  rw [h, augQ_proj, aug_fox, expEntry]

/-- A **Fox cycle**: an element of `π₂` of the presentation complex, in the coordinates of
`RequestProject/UniversalCoverPi2.lean`. -/
def IsFoxCycle (v : J → MonoidAlgebra ℤ (PresGroup ρ)) : Prop :=
  ∀ i : α, ∑ j, v j * foxMatrixPres ρ i j = 0

/-- **The Cockcroft property.**  The Hurewicz map of the presentation complex is zero: every
Fox cycle (i.e. every element of `π₂`) has zero augmentation in every coordinate. -/
def IsCockcroft : Prop :=
  ∀ v : J → MonoidAlgebra ℤ (PresGroup ρ), IsFoxCycle ρ v → ∀ j, augPres ρ (v j) = 0

end FiniteChains

namespace FiniteChains

open MonoidAlgebra

section Regular

variable {k G : Type*} [Ring k] [Group G]

/-- **`1 - t` is right-regular when `t` has infinite order.**  If `x (1 - t) = 0` then `x` is
invariant under right translation by `t`, so its support is a union of infinite `t`-orbits,
hence empty.  This is the algebraic form of the paper's remark that the associated elements
of the HNN extension have infinite order. -/
theorem mul_one_sub_single_eq_zero {t : G} (ht : ¬ IsOfFinOrder t)
    (x : MonoidAlgebra k G) (hx : x * (1 - single t 1) = 0) : x = 0 := by
  have hstep : ∀ h : G, x.coeff h = x.coeff (h * t⁻¹) := by
    intro h
    have hxt  := (sub_eq_zero.mp (by simpa [mul_sub] using hx)).symm
    have h2 := DFunLike.congr_fun (congrArg (fun f : MonoidAlgebra k G => f.coeff) hxt) h
    simpa [MonoidAlgebra.mul_single_apply] using h2.symm
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, x.coeff g ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (MonoidAlgebra.coeff_injective (Finsupp.ext hall))
  have key : ∀ n : ℕ, x.coeff (g * (t ^ n)⁻¹) ≠ 0 := by
    intro n
    induction n with
    | zero => simpa using hg
    | succ m ih =>
        have hrw : g * (t ^ (m + 1))⁻¹ = g * (t ^ m)⁻¹ * t⁻¹ := by group
        rw [hrw, ← hstep (g * (t ^ m)⁻¹)]
        exact ih
  have hsub : Set.range (fun n : ℕ => g * (t ^ n)⁻¹) ⊆ x.coeff.support := by
    rintro _ ⟨n, rfl⟩
    exact Finsupp.mem_support_iff.mpr (key n)
  have hinj : Function.Injective (fun n : ℕ => g * (t ^ n)⁻¹) := by
    intro a b hab
    simp at hab
    exact injective_pow_iff_not_isOfFinOrder.mpr ht hab
  exact (Set.infinite_range_of_injective hinj) (Set.Finite.subset x.coeff.support.finite_toSet hsub)

end Regular

universe u

end FiniteChains

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (w₀ : FreeGroup (Option α))

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- The augmentation is unchanged by pushing coefficients along a homomorphism of groups. -/
theorem augQ_mapDomain {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (x : MonoidAlgebra ℤ G) :
    (MonoidAlgebra.lift ℤ ℤ G' 1).toRingHom (MonoidAlgebra.mapDomainRingHom ℤ f x)
      = (MonoidAlgebra.lift ℤ ℤ G 1).toRingHom x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => grind
  | single g m => simp

end FiniteChains

namespace FiniteChains
namespace Comb

universe u v

variable {X : Complex2.{u}} {a : X.V} {G : Type v}

/-- The edge path contributed by one signed letter: the chosen loop of the letter, reversed if
the letter carries the negative sign. -/
def germLoopPath (g : G → Loop X a) (gb : G × Bool) : List (X.E × Bool) :=
  if gb.2 then (g gb.1).1 else revPath (g gb.1).1

@[simp] theorem germLoopPath_pos (g : G → Loop X a) (x : G) :
    germLoopPath g (x, true) = (g x).1 := rfl

@[simp] theorem germLoopPath_neg (g : G → Loop X a) (x : G) :
    germLoopPath g (x, false) = revPath (g x).1 := rfl

/-- **The edge loop spelled by a word**: the concatenation of the chosen loops of its letters. -/
def wordPath (g : G → Loop X a) (l : List (G × Bool)) : List (X.E × Bool) :=
  (l.map (germLoopPath g)).flatten

@[simp] theorem wordPath_nil (g : G → Loop X a) : wordPath g ([] : List (G × Bool)) = [] := rfl

@[simp] theorem wordPath_cons (g : G → Loop X a) (gb : G × Bool) (l : List (G × Bool)) :
    wordPath g (gb :: l) = germLoopPath g gb ++ wordPath g l := rfl

theorem wordPath_append (g : G → Loop X a) (l l' : List (G × Bool)) :
    wordPath g (l ++ l') = wordPath g l ++ wordPath g l' := by
  simp [wordPath]

/-- **The homomorphism determined by concrete loops on the generators.** -/
def loopHom (g : G → Loop X a) : FreeGroup G →* Pi1 X a :=
  FreeGroup.lift (fun x => Pi1.mk (g x))

@[simp] theorem loopHom_of (g : G → Loop X a) (x : G) :
    loopHom g (FreeGroup.of x) = Pi1.mk (g x) := by
  simp [loopHom]

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

universe u

variable {X : Complex2.{u}} {a b : X.V} {c : List (X.E × Bool)}

/-- The loop `c · p · c⁻¹` at `a`, for a loop `p` at `b` and a path `c` from `a` to `b`. -/
def conjLoop (hc : IsPath X.src X.tgt c a b) (p : Loop X b) : Loop X a :=
  ⟨c ++ p.1 ++ revPath c,
    isPath_append_iff.mpr ⟨b, isPath_append_iff.mpr ⟨b, hc, p.2⟩, isPath_revPath hc⟩⟩

/-- **Change of base point**: conjugation by a path `c` from `a` to `b` is a homomorphism
`π₁(X, b) →* π₁(X, a)`. -/
def pi1Conj (hc : IsPath X.src X.tgt c a b) : Pi1 X b →* Pi1 X a where
  toFun := Quotient.map (conjLoop hc) (fun _ _ h => (h.congr_append hc (isPath_revPath hc)))
  map_one' := by
    refine Quotient.sound ?_
    show Htpy X a a (c ++ [] ++ revPath c) []
    simpa using htpy_append_revPath hc
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    refine Quotient.sound ?_
    show Htpy X a a (c ++ (p.1 ++ q.1) ++ revPath c)
      ((c ++ p.1 ++ revPath c) ++ (c ++ q.1 ++ revPath c))
    have hcancel : Htpy X b b (revPath c ++ c) [] := htpy_revPath_append hc
    have hleft : IsPath X.src X.tgt (c ++ p.1) a b := isPath_append_iff.mpr ⟨b, hc, p.2⟩
    have hright : IsPath X.src X.tgt (q.1 ++ revPath c) b a :=
      isPath_append_iff.mpr ⟨b, q.2, isPath_revPath hc⟩
    have hmain := hcancel.congr_append hleft hright
    have hrw₁ : (c ++ p.1) ++ (revPath c ++ c) ++ (q.1 ++ revPath c)
        = (c ++ p.1 ++ revPath c) ++ (c ++ q.1 ++ revPath c) := by
      simp [List.append_assoc]
    have hrw₂ : (c ++ p.1) ++ ([] : List (X.E × Bool)) ++ (q.1 ++ revPath c)
        = c ++ (p.1 ++ q.1) ++ revPath c := by
      simp [List.append_assoc]
    rw [hrw₁, hrw₂] at hmain
    exact hmain.symm

@[simp] theorem pi1Conj_mk (hc : IsPath X.src X.tgt c a b) (p : Loop X b) :
    pi1Conj hc (Pi1.mk p) = Pi1.mk (conjLoop hc p) := rfl

/-- Conjugation only depends on the homotopy class of the conjugating path. -/
theorem pi1Conj_congr {c' : List (X.E × Bool)} (hc : IsPath X.src X.tgt c a b)
    (hc' : IsPath X.src X.tgt c' a b) (h : Htpy X a b c c') (x : Pi1 X b) :
    pi1Conj hc x = pi1Conj hc' x := by
  induction x using Quotient.inductionOn with
  | _ p =>
      refine Quotient.sound ?_
      show Htpy X a a (c ++ p.1 ++ revPath c) (c' ++ p.1 ++ revPath c')
      have h1  :=
        Htpy.append_congr hc (isPath_append_iff.mpr ⟨b, p.2, isPath_revPath hc⟩) h (Htpy.refl _)
      have h2  :=
        Htpy.append_congr p.2 (isPath_revPath hc) (Htpy.refl _) (htpy_revPath hc h)
      have h3  :=
        Htpy.append_congr (h.isPath hc) (isPath_append_iff.mpr ⟨b, p.2, isPath_revPath hc⟩)
          (Htpy.refl _) h2
      simpa [List.append_assoc] using h1.trans h3

/-- Conjugating twice is conjugating by the concatenated path. -/
theorem pi1Conj_pi1Conj {d : List (X.E × Bool)} {e : X.V} (hc : IsPath X.src X.tgt c a b)
    (hd : IsPath X.src X.tgt d b e) (x : Pi1 X e) :
    pi1Conj hc (pi1Conj hd x) = pi1Conj (hc.append hd) x := by
  induction x using Quotient.inductionOn with
  | _ p =>
      refine Quotient.sound ?_
      show Htpy X a a (conjLoop hc (conjLoop hd p)).1 (conjLoop (hc.append hd) p).1
      have hlist : (conjLoop hc (conjLoop hd p)).1 = (conjLoop (hc.append hd) p).1 := by
        simp [conjLoop, revPath_append, List.append_assoc]
      rw [hlist]
      exact Htpy.refl _

/-- Conjugation is natural: the image of a conjugated class is the class conjugated by the
image of the path. -/
theorem pi1Map_pi1Conj {Y : Complex2.{u}} (h : Hom X Y) (hc : IsPath X.src X.tgt c a b)
    (x : Pi1 X b) :
    pi1Map h a (pi1Conj hc x) = pi1Conj (isPath_mapPath h hc) (pi1Map h b x) := by
  induction x using Quotient.inductionOn with
  | _ p =>
      refine Quotient.sound ?_
      show Htpy Y (h.onV a) (h.onV a) (mapPath h (conjLoop hc p).1)
        (conjLoop (isPath_mapPath h hc) ⟨mapPath h p.1, isPath_mapPath h p.2⟩).1
      have hrev : mapPath h (revPath c) = revPath (mapPath h c) := by
        simp [mapPath, revPath, revGerm, List.map_map, Function.comp_def, List.map_reverse]
      have hlist : mapPath h (conjLoop hc p).1
          = (conjLoop (isPath_mapPath h hc) ⟨mapPath h p.1, isPath_mapPath h p.2⟩).1 := by
        simp [conjLoop, hrev]
      rw [hlist]
      exact Htpy.refl _

end Comb
end FiniteChains

namespace FiniteChains

open MonoidAlgebra

universe u

section

variable {α J α' J' α'' J'' : Type u}
  [Fintype α] [DecidableEq α] [Fintype J]
  [Fintype α'] [DecidableEq α'] [Fintype J']
  [Fintype α''] [DecidableEq α''] [Fintype J'']


namespace PresMor

variable {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'} {ρ'' : J'' → FreeGroup α''}


omit [Fintype α] [DecidableEq α] [Fintype J] [Fintype α'] [DecidableEq α'] [Fintype J']
  [Fintype α''] [DecidableEq α''] [Fintype J''] in
/-- Pushing coefficients along a composite of group homomorphisms. -/
theorem mapDomainRingHom_comp (g : PresGroup ρ' →* PresGroup ρ'') (f : PresGroup ρ →* PresGroup ρ')
    (c : MonoidAlgebra ℤ (PresGroup ρ)) :
    MonoidAlgebra.mapDomainRingHom ℤ (g.comp f) c
      = MonoidAlgebra.mapDomainRingHom ℤ g (MonoidAlgebra.mapDomainRingHom ℤ f c) := by simp


end PresMor
end
end FiniteChains

namespace FiniteChains.BlockMor

theorem mapDomainRingHom_comp' {G H K : Type*} [Group G] [Group H] [Group K]
    (g : H →* K) (f : G →* H) (x : MonoidAlgebra ℤ G) :
    MonoidAlgebra.mapDomainRingHom ℤ g (MonoidAlgebra.mapDomainRingHom ℤ f x)
      = MonoidAlgebra.mapDomainRingHom ℤ (g.comp f) x :=
  (MonoidAlgebra.mapDomain_comp f g x).symm

end FiniteChains.BlockMor

namespace FiniteChains

namespace BlockFamily

open MonoidAlgebra

universe u

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}

/-- The generators used by the block substituted at the entry `s`: the old generators
together with the copy `Zt s` of the internal generators belonging to `s`. -/
def genEmb (s : Sx) : α ⊕ Zt s → α ⊕ (Σ s : Sx, Zt s) :=
  Sum.map id (fun z => ⟨s, z⟩)

@[simp] theorem genEmb_inl (s : Sx) (i : α) :
    genEmb (Zt := Zt) s (Sum.inl i) = Sum.inl i := rfl

@[simp] theorem genEmb_inr (s : Sx) (z : Zt s) :
    genEmb (α := α) s (Sum.inr z) = Sum.inr ⟨s, z⟩ := rfl

theorem genEmb_injective (s : Sx) : Function.Injective (genEmb (α := α) (Zt := Zt) s) := by
  rintro (i | z) (i' | z') h
  · simp_all
  · simp_all
  · simp_all
  · simp_all

/-- A generator belonging to another block, or an internal generator of a different entry,
is outside the range of `genEmb s`. -/
theorem inr_ne_genEmb {s s' : Sx} (hs : s ≠ s') (z : Zt s') (x : α ⊕ Zt s) :
    (Sum.inr ⟨s', z⟩ : α ⊕ (Σ s : Sx, Zt s)) ≠ genEmb s x := by
  cases x with
  | inl i => simp
  | inr w =>
      simp only [genEmb_inr, ne_eq, Sum.inr.injEq]
      intro h
      exact hs (congrArg Sigma.fst h).symm

variable (ρ : Jr ⊕ Sx → FreeGroup α) (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))

/-- **The simultaneous substitution (3.4).**  The retained relators, read in the free group
on the old generators and all the new internal generators, together with the relators of the
blocks substituted at the entries of `Sx`. -/
def substPresF : Jr ⊕ (Σ s : Sx, Mt s) → FreeGroup (α ⊕ (Σ s : Sx, Zt s)) :=
  Sum.elim (fun j => FreeGroup.map Sum.inl (ρ (Sum.inl j)))
    (fun p => FreeGroup.map (genEmb p.1) (bsub p.1 p.2))

@[simp] theorem substPresF_inl (j : Jr) :
    substPresF ρ bsub (Sum.inl j) = FreeGroup.map Sum.inl (ρ (Sum.inl j)) := rfl

@[simp] theorem substPresF_inr (p : Σ s : Sx, Mt s) :
    substPresF ρ bsub (Sum.inr p) = FreeGroup.map (genEmb p.1) (bsub p.1 p.2) := rfl

/-- The hypothesis supplied by the chosen fillings of (B1): every replaced relator is a
consequence of the relators of the substituted presentation. -/
abbrev FilledF : Prop := ∀ s : Sx,
  FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)) (ρ (Sum.inr s))
    ∈ Subgroup.normalClosure (Set.range (substPresF ρ bsub))

/-- **The structural map on fundamental groups** of the simultaneous substitution. -/
def substHomF (hfill : FilledF ρ bsub) : PresGroup ρ →* PresGroup (substPresF ρ bsub) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (substPresF ρ bsub))).comp
      (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s))))
    (by
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨k, rfl⟩
      show ((QuotientGroup.mk' (relSub (substPresF ρ bsub))).comp
        (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)))) (ρ k) = 1
      cases k with
      | inl j =>
          exact (QuotientGroup.eq_one_iff _).2
            (Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩)
      | inr s => exact (QuotientGroup.eq_one_iff _).2 (hfill s))

variable (hfill : FilledF ρ bsub)

@[simp] theorem substHomF_mk (w : FreeGroup α) :
    substHomF ρ bsub hfill (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)) w) := rfl

/-- The coefficient homomorphism of the structural map. -/
def coeffF : MonoidAlgebra ℤ (PresGroup ρ) →+*
    MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)) :=
  MonoidAlgebra.mapDomainRingHom ℤ (substHomF ρ bsub hfill)

section Fox

variable [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr]
  [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)]

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
theorem coeffF_quotRingHom (x : FreeGroupRing α) :
    coeffF ρ bsub hfill (quotRingHom ℤ (relSub ρ) x)
      = quotRingHom ℤ (relSub (substPresF ρ bsub))
          (freeRingMap (Sum.inl (β := Σ s : Sx, Zt s)) x) := by
  show MonoidAlgebra.mapDomainRingHom ℤ (substHomF ρ bsub hfill)
      (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub ρ)) x)
    = MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub (substPresF ρ bsub)))
        (MonoidAlgebra.mapDomainRingHom ℤ
          (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s))) x)
  rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp']
  congr 1

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [∀ s, Fintype (Zt s)]
  [∀ s, Fintype (Mt s)] in
/-- **A retained relator contributes the old Fox matrix.** -/
theorem foxMatrix_inl_inl (i : α) (j : Jr) :
    foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inl j)
      = coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inl j)) := by
  show quotRingHom ℤ (relSub (substPresF ρ bsub))
      (fox (Sum.inl i) (substPresF ρ bsub (Sum.inl j)))
    = coeffF ρ bsub hfill (quotRingHom ℤ (relSub ρ) (fox i (ρ (Sum.inl j))))
  rw [coeffF_quotRingHom, substPresF_inl, fox_map Sum.inl Sum.inl_injective]

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [∀ s, Fintype (Zt s)]
  [∀ s, Fintype (Mt s)] in
/-- **A retained relator has no derivative in an internal generator.** -/
theorem foxMatrix_inr_inl (w : Σ s : Sx, Zt s) (j : Jr) :
    foxMatrixPres (substPresF ρ bsub) (Sum.inr w) (Sum.inl j) = 0 := by
  show quotRingHom ℤ (relSub (substPresF ρ bsub))
      (fox (Sum.inr w) (substPresF ρ bsub (Sum.inl j))) = 0
  rw [substPresF_inl, fox_map_of_not_mem_range Sum.inl (fun i => Sum.inr_ne_inl), map_zero]

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [∀ s, Fintype (Zt s)]
  [∀ s, Fintype (Mt s)] in
/-- **A block relator has no derivative in the internal generators of another block.**  This
is what makes the simultaneous replacement of a whole family behave like a single one: the
blocks do not interfere. -/
theorem foxMatrix_inr_inr_of_ne {s s' : Sx} (hs : s ≠ s') (z : Zt s') (m : Mt s) :
    foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s', z⟩) (Sum.inr ⟨s, m⟩) = 0 := by
  show quotRingHom ℤ (relSub (substPresF ρ bsub))
      (fox (Sum.inr ⟨s', z⟩) (substPresF ρ bsub (Sum.inr ⟨s, m⟩))) = 0
  rw [substPresF_inr,
    fox_map_of_not_mem_range (genEmb s) (inr_ne_genEmb hs z), map_zero]

/-! ### The structural map on two-chains -/

variable (c : ∀ s : Sx, Mt s → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))

/-- The map on two-chains induced by the simultaneous substitution: a retained two-cell keeps
its coefficient, the coefficient of the two-cell replaced at `s` is spread over the block at
`s` along the filling chain `c s`. -/
def cellsF (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) :
    Jr ⊕ (Σ s : Sx, Mt s) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)) :=
  Sum.elim (fun j => coeffF ρ bsub hfill (y (Sum.inl j)))
    (fun p => coeffF ρ bsub hfill (y (Sum.inr p.1)) * c p.1 p.2)

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem cellsF_inl (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) (j : Jr) :
    cellsF ρ bsub hfill c y (Sum.inl j) = coeffF ρ bsub hfill (y (Sum.inl j)) := rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem cellsF_inr (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ))
    (p : Σ s : Sx, Mt s) :
    cellsF ρ bsub hfill c y (Sum.inr p)
      = coeffF ρ bsub hfill (y (Sum.inr p.1)) * c p.1 p.2 := rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
theorem cellsF_add (y y' : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsF ρ bsub hfill c (y + y') = cellsF ρ bsub hfill c y + cellsF ρ bsub hfill c y' := by
  funext k
  cases k with
  | inl j => simp
  | inr p =>
      show coeffF ρ bsub hfill (y (Sum.inr p.1) + y' (Sum.inr p.1)) * c p.1 p.2 = _
      rw [map_add, add_mul]; rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
theorem cellsF_smul (x : MonoidAlgebra ℤ (PresGroup ρ))
    (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsF ρ bsub hfill c (x • y)
      = coeffF ρ bsub hfill x • cellsF ρ bsub hfill c y := by
  funext k
  cases k with
  | inl j => simp
  | inr p =>
      show coeffF ρ bsub hfill (x * y (Sum.inr p.1)) * c p.1 p.2
        = coeffF ρ bsub hfill x * (coeffF ρ bsub hfill (y (Sum.inr p.1)) * c p.1 p.2)
      rw [map_mul, mul_assoc]


variable {ρ bsub hfill c}




omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
/-- **The simultaneous substitution preserves zero augmentations** (naturality of the
Hurewicz map). -/
theorem augPres_cellsF_eq_zero {y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)}
    (hy : ∀ k, augPres ρ (y k) = 0) (k : Jr ⊕ (Σ s : Sx, Mt s)) :
    augPres (substPresF ρ bsub) (cellsF ρ bsub hfill c y k) = 0 := by
  have haug : ∀ x : MonoidAlgebra ℤ (PresGroup ρ),
      augPres (substPresF ρ bsub) (coeffF ρ bsub hfill x) = augPres ρ x :=
    fun x => augQ_mapDomain (substHomF ρ bsub hfill) x
  cases k with
  | inl j => simp_all
  | inr p => simp_all

end Fox
end BlockFamily
end FiniteChains

namespace FiniteChains
namespace BlockFamily

universe u v

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}

/-- **The data of the one-way comparison.**  A homomorphism `j` out of the source presentation
group and, for every replaced entry, a homomorphism of the free group on the generators of the
substituted block which is marked by `j` on the old generators and kills the block relators. -/
structure BlockMaps (ρ : Jr ⊕ Sx → FreeGroup α) (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))
    {H : Type v} [Group H] (j : PresGroup ρ →* H) where
  /-- The homomorphism carried by the block substituted at the entry `s`. -/
  b : ∀ s : Sx, FreeGroup (α ⊕ Zt s) →* H
  /-- On an old generator the block map is the marking given by `j`. -/
  mark : ∀ (s : Sx) (a : α),
    b s (FreeGroup.of (Sum.inl a)) = j (QuotientGroup.mk (FreeGroup.of a))
  /-- Every relator of the substituted block dies. -/
  rel : ∀ (s : Sx) (m : Mt s), b s (bsub s m) = 1

namespace BlockMaps

variable {ρ : Jr ⊕ Sx → FreeGroup α} {bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)}
  {H : Type v} [Group H] {j : PresGroup ρ →* H} (B : BlockMaps ρ bsub j)

/-- The assignment of the generators of the substituted presentation: an old generator goes to
its image under `j`, an internal generator of the block at `s` to its image under `b s`. -/
def gen : α ⊕ (Σ s : Sx, Zt s) → H :=
  Sum.elim (fun a => j (QuotientGroup.mk (FreeGroup.of a)))
    (fun p => B.b p.1 (FreeGroup.of (Sum.inr p.2)))

@[simp] theorem gen_inl (a : α) : B.gen (Sum.inl a) = j (QuotientGroup.mk (FreeGroup.of a)) := rfl

@[simp] theorem gen_inr (s : Sx) (z : Zt s) :
    B.gen (Sum.inr ⟨s, z⟩) = B.b s (FreeGroup.of (Sum.inr z)) := rfl

/-- On the old generators the lift of `gen` is `j`. -/
theorem lift_gen_map_inl (w : FreeGroup α) :
    FreeGroup.lift B.gen (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)) w)
      = j (QuotientGroup.mk w) := by
  have key : (FreeGroup.lift B.gen).comp (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)))
      = j.comp (QuotientGroup.mk' (relSub ρ)) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    simp [gen]
  exact DFunLike.congr_fun key w

/-- On the generators of the block at `s` the lift of `gen` is `b s`. -/
theorem lift_gen_map_genEmb (s : Sx) (w : FreeGroup (α ⊕ Zt s)) :
    FreeGroup.lift B.gen (FreeGroup.map (genEmb (Zt := Zt) s) w) = B.b s w := by
  have key : (FreeGroup.lift B.gen).comp (FreeGroup.map (genEmb (Zt := Zt) s)) = B.b s := by
    refine FreeGroup.ext_hom _ _ ?_
    rintro (a | z)
    · simpa [gen] using (B.mark s a).symm
    · simp
  exact DFunLike.congr_fun key w

/-- Every relator of the substituted presentation dies under the lift of `gen`. -/
theorem lift_gen_relator (k : Jr ⊕ (Σ s : Sx, Mt s)) :
    FreeGroup.lift B.gen (substPresF ρ bsub k) = 1 := by
  cases k with
  | inl i =>
      rw [substPresF_inl, lift_gen_map_inl]
      have h1 : (QuotientGroup.mk (ρ (Sum.inl i)) : PresGroup ρ) = 1 :=
        (QuotientGroup.eq_one_iff _).2
          (Subgroup.subset_normalClosure (Set.mem_range.2 ⟨Sum.inl i, rfl⟩))
      rw [h1, map_one]
  | inr p =>
      rw [substPresF_inr, lift_gen_map_genEmb]
      exact B.rel p.1 p.2

/-- **The homomorphism `ψ` out of the substituted presentation group** produced by the
universal property.  No injectivity or surjectivity of `ψ` is claimed. -/
def psi : PresGroup (substPresF ρ bsub) →* H :=
  QuotientGroup.lift _ (FreeGroup.lift B.gen) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨k, rfl⟩
    exact B.lift_gen_relator k)

@[simp] theorem psi_mk (w : FreeGroup (α ⊕ (Σ s : Sx, Zt s))) :
    B.psi (QuotientGroup.mk w) = FreeGroup.lift B.gen w := rfl

/-- **The comparison triangle.**  The composite of the structural map of the substitution with
`ψ` is the given homomorphism `j`. -/
theorem psi_comp_substHomF (hfill : FilledF ρ bsub) :
    B.psi.comp (substHomF ρ bsub hfill) = j := by
  refine MonoidHom.ext ?_
  intro x
  induction x using QuotientGroup.induction_on with
  | _ w =>
      show B.psi (substHomF ρ bsub hfill (QuotientGroup.mk w)) = j (QuotientGroup.mk w)
      rw [substHomF_mk, psi_mk, lift_gen_map_inl]

include B in
/-- **The one-way comparison proves `hinj`.**  If the marked block maps exist over an injective
`j`, the structural homomorphism of the simultaneous substitution is injective. -/
theorem injective_substHomF (hfill : FilledF ρ bsub) (hj : Function.Injective j) :
    Function.Injective (substHomF ρ bsub hfill) := by
  intro x y hxy
  refine hj ?_
  have hx  :=
    DFunLike.congr_fun (B.psi_comp_substHomF hfill) x
  have hy  :=
    DFunLike.congr_fun (B.psi_comp_substHomF hfill) y
  simp_all

end BlockMaps

/-! ### The marked form: the block with its own distinguished generators -/

section Marked

variable {Su : Sx → Type u}

/-- The substitution which reads the distinguished generators of the block at `s` as the
prescribed words in the old generators, and is the identity on the internal generators. -/
def blockSubst (u : ∀ s : Sx, Su s → FreeGroup α) (s : Sx) :
    FreeGroup (Su s ⊕ Zt s) →* FreeGroup (α ⊕ Zt s) :=
  FreeGroup.lift (Sum.elim (fun x => FreeGroup.map Sum.inl (u s x))
    (fun z => FreeGroup.of (Sum.inr z)))

@[simp] theorem blockSubst_of_inl (u : ∀ s : Sx, Su s → FreeGroup α) (s : Sx) (x : Su s) :
    blockSubst (Zt := Zt) u s (FreeGroup.of (Sum.inl x)) = FreeGroup.map Sum.inl (u s x) := by
  simp [blockSubst]

@[simp] theorem blockSubst_of_inr (u : ∀ s : Sx, Su s → FreeGroup α) (s : Sx) (z : Zt s) :
    blockSubst (Zt := Zt) u s (FreeGroup.of (Sum.inr z)) = FreeGroup.of (Sum.inr z) := rfl

/-- **The one-way comparison in the marked form of the article.**  The block at `s` is given by
its own presentation with distinguished generators `Su s` and internal generators `Zt s`, and
the substituted relators are `β_m(u, Z)`.  The input is a homomorphism `bq s` out of the free
group on the generators of the block which kills the block relators and whose value on a
distinguished generator is the image under `j` of the prescribed old word (the two marking
equalities `b [s_h] = j [u_h]`, `b [t_h] = j [v_h]` of the article).  The conclusion is the
injectivity of the actual structural homomorphism of the substitution. -/
theorem injective_substHomF_of_markedBlock {H : Type v} [Group H]
    {ρ : Jr ⊕ Sx → FreeGroup α} (u : ∀ s : Sx, Su s → FreeGroup α)
    (beta : ∀ s : Sx, Mt s → FreeGroup (Su s ⊕ Zt s))
    (hfill : FilledF ρ (fun s m => blockSubst u s (beta s m)))
    (j : PresGroup ρ →* H) (hj : Function.Injective j)
    (bq : ∀ s : Sx, FreeGroup (Su s ⊕ Zt s) →* H)
    (hmark : ∀ (s : Sx) (x : Su s),
      bq s (FreeGroup.of (Sum.inl x)) = j (QuotientGroup.mk (u s x)))
    (hrel : ∀ (s : Sx) (m : Mt s), bq s (beta s m) = 1) :
    Function.Injective (substHomF ρ (fun s m => blockSubst u s (beta s m)) hfill) := by
  -- the block map on the substituted generators: old generators go to their `j`-images,
  -- internal generators to their images under the marked block map
  set bb : ∀ s : Sx, FreeGroup (α ⊕ Zt s) →* H := fun s => FreeGroup.lift (Sum.elim
      (fun a : α => j (QuotientGroup.mk (FreeGroup.of a)))
      (fun z : Zt s => bq s (FreeGroup.of (Sum.inr z)))) with hbb
  -- the block map factors the substitution: both sides agree on the generators of the block
  have key : ∀ s : Sx, (bb s).comp (blockSubst u s) = bq s := by
    intro s
    refine FreeGroup.ext_hom _ _ ?_
    rintro (x | z)
    · rw [MonoidHom.comp_apply, blockSubst_of_inl, hmark s x]
      have hcomp : (bb s).comp (FreeGroup.map (Sum.inl))
          = j.comp (QuotientGroup.mk' (relSub ρ)) := by
        refine FreeGroup.ext_hom _ _ fun a => ?_
        simp [hbb]
      exact DFunLike.congr_fun hcomp (u s x)
    · simp_all
  have hmark' : ∀ s a,
      bb s (FreeGroup.of (Sum.inl a)) = j (QuotientGroup.mk (FreeGroup.of a)) := by
    intro s a
    simp [hbb]
  have hrel' : ∀ s m, bb s (blockSubst u s (beta s m)) = 1 := by
    intro s m
    rw [← MonoidHom.comp_apply, key s]
    exact hrel s m
  have hmaps : BlockMaps ρ (fun s m => blockSubst u s (beta s m)) j :=
    { b := bb, mark := hmark', rel := hrel' }
  exact BlockMaps.injective_substHomF hmaps hfill hj

end Marked

end BlockFamily
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- The retained cubes of `C(L)` form a poset: the face order of the cubes. -/
instance : PartialOrder (QOld A) := Subtype.partialOrder _

/-! ### The cut surface inside the block -/

/-- The cube `(σ, 0)` of a nonempty simplex `σ`: a cell of the cut surface, that is, of the part
of the block which is glued to the copy of the base. -/
def posQCube (σ : NeSpx A) : QOld A :=
  ⟨⟨σ.1, 0, σ.2.2, fun _ _ => rfl⟩, fun h => (Finset.nonempty_iff_ne_empty.mp σ.2.1) h.1⟩

omit [Fintype V] in
theorem posQCube_monotone : Monotone (posQCube (A := A)) := fun _ _ h => ⟨h, fun _ _ => rfl⟩

/-- The cut surface as a cellular map into the block. -/
def surfCx (A : CommRel V) : Hom (orderCx (NeSpx A)) (orderCx (QOld A)) :=
  orderCxMap posQCube posQCube_monotone

section Block

variable {X : Type u} [Preorder X] {att : NeSpx A →o X}

/-- The block inside the quotient `Q`: a retained cube is a cell of `Q`. -/
def qOldIncl (c : QOld A) : Qpos A X att := qOld c.1 c.2

omit [Fintype V] in
theorem qOldIncl_monotone : Monotone (qOldIncl (X := X) (att := att)) := fun _ _ h => h

/-- The block as a cellular map into the quotient. -/
def blockCx (A : CommRel V) (X : Type u) [Preorder X] (att : NeSpx A →o X) :
    Hom (orderCx (QOld A)) (orderCx (Qpos A X att)) :=
  orderCxMap qOldIncl qOldIncl_monotone

omit [Fintype V] in
/-- **The defining relation of the cylinder**: the image of a cell of the cut surface under the
attaching map lies below that cell. -/
theorem qNew_att_le_qOldIncl (σ : NeSpx A) :
    (qNew (A := A) (att := att) (att σ)) ≤ qOldIncl (posQCube σ) :=
  ⟨rfl, σ.2.1, le_refl _⟩

end Block
end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- Being joined by an edge path in the block. -/
def ConnQ (a b : QOld A) : Prop :=
  ∃ p, IsPath (orderCx (QOld A)).src (orderCx (QOld A)).tgt p a b

namespace ConnQ


omit [Fintype V] in
theorem symm {a b : QOld A} (h : ConnQ a b) : ConnQ b a :=
  ⟨revPath h.choose, isPath_revPath h.choose_spec⟩

omit [Fintype V] in
theorem trans {a b c : QOld A} (h : ConnQ a b) (h' : ConnQ b c) : ConnQ a c :=
  ⟨h.choose ++ h'.choose, h.choose_spec.append h'.choose_spec⟩

omit [Fintype V] in
theorem of_le {a b : QOld A} (h : a ≤ b) : ConnQ a b := ⟨[ordPos h], isPath_ordPos h⟩

omit [Fintype V] in
theorem of_ge {a b : QOld A} (h : b ≤ a) : ConnQ a b := ⟨[ordNeg h], isPath_ordNeg h⟩

end ConnQ

/-- **A vertex cube**: the cube `(∅, ξ)` of a nonzero sign vector. -/
def vtxCube (ξ : V → ZMod 2) (hξ : ξ ≠ 0) : QOld A :=
  ⟨⟨∅, ξ, isSimplex_empty (A := A), fun v hv => absurd hv (Finset.notMem_empty v)⟩,
    fun h => hξ h.2⟩

/-- **An edge cube**: the cube `({v}, ξ)` with the sign at `v` normalised away. -/
def oneCube (v : V) (ξ : V → ZMod 2) : QOld A :=
  ⟨⟨{v}, Function.update ξ v 0, isSimplex_singleton (A := A) v, fun w hw => by
      rw [Finset.mem_singleton] at hw
      subst hw
      simp⟩,
    fun h => by simpa using congrArg (fun s : Finset V => v ∈ s) h.1⟩

omit [Fintype V] in
theorem vtxCube_le_oneCube {ξ : V → ZMod 2} (hξ : ξ ≠ 0) (v : V) :
    (vtxCube ξ hξ : QOld A) ≤ oneCube v ξ := by
  refine ⟨Finset.empty_subset _, fun w hw => ?_⟩
  have hwv : w ≠ v := fun h => hw (by rw [h]; exact Finset.mem_singleton_self v)
  simp [oneCube, vtxCube, hwv]

omit [Fintype V] in
theorem vtxCube_update_le_oneCube {ξ : V → ZMod 2} (v : V) (a : ZMod 2)
    (h : Function.update ξ v a ≠ 0) :
    (vtxCube (Function.update ξ v a) h : QOld A) ≤ oneCube v ξ := by
  refine ⟨Finset.empty_subset _, fun w hw => ?_⟩
  have hwv : w ≠ v := fun h' => hw (by rw [h']; exact Finset.mem_singleton_self v)
  simp [oneCube, vtxCube, hwv]

/-- The support of a sign vector. -/
def sgnSupport (ξ : V → ZMod 2) : Finset V :=
  Finset.univ.filter (fun v => ξ v ≠ 0)

omit [DecidableEq V] in
theorem mem_sgnSupport {ξ : V → ZMod 2} {v : V} : v ∈ sgnSupport ξ ↔ ξ v ≠ 0 := by
  simp [sgnSupport]

/-- The distinguished sign vector: `1` at `v₀` and `0` elsewhere. -/
def unitSgn (v₀ : V) : V → ZMod 2 := fun w => if w = v₀ then 1 else 0

omit [Fintype V] in
theorem unitSgn_ne_zero (v₀ : V) : unitSgn (V := V) v₀ ≠ 0 := by
  intro h
  simpa [unitSgn] using congrFun h v₀

/-- **Every vertex cube whose sign at `v₀` is `1` is joined to the distinguished one.** -/
theorem connQ_vtxCube_unit (v₀ : V) :
    ∀ (n : ℕ) (ξ : V → ZMod 2) (hξ : ξ ≠ 0), ξ v₀ = 1 → (sgnSupport ξ).card = n →
      ConnQ (vtxCube ξ hξ : QOld A) (vtxCube (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ξ hξ hv₀ hcard
    by_cases hsupp : ∀ w, ξ w ≠ 0 → w = v₀
    · -- the support is `{v₀}`, so `ξ` is the distinguished vector
      have hxi : ξ = unitSgn v₀ := by
        funext w
        by_cases hw : w = v₀
        · subst hw
          simp [unitSgn, hv₀]
        · have : ξ w = 0 := by
            by_contra hne
            exact hw (hsupp w hne)
          simp [unitSgn, hw, this]
      subst hxi
      exact (⟨[], rfl⟩)
    · push_neg at hsupp
      obtain ⟨w, hw, hwv⟩ := hsupp
      set ξ' := Function.update ξ w 0 with hξ'
      have hξ'v₀ : ξ' v₀ = 1 := by
        rw [hξ', Function.update_apply, if_neg (Ne.symm hwv), hv₀]
      have hξ'ne : ξ' ≠ 0 := by
        intro h
        simpa [hξ'v₀] using congrFun h v₀
      -- the two vertex cubes are both faces of the edge cube at `w`
      have hstep : ConnQ (vtxCube ξ hξ : QOld A) (vtxCube ξ' hξ'ne) :=
        (ConnQ.of_le (vtxCube_le_oneCube hξ w)).trans
          (ConnQ.of_ge (vtxCube_update_le_oneCube w 0 hξ'ne))
      -- the support has become smaller
      have hsub : sgnSupport ξ' ⊂ sgnSupport ξ := by
        constructor
        · intro x hx
          rw [mem_sgnSupport] at hx ⊢
          by_cases hxw : x = w
          · subst hxw
            simp [hξ'] at hx
          · rwa [hξ', Function.update_apply, if_neg hxw] at hx
        · intro hle
          have := hle (mem_sgnSupport.2 hw)
          rw [mem_sgnSupport, hξ'] at this
          simp at this
      have hlt : (sgnSupport ξ').card < n := by
        rw [← hcard]
        exact Finset.card_lt_card hsub
      exact hstep.trans (ih _ hlt ξ' hξ'ne hξ'v₀ rfl)

omit [Fintype V] in
/-- **Every cell of the block is joined to a vertex cube.** -/
theorem connQ_to_vtxCube (c : QOld A) :
    ∃ (ξ : V → ZMod 2) (hξ : ξ ≠ 0), ConnQ c (vtxCube ξ hξ) := by
  by_cases hs : c.1.spx = ∅
  · have hne  := fun h => c.2 ⟨hs, h⟩
    refine ⟨c.1.sgn, hne, ?_⟩
    have hEq : c = vtxCube c.1.sgn hne := by
      apply Subtype.ext
      exact QCube.ext' (by simpa [vtxCube] using hs) (fun v _ => rfl)
    exact ConnQ.of_le (le_of_eq hEq)
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hs
    refine ⟨Function.update c.1.sgn v 1, ?_, ?_⟩
    · intro h
      simpa using congrFun h v
    · refine ConnQ.of_ge ⟨Finset.empty_subset _, fun w hw => ?_⟩
      have hwv : w ≠ v := fun h => hw (h ▸ hv)
      simp [vtxCube, hwv]

/-- **The block is connected.** -/
theorem isConnected_orderCx_qOld [Nonempty V] : IsConnected (orderCx (QOld A)) := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have key : ∀ c : QOld A, ConnQ c (vtxCube (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
    intro c
    obtain ⟨ξ, hξ, hc⟩ := connQ_to_vtxCube c
    refine hc.trans ?_
    -- first make the sign at `v₀` equal to `1`, then reduce the support
    set ξ₁ := Function.update ξ v₀ 1 with hξ₁
    have hξ₁v₀ : ξ₁ v₀ = 1 := by simp [hξ₁]
    have hξ₁ne : ξ₁ ≠ 0 := by
      intro h
      simpa [hξ₁v₀] using congrFun h v₀
    have hfirst : ConnQ (vtxCube ξ hξ : QOld A) (vtxCube ξ₁ hξ₁ne) :=
      (ConnQ.of_le (vtxCube_le_oneCube hξ v₀)).trans
        (ConnQ.of_ge (vtxCube_update_le_oneCube v₀ 1 hξ₁ne))
    exact hfirst.trans (connQ_vtxCube_unit v₀ _ ξ₁ hξ₁ne hξ₁v₀ rfl)
  intro a b
  exact ((key a).trans (key b).symm)

/-- **The block carries a spanning tree with any prescribed root**, in particular one rooted at a
cell of the cut surface. -/
theorem exists_spanningTree_qOld [Nonempty V] (r : QOld A) :
    ∃ T : SpanningTree (orderCx (QOld A)), T.root = r :=
  SpanningTree.exists_of_isConnected isConnected_orderCx_qOld r

end Davis
end FiniteChains

namespace FiniteChains

universe u

variable {V : Type u}

/-- An abstract simplicial complex on the vertex type `V`: a downward closed family of
finite subsets of `V` containing the empty face. -/
structure ASC (V : Type u) where
  /-- The family of faces. -/
  faces : Set (Finset V)
  /-- The empty simplex is a face. -/
  empty_mem : (∅ : Finset V) ∈ faces
  /-- Faces are closed under passing to subsets. -/
  down_closed : ∀ {s t : Finset V}, s ∈ faces → t ⊆ s → t ∈ faces

namespace ASC

/-- The order complex of a preorder: its faces are the finite chains. -/
def orderComplex (P : Type u) [Preorder P] : ASC P where
  faces := {s : Finset P | IsChain (· ≤ ·) (s : Set P)}
  empty_mem := by simp [IsChain, Set.Pairwise]
  down_closed := by
    intro s t hs hts
    exact hs.mono (by exact_mod_cast hts)

@[simp] theorem mem_orderComplex {P : Type u} [Preorder P] {s : Finset P} :
    s ∈ (orderComplex P).faces ↔ IsChain (· ≤ ·) (s : Set P) := Iff.rfl



end ASC

end FiniteChains

namespace FiniteChains

open Finset

/-- The state of one coordinate of a cube of `C(L)`: either free, or fixed at `+1`, or
fixed at `-1`. -/
inductive CubeCoord
  | free : CubeCoord
  | pos : CubeCoord
  | neg : CubeCoord
  deriving DecidableEq

namespace CubeCoord

/-- The sign of a fixed coordinate; free coordinates get the value `0`. -/
def sgn : CubeCoord → ℤ
  | .free => 0
  | .pos => 1
  | .neg => -1

end CubeCoord

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- A cube of the moment-angle complex: an assignment of a state to each coordinate. -/
abbrev Cube (V : Type) := V → CubeCoord

/-- The set of free coordinates of a cube; its cardinality is the dimension of the cube. -/
def freeSet (f : Cube V) : Finset V := univ.filter fun v => f v = CubeCoord.free

omit [DecidableEq V] [LinearOrder V] in
@[simp] theorem mem_freeSet {f : Cube V} {v : V} : v ∈ freeSet f ↔ f v = CubeCoord.free := by
  simp [freeSet]

/-! ### The cubical boundary and the fundamental cycle -/

/-- The incidence number of the cube obtained from `g` by freeing the coordinate `j`
(which must be fixed in `g`) with its face `g`: the sign `(-1)^k·δ`, where `k` is the
position of `j` among the free coordinates of the bigger cube and `δ` is the sign at which
the coordinate `j` is fixed. -/
def incid (g : Cube V) (j : V) : ℤ :=
  (-1) ^ ((freeSet g).filter (fun i => i < j)).card * (g j).sgn

/-- The cubical boundary operator, written on coefficient functions: the coefficient of the
cube `g` in `∂c`. -/
def bdry (c : Cube V → ℤ) : Cube V → ℤ := fun g =>
  ∑ j ∈ univ.filter (fun j => g j ≠ CubeCoord.free),
    incid g j * c (Function.update g j CubeCoord.free)

/-- The simplicial boundary of a chain of `n`-simplices, written on coefficient functions:
the coefficient of the face `τ` in `∂o`. -/
def simpBdry (o : Finset V → ℤ) : Finset V → ℤ := fun τ =>
  ∑ j ∈ univ.filter (fun j => j ∉ τ),
    (-1) ^ (τ.filter (fun i => i < j)).card * o (insert j τ)

/-- The cubical chain attached to a simplicial chain `o`: the cube with free set `σ` and
signs `ε` off `σ` gets the coefficient `o(σ)·∏_{h ∉ σ} ε_h`. -/
def cubeChain (o : Finset V → ℤ) : Cube V → ℤ := fun f =>
  o (freeSet f) * ∏ h ∈ univ \ freeSet f, (f h).sgn

/-- **The signed cubical chains of the moment-angle complex form a chain map**:
`∂(c_o) = c_{∂o}`.  This is the computation "every square meets exactly two three-cubes …
the two incidences at each square cancel" of Lemma 3.2, in the form valid in every degree
and for an arbitrary coefficient function. -/
theorem bdry_cubeChain (o : Finset V → ℤ) :
    bdry (cubeChain o) = cubeChain (simpBdry o) := by
  funext g
  have hindex : (univ.filter fun j => g j ≠ CubeCoord.free)
      = univ.filter fun j => j ∉ freeSet g := by
    ext j; simp
  rw [bdry, hindex, cubeChain, simpBdry, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjτ : j ∉ freeSet g := by simpa using hj
  -- the free set of the bigger cube
  have hfree : freeSet (Function.update g j CubeCoord.free) = insert j (freeSet g) := by
    ext i
    by_cases hij : i = j <;> simp [hij]
  -- the sign product over the complement of the bigger cube
  have hprodeq : ∏ h ∈ univ \ insert j (freeSet g),
      (Function.update g j CubeCoord.free h).sgn
      = ∏ h ∈ univ \ insert j (freeSet g), (g h).sgn := by
    refine Finset.prod_congr rfl ?_
    intro h hh
    have hhj : h ≠ j := by
      intro hhj; subst hhj
      simp at hh
    simp [hhj]
  -- split off the `j`-th factor
  have hsplit : ∏ h ∈ univ \ freeSet g, (g h).sgn
      = (g j).sgn * ∏ h ∈ univ \ insert j (freeSet g), (g h).sgn := by
    have hmem : j ∈ univ \ freeSet g := by simp [hjτ]
    rw [← Finset.prod_erase_mul _ _ hmem, mul_comm]
    congr 2
    ext i
    by_cases hij : i = j <;> simp [hij, hjτ]
  rw [cubeChain, hfree, hprodeq, incid, hsplit]
  ring

/-! ### Incidences: every square lies in exactly two three-cubes -/

section Incidence

open scoped Classical

/-- The cubes of `C(L)` having `g` as a codimension one face: those obtained from `g` by
making one further coordinate free. -/
def cofaces (L : ASC V) (g : Cube V) : Finset (Cube V) :=
  ((univ.filter fun j => g j ≠ CubeCoord.free).filter
      fun j => insert j (freeSet g) ∈ L.faces).image
    fun j => Function.update g j CubeCoord.free

omit [LinearOrder V] in
theorem mem_cofaces {L : ASC V} {g f : Cube V} :
    f ∈ cofaces L g ↔ ∃ j, g j ≠ CubeCoord.free ∧ insert j (freeSet g) ∈ L.faces ∧
      f = Function.update g j CubeCoord.free := by
  simp only [cofaces, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  grind

omit [LinearOrder V] in
/-- **Counting the cubes above a given face.**  The number of cubes of `C(L)` having `g` as
a codimension one face is the number of ways of enlarging the free set of `g` by one vertex
inside `L`. -/
theorem card_cofaces (L : ASC V) (g : Cube V) :
    (cofaces L g).card
      = ((univ.filter fun j => j ∉ freeSet g).filter
          fun j => insert j (freeSet g) ∈ L.faces).card := by
  rw [cofaces, Finset.card_image_of_injOn]
  · simp
  · intro j hj k hk hjk
    simp at hj hk
    by_contra hne
    have hval  := congrFun hjk j
    simp only [Function.update_apply, if_neg hne] at hval
    exact hj.1 hval.symm

end Incidence

/-! ### The cubical boundary is a differential -/

omit [LinearOrder V] in
theorem freeSet_update_free (g : Cube V) (j : V) :
    freeSet (Function.update g j CubeCoord.free) = insert j (freeSet g) := by
  ext i
  by_cases hij : i = j <;> simp [hij]

/-- **A simplicial cycle gives a cubical cycle.**  For a triangulated closed oriented
surface `L` with orientation coefficients `o` the hypothesis says that `Σ_σ o(σ)·σ` is a
cycle; the conclusion is that the corresponding signed sum of top-dimensional cubes of
`C(L)` is a cycle, which is the chain used in the proof of Lemma 3.2. -/
theorem cubeChain_cycle {o : Finset V → ℤ} (ho : simpBdry o = 0) :
    bdry (cubeChain o) = 0 := by
  rw [bdry_cubeChain, ho]
  funext f
  simp [cubeChain]

end FiniteChains

namespace FiniteChains

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The cube with free set `σ` all of whose remaining coordinates are `+1`; it is the unique
cube of `C(L)` with free set `σ` that is truncated along the cut cell `Δ_σ`. -/
def posCube (σ : Finset V) : Cube V := fun v => if v ∈ σ then CubeCoord.free else CubeCoord.pos

omit [LinearOrder V] in
@[simp] theorem freeSet_posCube (σ : Finset V) : freeSet (posCube σ) = σ := by
  ext v
  by_cases hv : v ∈ σ <;> simp [posCube, hv]

omit [Fintype V] [LinearOrder V] in
theorem update_posCube (σ : Finset V) (j : V) :
    Function.update (posCube σ) j CubeCoord.free = posCube (insert j σ) := by grind [posCube, Function.update_apply]

omit [LinearOrder V] in
@[simp] theorem cubeChain_posCube (o : Finset V → ℤ) (σ : Finset V) :
    cubeChain o (posCube σ) = o σ := by
  have : ∏ h ∈ univ \ σ, ((posCube σ) h).sgn = 1 := by
    refine Finset.prod_eq_one ?_
    intro h hh
    have := (Finset.mem_sdiff.mp hh).2
    simp [posCube, this, CubeCoord.sgn]
  simp [cubeChain, this]

/-- The sign with which the cut cell `Δ_σ` occurs in the boundary of the truncated cube
with free set `σ` and remaining coordinates `+1`. -/
def cutSign (σ : Finset V) : ℤ := (-1) ^ σ.card

/-- A chain of the truncated complex: coefficients on the cubes and on the cut cells. -/
abbrev TChain (V : Type) := (Cube V → ℤ) × (Finset V → ℤ)

/-- The boundary operator of the truncated complex. -/
def bdryT (x : TChain V) : TChain V :=
  (bdry x.1, fun τ => cutSign τ * x.1 (posCube τ) + simpBdry x.2 τ)

/-- The cubical boundary of the cube `posCube τ`, written out. -/
theorem bdry_posCube (c : Cube V → ℤ) (τ : Finset V) :
    bdry c (posCube τ)
      = ∑ j ∈ univ.filter (fun j => j ∉ τ),
          (-1 : ℤ) ^ (τ.filter (fun i => i < j)).card * c (posCube (insert j τ)) := by simp_all [posCube, bdry, update_posCube, incid, freeSet_posCube, CubeCoord.sgn, Finset.sum_congr]

/-- **Lemma 3.2 (iii): the cut surface bounds.**  Let `o` be the fundamental cycle of an
oriented triangulated closed surface `L` (a simplicial cycle supported on the triangles).
Then the signed sum of the three-cubes of `C(L)`, viewed in the truncated complex, has
boundary equal to the fundamental cycle of the cut copy of `L`, up to sign.  In particular
the class of the cut surface vanishes in `H₂(M)`. -/
theorem cutSurface_isBoundary {o : Finset V → ℤ} (hcyc : simpBdry o = 0)
    (hsupp : ∀ σ : Finset V, σ.card ≠ 3 → o σ = 0) :
    bdryT (cubeChain o, 0) = (0, -o) := by
  refine Prod.ext ?_ ?_
  · exact cubeChain_cycle hcyc
  · funext τ
    show cutSign τ * cubeChain o (posCube τ) + simpBdry 0 τ = -o τ
    have hzero : simpBdry 0 τ = 0 := by simp [simpBdry]
    rw [hzero, add_zero, cubeChain_posCube]
    by_cases h3 : τ.card = 3
    · simp [cutSign, h3]
    · simp [hsupp τ h3]

end FiniteChains

namespace FiniteChains
namespace Comb

universe u

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- The image of a path under a constant map is null-homotopic: all its edges lie in the
subposet `{c}`, which has a largest element. -/
theorem htpy_nil_mapPath_const (c : Q) {u : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p u u) :
    Htpy (orderCx Q) c c
      (mapPath (orderCxMap (fun _ : P => c) monotone_const) p) [] := by
  have hpath  :=
    isPath_mapPath (orderCxMap (fun _ : P => c) monotone_const) hp
  refine htpy_nil_of_pathIn_le_top (A := fun x : Q => x = c) rfl
    (fun x hx => le_of_eq hx) rfl hpath ?_
  intro e he
  simp only [mapPath, List.mem_map] at he
  obtain ⟨e', -, rfl⟩ := he
  exact ⟨rfl, rfl⟩

/-- **Loops dominated by a cone die.**  If the monotone map `g` lies above the monotone map `f`
and above a constant, then the image under `f` of every loop is null-homotopic. -/
theorem htpy_nil_mapPath_of_const_le {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) (c : Q) (hcg : ∀ x, c ≤ g x) {u : P}
    {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p u u) :
    Htpy (orderCx Q) (f u) (f u) (mapPath (orderCxMap f hf) p) [] := by
  have hfp  :=
    isPath_mapPath (orderCxMap f hf) hp
  have hcp  :=
    isPath_mapPath (orderCxMap (fun _ : P => c) monotone_const) hp
  -- both images are conjugate to the image under `g`
  have h1 := htpy_loop_mapPath_le hf hg hfg hp
  have h2 := htpy_loop_mapPath_le monotone_const hg hcg hp
  -- the image under the constant map is trivial
  have h3  :=
    (htpy_nil_mapPath_const c hp).congr_append (isPath_ordNeg (hcg u)) (isPath_ordPos (hcg u))
  have h4  :=
    htpy_ordNeg_ordPos (hcg u)
  have hgnil : Htpy (orderCx Q) (g u) (g u) (mapPath (orderCxMap g hg) p) [] := by
    refine h2.trans (h3.trans ?_)
    simpa using h4
  -- hence the conjugate of the image under `f` is trivial
  have hconj  := h1.symm.trans hgnil
  -- peel the conjugation off
  have hmid : IsPath (orderCx Q).src (orderCx Q).tgt
      ([ordNeg (hfg u)] ++ mapPath (orderCxMap f hf) p ++ [ordPos (hfg u)]) (g u) (g u) :=
    isPath_append_iff.mpr ⟨f u, isPath_append_iff.mpr ⟨f u, isPath_ordNeg (hfg u), hfp⟩,
      isPath_ordPos (hfg u)⟩
  have hstep  :=
    hconj.congr_append (isPath_ordPos (hfg u)) (isPath_ordNeg (hfg u))
  have hcancel  :=
    htpy_ordPos_ordNeg (hfg u)
  have hleft : Htpy (orderCx Q) (f u) (f u)
      ([ordPos (hfg u)] ++ ([ordNeg (hfg u)] ++ mapPath (orderCxMap f hf) p
        ++ [ordPos (hfg u)]) ++ [ordNeg (hfg u)]) [] := by
    refine hstep.trans ?_
    simpa using hcancel
  -- the left hand side is homotopic to the image itself
  have hid : Htpy (orderCx Q) (f u) (f u) (mapPath (orderCxMap f hf) p)
      ([ordPos (hfg u)] ++ ([ordNeg (hfg u)] ++ mapPath (orderCxMap f hf) p
        ++ [ordPos (hfg u)]) ++ [ordNeg (hfg u)]) := by
    have hA : Htpy (orderCx Q) (f u) (f u)
        ([ordPos (hfg u), ordNeg (hfg u)] ++ (mapPath (orderCxMap f hf) p
          ++ [ordPos (hfg u), ordNeg (hfg u)]))
        ([] ++ (mapPath (orderCxMap f hf) p ++ [ordPos (hfg u), ordNeg (hfg u)])) :=
      hcancel.congr_append (isPath_nil' (f u))
        (isPath_append_iff.mpr ⟨f u, hfp, ⟨rfl, rfl, rfl⟩⟩)
    have hB :=
      Htpy.append_congr hfp
        (show IsPath (orderCx Q).src (orderCx Q).tgt [ordPos (hfg u), ordNeg (hfg u)]
          (f u) (f u) from ⟨rfl, rfl, rfl⟩)
        (Htpy.refl _) hcancel
    have : Htpy (orderCx Q) (f u) (f u)
        ([ordPos (hfg u), ordNeg (hfg u)] ++ (mapPath (orderCxMap f hf) p
          ++ [ordPos (hfg u), ordNeg (hfg u)]))
        (mapPath (orderCxMap f hf) p) := by
      refine hA.trans ?_
      simpa using hB
    simpa [List.append_assoc] using this.symm
  exact hid.trans hleft

/-- **A loop inside a subposet carrying a cone is null-homotopic.**  The subposet `A` need not
have a largest element: it is enough to have a monotone map `g` on `A`, with values in the
ambient poset, which lies above the inclusion and above one fixed element. -/
theorem htpy_nil_of_pathIn_cone {A : P → Prop} (g : {x : P // A x} → P) (hg : Monotone g)
    (hfg : ∀ x : {x : P // A x}, (x : P) ≤ g x) (d : P) (hdg : ∀ x : {x : P // A x}, d ≤ g x)
    {v : P} (hv : A v) {l : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt l v v) (hl : PathIn A l) :
    Htpy (orderCx P) v v l [] := by
  have hlift := isPath_liftPathIn l hl hv hv hp
  have h := htpy_nil_mapPath_of_const_le (f := fun x : {x : P // A x} => (x : P))
    monotone_subtypeVal hg hfg d hdg hlift
  rw [show mapPath (orderCxMap (fun x : {x : P // A x} => (x : P)) monotone_subtypeVal)
      (liftPathIn l hl) = l from mapPath_liftPathIn l hl] at h
  exact h

end Comb
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u v

/-! ### A cancellation rule for homotopies -/

section PathCalc

variable {X : Complex2.{u}}

/-- Two paths with the same endpoints are homotopic as soon as the loop obtained by following
the first and coming back along the second is null-homotopic. -/
theorem htpy_of_loop_nil {a b : X.V} {p q : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p a b) (hq : IsPath X.src X.tgt q a b)
    (h : Htpy X a a (p ++ revPath q) []) : Htpy X a b p q := by
  have hrq  := isPath_revPath hq
  have h1 : Htpy X a b (p ++ (revPath q ++ q)) q := by
    have hh := h.congr_append (r := []) rfl hq
    simpa using hh
  have h2  :=
    Htpy.append_congr hp (isPath_append_iff.mpr ⟨a, hrq, hq⟩) (Htpy.refl p)
      (htpy_revPath_append hq)
  have h3 := h2.symm.trans h1
  simpa using h3

/-- Appending a fixed path on the right of a homotopy. -/
theorem htpy_append_right {a b c : X.V} {p q r : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p a b) (hr : IsPath X.src X.tgt r b c) (h : Htpy X a b p q) :
    Htpy X a c (p ++ r) (q ++ r) :=
  Htpy.append_congr hp hr h (Htpy.refl r)

/-- Appending a fixed path on the left of a homotopy. -/
theorem htpy_append_left {a b c : X.V} {p q r : List (X.E × Bool)}
    (hr : IsPath X.src X.tgt r a b) (hp : IsPath X.src X.tgt p b c) (h : Htpy X b c p q) :
    Htpy X a c (r ++ p) (r ++ q) :=
  Htpy.append_congr hr hp (Htpy.refl r) h

end PathCalc

section CmpNerve

variable {P : Type u} [PartialOrder P] [DecidableEq P]

/-- **The comparability graph of a partial order**: two distinct comparable cells are joined. -/
def cmpRel (P : Type u) [PartialOrder P] : CommRel P where
  rel x y := x ≠ y ∧ (x ≤ y ∨ y ≤ x)
  rel_symm := by grind
  rel_irrefl := by simp

/-- **The simplices of the comparability graph are the chains.** -/
theorem isSimplex_cmpRel_iff {σ : Finset P} :
    IsSimplex (cmpRel P) σ ↔ ∀ x ∈ σ, ∀ y ∈ σ, x ≤ y ∨ y ≤ x := by
  constructor
  · intro h x hx y hy
    by_cases hxy : x = y
    · exact Or.inl (le_of_eq hxy)
    · exact (h x hx y hy hxy).2
  · intro h x hx y hy hxy
    exact ⟨hxy, h x hx y hy⟩

/-- The chain with one element: a vertex of the barycentric subdivision. -/
def spx1 (x : P) : NeSpx (cmpRel P) :=
  ⟨{x}, ⟨x, Finset.mem_singleton_self x⟩, isSimplex_singleton x⟩

omit [DecidableEq P] in
@[simp] theorem spx1_val (x : P) : (spx1 x).1 = {x} := rfl

/-- The chain with (at most) two elements: an edge of the barycentric subdivision. -/
def spx2 {x y : P} (h : x ≤ y) : NeSpx (cmpRel P) :=
  ⟨{x, y}, ⟨x, by simp⟩, by
    refine isSimplex_cmpRel_iff.2 ?_
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    exacts [Or.inl le_rfl, Or.inl h, Or.inr h, Or.inl le_rfl]⟩

@[simp] theorem spx2_val {x y : P} (h : x ≤ y) : (spx2 h).1 = {x, y} := rfl

theorem spx1_le_spx2_left {x y : P} (h : x ≤ y) : spx1 x ≤ spx2 h := by
  intro a ha
  simp_all

theorem spx1_le_spx2_right {x y : P} (h : x ≤ y) : spx1 y ≤ spx2 h := by
  intro a ha
  simp_all

/-! ### Paths crossing a chain -/

/-- The two-edge path of the order complex of the chains which goes from the face `a` of the
chain `c` up to `c` and down to its face `b`. -/
def hop {a b c : NeSpx (cmpRel P)} (ha : a ≤ c) (hb : b ≤ c) :
    List ((orderCx (NeSpx (cmpRel P))).E × Bool) :=
  [ordPos ha, ordNeg hb]

omit [DecidableEq P] in
theorem isPath_hop {a b c : NeSpx (cmpRel P)} (ha : a ≤ c) (hb : b ≤ c) :
    IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt (hop ha hb) a b :=
  ⟨rfl, rfl, rfl⟩

/-- The two-edge path which crosses the edge `{x, y}` of the subdivision from `x` to `y`. -/
def edgeHop {x y : P} (h : x ≤ y) : List ((orderCx (NeSpx (cmpRel P))).E × Bool) :=
  hop (spx1_le_spx2_left h) (spx1_le_spx2_right h)

theorem isPath_edgeHop {x y : P} (h : x ≤ y) :
    IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt (edgeHop h)
      (spx1 x) (spx1 y) :=
  isPath_hop _ _

/-- The same edge crossed from `y` to `x`. -/
def edgeHopRev {x y : P} (h : x ≤ y) : List ((orderCx (NeSpx (cmpRel P))).E × Bool) :=
  hop (spx1_le_spx2_right h) (spx1_le_spx2_left h)

theorem isPath_edgeHopRev {x y : P} (h : x ≤ y) :
    IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt (edgeHopRev h)
      (spx1 y) (spx1 x) :=
  isPath_hop _ _

theorem revPath_edgeHop {x y : P} (h : x ≤ y) : revPath (edgeHop h) = edgeHopRev h := rfl

theorem revPath_edgeHopRev {x y : P} (h : x ≤ y) : revPath (edgeHopRev h) = edgeHop h := rfl

/-! ### The star of a cell -/

/-- The chains all of whose elements are faces of the cell `t`: the closed star of `t` in the
barycentric subdivision. -/
def StarCh (t : P) (σ : NeSpx (cmpRel P)) : Prop := ∀ x ∈ σ.1, x ≤ t

omit [DecidableEq P] in
theorem starCh_spx1 {t x : P} (h : x ≤ t) : StarCh t (spx1 x) := by
  intro a ha
  simp_all

theorem starCh_spx2 {t x y : P} (hxy : x ≤ y) (hx : x ≤ t) (hy : y ≤ t) :
    StarCh t (spx2 hxy) := by
  intro a ha
  simp at ha
  grind

/-- The chain obtained by adding the cell `t` to a chain of its star. -/
def insCh (t : P) (σ : NeSpx (cmpRel P)) (hσ : StarCh t σ) : NeSpx (cmpRel P) :=
  ⟨insert t σ.1, ⟨t, Finset.mem_insert_self _ _⟩, by
    refine isSimplex_cmpRel_iff.2 ?_
    intro a ha b hb
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact Or.inl le_rfl
      · exact Or.inr (hσ b hb)
    · rcases hb with rfl | hb
      · exact Or.inl (hσ a ha)
      · exact isSimplex_cmpRel_iff.1 σ.2.2 a ha b hb⟩

@[simp] theorem insCh_val (t : P) (σ : NeSpx (cmpRel P)) (hσ : StarCh t σ) :
    (insCh t σ hσ).1 = insert t σ.1 := rfl

/-- **The filling tool.**  A loop of the subdivision all of whose chains consist of faces of one
fixed cell `t` is null-homotopic: the closed star of a cell is a cone. -/
theorem htpy_nil_of_star (t : P) {v : NeSpx (cmpRel P)} (hv : StarCh t v)
    {l : List ((orderCx (NeSpx (cmpRel P))).E × Bool)}
    (hp : IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt l v v)
    (hl : PathIn (StarCh t) l) :
    Htpy (orderCx (NeSpx (cmpRel P))) v v l [] := by
  refine htpy_nil_of_pathIn_cone (fun σ => insCh t σ.1 σ.2) ?_ ?_ (spx1 t) ?_ hv hp hl
  · rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
    exact Finset.insert_subset_insert _ h
  · rintro ⟨σ, hσ⟩
    exact Finset.subset_insert t σ.1
  · rintro ⟨σ, hσ⟩ a ha
    simp at ha
    subst ha
    exact Finset.mem_insert_self _ _

omit [DecidableEq P] in
/-- A two-edge path inside the star of `t`. -/
theorem pathIn_hop {t : P} {a b c : NeSpx (cmpRel P)} (ha : a ≤ c) (hb : b ≤ c)
    (hc : StarCh t c) : PathIn (StarCh t) (hop ha hb) := by
  have hA  := fun x hx => hc x (ha hx)
  have hB  := fun x hx => hc x (hb hx)
  intro e he
  simp only [hop, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  exacts [⟨hA, hc⟩, ⟨hB, hc⟩]

/-- The path crossing an edge of the subdivision stays in the star of any cell dominating the
two endpoints. -/
theorem pathIn_edgeHop {t x y : P} (hxy : x ≤ y) (hx : x ≤ t) (hy : y ≤ t) :
    PathIn (StarCh t) (edgeHop hxy) :=
  pathIn_hop _ _ (starCh_spx2 hxy hx hy)

theorem pathIn_edgeHopRev {t x y : P} (hxy : x ≤ y) (hx : x ≤ t) (hy : y ≤ t) :
    PathIn (StarCh t) (edgeHopRev hxy) :=
  pathIn_hop _ _ (starCh_spx2 hxy hx hy)

omit [DecidableEq P] in
theorem pathIn_append' {A : NeSpx (cmpRel P) → Prop} {l l' : List ((orderCx (NeSpx (cmpRel P))).E × Bool)}
    (h : PathIn A l) (h' : PathIn A l') : PathIn A (l ++ l') := by
  intro e he
  rcases List.mem_append.1 he with hh | hh
  exacts [h e hh, h' e hh]

/-! ### The largest element of a chain -/

theorem exists_greatest_chain {σ : Finset P} (hne : σ.Nonempty)
    (hch : ∀ x ∈ σ, ∀ y ∈ σ, x ≤ y ∨ y ≤ x) : ∃ m, m ∈ σ ∧ ∀ x ∈ σ, x ≤ m := by
  induction σ using Finset.induction_on with
  | empty => simp_all
  | insert a s ha ih =>
      by_cases hs : s.Nonempty
      · obtain ⟨m, hm, hmax⟩ := ih hs (fun x hx y hy =>
          hch x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy))
        rcases hch a (Finset.mem_insert_self _ _) m (Finset.mem_insert_of_mem hm) with h | h
        · grind
        · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          exacts [le_rfl, le_trans (hmax x hx) h]
      · simp_all

/-- **The largest cell of a nonempty chain.** -/
def chainMax (σ : NeSpx (cmpRel P)) : P :=
  Classical.choose (exists_greatest_chain σ.2.1 (isSimplex_cmpRel_iff.1 σ.2.2))

theorem chainMax_mem (σ : NeSpx (cmpRel P)) : chainMax σ ∈ σ.1 :=
  (Classical.choose_spec (exists_greatest_chain σ.2.1 (isSimplex_cmpRel_iff.1 σ.2.2))).1

theorem le_chainMax (σ : NeSpx (cmpRel P)) {x : P} (hx : x ∈ σ.1) : x ≤ chainMax σ :=
  (Classical.choose_spec (exists_greatest_chain σ.2.1 (isSimplex_cmpRel_iff.1 σ.2.2))).2 x hx

theorem chainMax_monotone : Monotone (chainMax (P := P)) := by
  intro σ τ h
  exact le_chainMax τ (h (chainMax_mem σ))

@[simp] theorem chainMax_spx1 (x : P) : chainMax (spx1 x) = x := by
  have h := chainMax_mem (spx1 x)
  simpa using h

@[simp] theorem chainMax_spx2 {x y : P} (h : x ≤ y) : chainMax (spx2 h) = y := by
  have hmem := chainMax_mem (spx2 h)
  have hy : y ≤ chainMax (spx2 h) := le_chainMax (spx2 h) (by simp)
  simp at hmem
  grind

/-- **The attaching map induced by a monotone labelling of the cells.** -/
def nerveAtt {X : Type v} [Preorder X] (g : P →o X) : NeSpx (cmpRel P) →o X :=
  ⟨fun σ => g (chainMax σ), g.monotone.comp chainMax_monotone⟩

@[simp] theorem nerveAtt_spx1 {X : Type v} [Preorder X] (g : P →o X) (x : P) :
    nerveAtt g (spx1 x) = g x := by simp [nerveAtt]

@[simp] theorem nerveAtt_spx2 {X : Type v} [Preorder X] (g : P →o X) {x y : P} (h : x ≤ y) :
    nerveAtt g (spx2 h) = g y := by simp [nerveAtt]

end CmpNerve

end Davis
end FiniteChains

namespace FiniteChains.Davis
open RACG Mirror
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- Zero parity is the positive corner, consistently with the corner removed in `QOld`. -/
def qCubeToCoordinate (c : QCube A) : Cube V := fun v =>
  if v ∈ c.spx then CubeCoord.free else if c.sgn v = 0 then CubeCoord.pos else CubeCoord.neg

@[simp] theorem freeSet_qCubeToCoordinate (c : QCube A) :
    freeSet (qCubeToCoordinate c) = c.spx := by
  ext v
  by_cases hv : v ∈ c.spx <;> by_cases hs : c.sgn v = 0 <;>
    simp [qCubeToCoordinate, hv, hs]

/-- The same admissible cells as the cube-poset quotient, expressed in coordinates. -/
def CoordinateCube (A : CommRel V) := {c : Cube V // IsSimplex A (freeSet c)}

def coordinateToQCube (c : CoordinateCube A) : QCube A where
  spx := freeSet c.1
  sgn v := match c.1 v with
    | CubeCoord.neg => 1
    | _ => 0
  isSimplex := c.2
  sgn_eq_zero v hv := by simp_all

@[simp] theorem coordinateToQCube_toCoordinate (c : CoordinateCube A) :
    qCubeToCoordinate (coordinateToQCube c) = c.1 := by
  funext v
  cases h : c.1 v <;> simp [qCubeToCoordinate, coordinateToQCube, mem_freeSet, h]

/-- The coordinate identification is an actual equivalence of cell sets. -/
def qCubeCoordinateEquiv : QCube A ≃ CoordinateCube A where
  toFun c := ⟨qCubeToCoordinate c, by simpa using c.isSimplex⟩
  invFun := coordinateToQCube
  left_inv c := by
    apply QCube.ext'
    · exact freeSet_qCubeToCoordinate c
    · intro v hv
      change (match qCubeToCoordinate c v with | CubeCoord.neg => 1 | _ => 0) = c.sgn v
      have hz : c.sgn v = 0 ∨ c.sgn v = 1 := by
        generalize c.sgn v = z
        revert z
        decide
      rcases hz with hz | hz <;> simp [qCubeToCoordinate, hv, hz]
  right_inv c := Subtype.ext (coordinateToQCube_toCoordinate c)

omit [Fintype V] in
/-- The positive corner cubes of the quotient are precisely the cubes meeting the cut. -/
theorem qCubeToCoordinate_sgn_zero (c : QCube A) (hc : c.sgn = 0) :
    qCubeToCoordinate c = posCube c.spx := by
  funext v
  simp [qCubeToCoordinate, posCube, hc]

/-- Recover the parity sign from the actual fixed coordinate. -/
theorem qCubeToCoordinate_parity (c : QCube A) (v : V) :
    (match qCubeToCoordinate c v with | CubeCoord.neg => (1 : ZMod 2) | _ => 0) =
      c.sgn v := congrArg (fun d : QCube A => d.sgn v) (qCubeCoordinateEquiv.left_inv c)

/-- A coordinate cube is a face of another when each coordinate of the larger cube is
 free or agrees with the smaller cube. -/
def CoordinateFace (c d : Cube V) : Prop := ∀ v, d v = CubeCoord.free ∨ c v = d v

/-- The poset used in the full Davis nerve is exactly the coordinate-cube face poset. -/
theorem qCubeToCoordinate_face_iff (c d : QCube A) :
    c ≤ d ↔ CoordinateFace (qCubeToCoordinate c) (qCubeToCoordinate d) := by
  constructor
  · intro h v
    by_cases hv : v ∈ d.spx
    · exact Or.inl (by simp [qCubeToCoordinate, hv])
    · right
      have hvc : v ∉ c.spx := fun hc => hv (h.1 hc)
      simp [qCubeToCoordinate, hv, hvc, h.2 v hv]
  · intro h
    refine ⟨?_, ?_⟩
    · intro v hv
      have hc : qCubeToCoordinate c v = CubeCoord.free := by
        simp [qCubeToCoordinate, hv]
      have hd : qCubeToCoordinate d v = CubeCoord.free := by
        rcases h v with hd | hd
        · exact hd
        · exact hd.symm.trans hc
      have hm  := mem_freeSet.mpr hd
      simpa using hm
    · intro v hv
      have hd : qCubeToCoordinate d v ≠ CubeCoord.free := by
        intro he
        have hm := mem_freeSet.mpr he
        rw [freeSet_qCubeToCoordinate] at hm
        exact hv hm
      have he  := (h v).resolve_left hd
      rw [← qCubeToCoordinate_parity c v, ← qCubeToCoordinate_parity d v, he]


end FiniteChains.Davis

namespace FiniteChains

namespace ASC

universe u

variable {V : Type u} [DecidableEq V]

/-- "The predicate `P` has exactly two witnesses." -/
def ExactlyTwo {α : Sort*} (P : α → Prop) : Prop :=
  ∃ x y, x ≠ y ∧ P x ∧ P y ∧ ∀ z, P z → z = x ∨ z = y

/-- Every edge of `K` lies in exactly two triangles: for every edge `e` there are exactly
two vertices outside `e` spanning a triangle with it. -/
def EdgeInTwoTriangles (K : ASC V) : Prop :=
  ∀ e ∈ K.faces, e.card = 2 → ExactlyTwo (fun v => v ∉ e ∧ insert v e ∈ K.faces)

section Chains

variable {P : Type u} [Preorder P]

theorem isChain_triple {x y z : P} (hxy : x ≤ y ∨ y ≤ x) (hxz : x ≤ z ∨ z ≤ x)
    (hyz : y ≤ z ∨ z ≤ y) : IsChain (· ≤ ·) ({x, y, z} : Set P) := by
  rintro p (rfl | rfl | rfl) q (rfl | rfl | rfl) hpq <;> first
    | exact absurd rfl hpq
    | exact hxy | exact hxy.symm | exact hxz | exact hxz.symm | exact hyz | exact hyz.symm

theorem le_or_le_of_isChain {s : Set P} (hs : IsChain (· ≤ ·) s) {x y : P} (hx : x ∈ s)
    (hy : y ∈ s) : x ≤ y ∨ y ≤ x := by
  by_cases hxy : x = y
  · simp_all
  · exact hs hx hy hxy

end Chains



/-! ### Every vertex of the subdivision lies in a triangle -/

end ASC

end FiniteChains

namespace FiniteChains
namespace Collapse

variable {T F : Type*} [DecidableEq T]

variable (inc : F → Finset T)

/-- Two distinct top cells are adjacent if they share a codimension one face. -/
def Adj (t t' : T) : Prop := t ≠ t' ∧ ∃ f, t ∈ inc f ∧ t' ∈ inc f

/-- The face `f` is *free* for the set `S` of remaining top cells if `t` is the only
remaining top cell containing it. -/
def IsFree (S : Finset T) (f : F) (t : T) : Prop := inc f ∩ S = {t}

/-- `t` admits an elementary collapse in `S`: some face of `t` is free for `S`. -/
def HasFreeFace (S : Finset T) (t : T) : Prop := ∃ f, IsFree inc S f t

/-- A sequence of elementary collapses removing exactly the top cells of `S`. -/
def IsCollapse : List T → Finset T → Prop
  | [], S => S = ∅
  | t :: l, S => t ∈ S ∧ HasFreeFace inc S t ∧ IsCollapse l (S.erase t)

/-- The invariant maintained by the spanning-tree argument: every nonempty subset of the
remaining cells which is closed under adjacency contains a cell with a free face. -/
def Collapsible (S : Finset T) : Prop :=
  ∀ C : Finset T, C ⊆ S → C.Nonempty → (∀ c ∈ C, ∀ t ∈ S, Adj inc c t → t ∈ C) →
    ∃ c ∈ C, HasFreeFace inc S c

/-- Connectivity of the adjacency graph inside `S`. -/
def Connected (S : Finset T) : Prop :=
  ∀ t ∈ S, ∀ t' ∈ S, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj inc a b) t t'

variable {inc}

/-- A nonempty collapsible set has a cell with a free face. -/
theorem exists_hasFreeFace {S : Finset T} (hS : Collapsible inc S) (hne : S.Nonempty) :
    ∃ t ∈ S, HasFreeFace inc S t :=
  hS S (Finset.Subset.refl S) hne fun _ _ _ ht _ => ht

/-- **Collapsibility is preserved by an elementary collapse.**  This is the step "the face
formerly shared with the parent is free once the parent has been removed": a subset that
becomes closed only after the removal of `t` contains a neighbour of `t`, and the shared
face is free for the smaller set. -/
theorem collapsible_erase (hcard : ∀ f, (inc f).card ≤ 2) {S : Finset T}
    (hS : Collapsible inc S) (t : T) : Collapsible inc (S.erase t) := by
  intro C hCS hne hclosed
  by_cases hadj : ∃ c ∈ C, Adj inc c t
  · -- the shared face becomes free
    obtain ⟨c, hcC, hne', f, htf, hcf⟩ := hadj
    refine ⟨c, hcC, f, ?_⟩
    have hsub : ({t, c}) ⊆ inc f := by
      intro z hz
      simp at hz
      rcases hz with rfl | rfl <;> assumption
    have hcard2 : ({t, c} : Finset T).card = 2 := by
      rw [Finset.card_pair]
      exact fun hh => hne' hh.symm
    have hfeq  :=
      (Finset.eq_of_subset_of_card_le hsub (by rw [hcard2]; exact hcard f)).symm
    have hcS  := hCS hcC
    ext z
    simp
    constructor
    · grind
    · simp_all
  · -- `C` was already closed in `S`, so the invariant applies directly
    push_neg at hadj
    have hCS'  := hCS.trans (Finset.erase_subset _ _)
    have hclosed' : ∀ c ∈ C, ∀ u ∈ S, Adj inc c u → u ∈ C := by
      intro c hc u huS hcu
      have hut : u ≠ t := by
        rintro rfl
        exact hadj c hc hcu
      exact hclosed c hc u (Finset.mem_erase.2 ⟨hut, huS⟩) hcu
    obtain ⟨c, hcC, f, hf⟩ := hS C hCS' hne hclosed'
    refine ⟨c, hcC, f, ?_⟩
    have hct  := (Finset.mem_erase.1 (hCS hcC)).1
    ext z
    constructor
    · intro hz
      simp at hz
      have := Finset.mem_inter.2 ⟨hz.1, hz.2.2⟩
      rwa [hf] at this
    · intro hz
      simp at hz
      subst hz
      have hzf : z ∈ inc f ∩ S := by rw [hf]; simp
      simp at hzf
      exact Finset.mem_inter.2 ⟨hzf.1, Finset.mem_erase.2 ⟨hct, hzf.2⟩⟩

/-- **All top cells of a collapsible set can be collapsed away.** -/
theorem exists_isCollapse (hcard : ∀ f, (inc f).card ≤ 2) :
    ∀ (n : ℕ) (S : Finset T), S.card = n → Collapsible inc S → ∃ l : List T, IsCollapse inc l S
  | 0, S, hn, _ => ⟨[], Finset.card_eq_zero.1 hn⟩
  | n + 1, S, hn, hS => by
      have hne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨t, htS, hfree⟩ := exists_hasFreeFace hS hne
      have hcard' : (S.erase t).card = n := by
        rw [Finset.card_erase_of_mem htS, hn]
        omega
      obtain ⟨l, hl⟩ :=
        exists_isCollapse hcard n (S.erase t) hcard' (collapsible_erase hcard hS t)
      exact ⟨t :: l, htS, hfree, hl⟩

/-- A connected set of top cells one of which has a free face is collapsible. -/
theorem collapsible_of_connected {S : Finset T} (hconn : Connected inc S)
    {t₀ : T} (ht₀ : t₀ ∈ S) (hfree : HasFreeFace inc S t₀) : Collapsible inc S := by
  intro C hCS hne hclosed
  obtain ⟨c, hcC⟩ := hne
  have hcS  := hCS hcC
  have key : ∀ x, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj inc a b) c x →
      x ∈ C := by
    intro x hx
    induction hx with
    | refl => exact hcC
    | tail _ hstep ih => grind
  exact ⟨t₀, key t₀ (hconn c hcS t₀ ht₀), hfree⟩

/-- **The collapse of Lemma 3.2 (ii).**  If every codimension one face lies in at most two
top cells, the adjacency graph of the top cells is connected, and one top cell has a free
face, then all top cells can be removed by elementary collapses. -/
theorem exists_isCollapse_of_connected (hcard : ∀ f, (inc f).card ≤ 2) {S : Finset T}
    (hconn : Connected inc S) {t₀ : T} (ht₀ : t₀ ∈ S) (hfree : HasFreeFace inc S t₀) :
    ∃ l : List T, IsCollapse inc l S :=
  exists_isCollapse hcard S.card S rfl (collapsible_of_connected hconn ht₀ hfree)

/-! ### A nonempty instance -/


end Collapse
end FiniteChains

namespace FiniteChains

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- A triangle of `L`: a face with three vertices. -/
def IsTri (L : ASC V) (σ : Finset V) : Prop := σ ∈ L.faces ∧ σ.card = 3

/-- Adjacency of triangles in the dual graph of `L`: they share an edge. -/
def TriAdj (L : ASC V) (σ σ' : Finset V) : Prop :=
  IsTri L σ ∧ IsTri L σ' ∧ (σ ∩ σ').card = 2

/-- The vertices at which a cube has the sign `-1`. -/
def negSet (f : Cube V) : Finset V := univ.filter fun v => f v = CubeCoord.neg

omit [DecidableEq V] [LinearOrder V] in
@[simp] theorem mem_negSet {f : Cube V} {v : V} : v ∈ negSet f ↔ f v = CubeCoord.neg := by
  simp [negSet]

omit [LinearOrder V] in
theorem eq_posCube_of_negSet_empty {f : Cube V} (h : negSet f = ∅) :
    f = posCube (freeSet f) := by
  funext v
  by_cases hv : f v = CubeCoord.free
  · simp [posCube, hv]
  · have hvn : f v ≠ CubeCoord.neg := by
      intro hn
      have : v ∈ negSet f := by simpa using hn
      simp [h] at this
    have hvp : f v = CubeCoord.pos := by
      cases hfv : f v with
      | free => simp_all
      | pos => rfl
      | neg => simp_all
    have : v ∉ freeSet f := by simpa using hv
    simp [posCube, this, hvp]

/-- An elementary move of the adjacency graph: free the coordinate `c'` and fix the
coordinate `c`, leaving the other coordinates untouched.  Both cubes are required to lie in
`C(L)`. -/
def Move (L : ASC V) (f g : Cube V) : Prop :=
  ∃ c c' : V, c ≠ c' ∧ f c = CubeCoord.free ∧ f c' ≠ CubeCoord.free ∧
    g c ≠ CubeCoord.free ∧ g c' = CubeCoord.free ∧
    (∀ v, v ≠ c → v ≠ c' → f v = g v) ∧ freeSet f ∈ L.faces ∧ freeSet g ∈ L.faces

omit [LinearOrder V] in
omit [DecidableEq V] in
theorem Move.symm {L : ASC V} {f g : Cube V} (h : Move L f g) : Move L g f := by grind [Move]

omit [LinearOrder V] in
/-- Two cubes joined by a move share a codimension one face: the cube obtained by fixing
the coordinate `c` as in `g` and the coordinate `c'` as in `f`. -/
theorem Move.shares_square {L : ASC V} {f g : Cube V} (h : Move L f g) :
    ∃ s : Cube V, (∃ j, s j ≠ CubeCoord.free ∧ f = Function.update s j CubeCoord.free) ∧
      (∃ j, s j ≠ CubeCoord.free ∧ g = Function.update s j CubeCoord.free) := by
  obtain ⟨c, c', hcc, hfc, hfc', hgc, hgc', hagree, -, -⟩ := h
  refine ⟨fun v => if v = c then g c else if v = c' then f c' else f v, ⟨c, ?_, ?_⟩,
    ⟨c', ?_, ?_⟩⟩
  · simpa using hgc
  · grind
  · grind
  · grind

/-- The result of a single move which frees `c'` and gives the sign `+1` to `c`. -/
def moveTo (f : Cube V) (c c' : V) : Cube V := fun v =>
  if v = c then CubeCoord.pos else if v = c' then CubeCoord.free else f v

omit [LinearOrder V] in
theorem freeSet_moveTo {f : Cube V} {c c' : V} (hcc : c ≠ c') (hfc : f c = CubeCoord.free) :
    freeSet (moveTo f c c') = insert c' ((freeSet f).erase c) := by
  ext v
  by_cases hv : v = c
  · subst hv
    simp [moveTo, hcc]
  · by_cases hv' : v = c'
    · subst hv'
      simp [moveTo, hv]
    · simp [moveTo, hv, hv']


omit [LinearOrder V] in
/-- An elementary move along an edge of the dual graph of `L`. -/
theorem move_moveTo {L : ASC V} {f : Cube V} {c c' : V} (hcc : c ≠ c')
    (hfc : f c = CubeCoord.free) (hfc' : f c' ≠ CubeCoord.free) (hfL : freeSet f ∈ L.faces)
    (hgL : freeSet (moveTo f c c') ∈ L.faces) : Move L f (moveTo f c c') := by grind [moveTo, Move]

omit [Fintype V] [LinearOrder V] in
/-- Two triangles sharing an edge differ in exactly one vertex each. -/
theorem exists_pair_of_triAdj {L : ASC V} {σ σ' : Finset V} (h : TriAdj L σ σ') :
    ∃ c c', c ≠ c' ∧ c ∈ σ ∧ c ∉ σ' ∧ c' ∈ σ' ∧ c' ∉ σ ∧ σ' = insert c' (σ.erase c) := by
  obtain ⟨⟨-, hcard⟩, ⟨-, hcard'⟩, hint⟩ := h
  have hdiff : (σ \ σ').card = 1 := by
    have := Finset.card_sdiff_add_card_inter σ σ'
    omega
  have hdiff' : (σ' \ σ).card = 1 := by
    have := Finset.card_sdiff_add_card_inter σ' σ
    rw [Finset.inter_comm] at this
    omega
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 hdiff
  obtain ⟨c', hc'⟩ := Finset.card_eq_one.1 hdiff'
  have hcmem : c ∈ σ \ σ' := by rw [hc]; simp
  have hc'mem : c' ∈ σ' \ σ := by rw [hc']; simp
  simp at hcmem hc'mem
  refine ⟨c, c', ?_, hcmem.1, hcmem.2, hc'mem.1, hc'mem.2, ?_⟩
  · grind
  · apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp
      by_cases hzc' : z = c'
      · exact Or.inl hzc'
      · refine Or.inr ⟨?_, ?_⟩
        · rintro rfl
          exact hcmem.2 hz
        · by_contra hzσ
          have : z ∈ σ' \ σ := Finset.mem_sdiff.2 ⟨hz, hzσ⟩
          rw [hc'] at this
          exact hzc' (Finset.mem_singleton.1 this)
    · simp_all

omit [LinearOrder V] in
/-- **Moving along a path in the dual graph of `L`.**  A cube over the triangle `σ` can be
driven to a cube over any triangle joined to `σ` in the dual graph, and the moves never
create new `-1` signs. -/
theorem exists_move_path {L : ASC V} {σ σ' : Finset V}
    (hpath : Relation.ReflTransGen (TriAdj L) σ σ') :
    ∀ f : Cube V, freeSet f = σ → ∃ g : Cube V, freeSet g = σ' ∧ negSet g ⊆ negSet f ∧
      Relation.ReflTransGen (Move L) f g := by
  induction hpath with
  | refl => grind
  | @tail τ τ' hchain hstep ih =>
      intro f hf
      obtain ⟨g, hgfree, hgneg, hgpath⟩ := ih f hf
      obtain ⟨c, c', hcc, hcτ, hcτ', hc'τ', hc'τ, hτ'⟩ := exists_pair_of_triAdj hstep
      have hgc : g c = CubeCoord.free := by
        have : c ∈ freeSet g := by rw [hgfree]; exact hcτ
        simpa using this
      have hgc' : g c' ≠ CubeCoord.free := by
        intro hcon
        have : c' ∈ freeSet g := by simpa using hcon
        rw [hgfree] at this
        exact hc'τ this
      have hfreeNew : freeSet (moveTo g c c') = τ' := by
        rw [freeSet_moveTo hcc hgc, hgfree, hτ']
      refine ⟨moveTo g c c', hfreeNew, (show negSet (moveTo g c c') ⊆ negSet g by
        intro v hv
        simp only [mem_negSet, moveTo] at hv ⊢
        grind).trans hgneg, ?_⟩
      refine hgpath.tail (move_moveTo hcc hgc hgc' ?_ ?_)
      · rw [hgfree]; exact hstep.1.1
      · rw [hfreeNew]; exact hstep.2.1.1

omit [LinearOrder V] in
/-- Every cube of `C(L)` over a triangle can be driven to the all-`+1` cube over a fixed
triangle. -/
theorem reflTransGen_move_posCube {L : ASC V} (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' →
      Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ) {σ₀ : Finset V} (hσ₀ : IsTri L σ₀) :
    ∀ (n : ℕ) (f : Cube V), IsTri L (freeSet f) → (negSet f).card ≤ n →
      Relation.ReflTransGen (Move L) f (posCube σ₀)
  | 0, f, hf, hn => by
      have hempty : negSet f = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hn)
      obtain ⟨g, hgfree, hgneg, hgpath⟩ :=
        exists_move_path (hdual _ _ hf hσ₀) f rfl
      have hgempty : negSet g = ∅ := Finset.subset_empty.1 (hempty ▸ hgneg)
      have : g = posCube σ₀ := by
        rw [eq_posCube_of_negSet_empty hgempty, hgfree]
      rwa [this] at hgpath
  | n + 1, f, hf, hn => by
      rcases (negSet f).eq_empty_or_nonempty with hempty | ⟨v, hv⟩
      · exact reflTransGen_move_posCube hdual hcover hσ₀ 0 f hf (by simp [hempty])
      · obtain ⟨τ, hτ, hvτ⟩ := hcover v
        obtain ⟨g, hgfree, hgneg, hgpath⟩ := exists_move_path (hdual _ _ hf hτ) f rfl
        have hvg : v ∉ negSet g := by
          intro hcon
          have hvfree : g v = CubeCoord.free := by
            have : v ∈ freeSet g := by rw [hgfree]; exact hvτ
            simpa using this
          rw [mem_negSet] at hcon
          rw [hvfree] at hcon
          exact CubeCoord.noConfusion hcon
        have hstrict : (negSet g).card < (negSet f).card :=
          Finset.card_lt_card ⟨hgneg, fun hcon => hvg (hcon hv)⟩
        have hgtri : IsTri L (freeSet g) := by rw [hgfree]; exact hτ
        have : (negSet g).card ≤ n := by omega
        exact hgpath.trans (reflTransGen_move_posCube hdual hcover hσ₀ n g hgtri this)

omit [LinearOrder V] in
/-- **The adjacency graph of the three-cubes of `C(L)` is connected.**  The hypotheses are
the two combinatorial properties of a triangulated closed surface that the paper uses: the
dual graph of `L` is connected, and every vertex of `L` lies in a triangle. -/
theorem reflTransGen_move {L : ASC V} (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' →
      Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ) {f g : Cube V}
    (hf : IsTri L (freeSet f)) (hg : IsTri L (freeSet g)) :
    Relation.ReflTransGen (Move L) f g := by
  have hfp := reflTransGen_move_posCube hdual hcover hf (negSet f).card f hf le_rfl
  have hgp := reflTransGen_move_posCube hdual hcover hf (negSet g).card g hg le_rfl
  have hgp_rev : Relation.ReflTransGen (Move L) (posCube (freeSet f)) g := by
    exact Relation.ReflTransGen.mono (fun _ _ (step : Move L _ _) => step.symm) _ _
      (Relation.ReflTransGen.swap _ _ hgp)
  exact hfp.trans hgp_rev

end FiniteChains

namespace FiniteChains

open Finset

instance : Fintype CubeCoord :=
  ⟨{CubeCoord.free, CubeCoord.pos, CubeCoord.neg}, fun x => by cases x <;> decide⟩

variable {V : Type} [Fintype V] [DecidableEq V]

open scoped Classical in
/-- The three-cubes of `C(L)`: the top cells of the complex. -/
def topCubes (L : ASC V) : Finset (Cube V) :=
  univ.filter fun f => IsTri L (freeSet f)

open scoped Classical in
@[simp] theorem mem_topCubes {L : ASC V} {f : Cube V} :
    f ∈ topCubes L ↔ IsTri L (freeSet f) := by
  simp [topCubes]

open scoped Classical in
/-- The codimension one faces used in the collapse of `M`, and the three-cubes containing
each of them: a square `g` lies in its cofaces, and the cut face attached to the truncated
corner cube over a triangle `σ` lies in that cube alone. -/
def spineInc (L : ASC V) : Cube V ⊕ Finset V → Finset (Cube V)
  | Sum.inl g => if (freeSet g).card = 2 then cofaces L g else ∅
  | Sum.inr σ => if IsTri L σ then {posCube σ} else ∅

open scoped Classical in
/-- **Every codimension one face lies in at most two three-cubes.**  For squares this is the
incidence count of Lemma 3.2 ("every square meets exactly two three-cubes, because every
edge of `L` meets two triangles"); a cut face lies in the single cube it truncates. -/
theorem spineInc_card_le_two {L : ASC V}
    (hedge : ∀ e : Finset V, e.card = 2 →
      ((univ.filter fun j => j ∉ e).filter fun j => insert j e ∈ L.faces).card ≤ 2)
    (f : Cube V ⊕ Finset V) : (spineInc L f).card ≤ 2 := by
  cases f with
  | inl g =>
      by_cases hg : (freeSet g).card = 2
      · simp only [spineInc, if_pos hg]
        rw [card_cofaces]
        exact hedge _ hg
      · simp [spineInc, hg]
  | inr σ =>
      by_cases hσ : IsTri L σ
      · simp [spineInc, hσ]
      · simp [spineInc, hσ]

/-- A move keeps a cube among the three-cubes: it exchanges one free coordinate for
another, so the dimension is unchanged. -/
theorem mem_topCubes_of_move {L : ASC V} {f g : Cube V} (h : Move L f g)
    (hf : f ∈ topCubes L) : g ∈ topCubes L := by
  obtain ⟨c, c', hcc, hfc, hfc', hgc, hgc', hagree, -, hgL⟩ := h
  rw [mem_topCubes] at hf ⊢
  refine ⟨hgL, ?_⟩
  -- `freeSet g = insert c' ((freeSet f).erase c)`
  have hset : freeSet g = insert c' ((freeSet f).erase c) := by
    ext v
    simp
    constructor
    · intro hv
      by_cases hvc' : v = c'
      · exact Or.inl hvc'
      · have hvc : v ≠ c := by
          rintro rfl
          exact hgc hv
        exact Or.inr ⟨hvc, by rw [hagree v hvc hvc']; exact hv⟩
    · rintro (rfl | ⟨hvc, hv⟩)
      · exact hgc'
      · by_cases hvc' : v = c'
        · subst hvc'
          exact absurd hv hfc'
        · rw [← hagree v hvc hvc']; exact hv
  have hc : c ∈ freeSet f := by simpa using hfc
  have hc' : c' ∉ (freeSet f).erase c := by
    simp
    intro _
    exact hfc'
  rw [hset, Finset.card_insert_of_notMem hc', Finset.card_erase_of_mem hc, hf.2]

/-- **A move is an adjacency of the collapse**: the two cubes are distinct and share a
square. -/
theorem adj_of_move {L : ASC V} {f g : Cube V} (h : Move L f g)
    (hf : f ∈ topCubes L) (hg : g ∈ topCubes L) :
    Collapse.Adj (spineInc L) f g := by
  obtain ⟨s, ⟨j, hsj, hfs⟩, ⟨k, hsk, hgs⟩⟩ := h.shares_square
  have hfree : freeSet f = insert j (freeSet s) := by
    rw [hfs, freeSet_update_free]
  have hjs : j ∉ freeSet s := by simpa using hsj
  have hcard : (freeSet s).card = 2 := by
    have := (mem_topCubes.1 hf).2
    rw [hfree, Finset.card_insert_of_notMem hjs] at this
    omega
  have hne : f ≠ g := by
    obtain ⟨c, c', hcc, hfc, hfc', hgc, hgc', -, -, -⟩ := h
    intro hfg
    rw [hfg] at hfc
    exact hgc hfc
  refine ⟨hne, Sum.inl s, ?_, ?_⟩
  · simp only [spineInc, if_pos hcard]
    exact mem_cofaces.2 ⟨j, hsj, by rw [← hfree]; exact (mem_topCubes.1 hf).1, hfs⟩
  · simp only [spineInc, if_pos hcard]
    refine mem_cofaces.2 ⟨k, hsk, ?_, hgs⟩
    have : freeSet g = insert k (freeSet s) := by rw [hgs, freeSet_update_free]
    rw [← this]
    exact (mem_topCubes.1 hg).1

/-- **The adjacency graph of the three-cubes of `C(L)` is connected**, in the form required
by the collapse theorem. -/
theorem connected_topCubes {L : ASC V}
    (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' → Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ) :
    Collapse.Connected (spineInc L) (topCubes L) := by
  intro f hf g hg
  have hpath  :=
    reflTransGen_move hdual hcover (mem_topCubes.1 hf) (mem_topCubes.1 hg)
  -- transport the path to the relation restricted to the three-cubes
  have key : ∀ {a b : Cube V}, Relation.ReflTransGen (Move L) a b → a ∈ topCubes L →
      b ∈ topCubes L ∧ Relation.ReflTransGen
        (fun x y => x ∈ topCubes L ∧ y ∈ topCubes L ∧ Collapse.Adj (spineInc L) x y) a b := by
    intro a b hab ha
    induction hab with
    | refl => grind
    | tail hxy hyz ih =>
        obtain ⟨hy, hpath'⟩ := ih
        have hz := mem_topCubes_of_move hyz hy
        exact ⟨hz, hpath'.tail ⟨hy, hz, adj_of_move hyz hy hz⟩⟩
  simp_all

/-- The cut face of the truncated corner cube over a triangle `σ` is free: that cube is the
only three-cube containing it. -/
theorem hasFreeFace_posCube {L : ASC V} {σ : Finset V} (hσ : IsTri L σ) :
    Collapse.HasFreeFace (spineInc L) (topCubes L) (posCube σ) := by
  refine ⟨Sum.inr σ, ?_⟩
  have hmem : posCube σ ∈ topCubes L := by
    rw [mem_topCubes, freeSet_posCube]
    exact hσ
  simp only [Collapse.IsFree, spineInc, if_pos hσ]
  simp_all

open scoped Classical in
/-- **Lemma 3.2 (ii) in the explicit model.**  For a simplicial complex `L` each of whose
edges lies in at most two triangles, whose dual graph is connected and each of whose
vertices lies in a triangle, all three-cubes of the truncated complex
`M = C(L) ∖ (neighbourhood of the corner)` can be removed by elementary collapses: the
spanning-tree argument of the paper is carried out, and `M` collapses onto a
two-dimensional spine. -/
theorem exists_spine_collapse {L : ASC V}
    (hedge : ∀ e : Finset V, e.card = 2 →
      ((univ.filter fun j => j ∉ e).filter fun j => insert j e ∈ L.faces).card ≤ 2)
    (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' → Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ)
    {σ₀ : Finset V} (hσ₀ : IsTri L σ₀) :
    ∃ l : List (Cube V), Collapse.IsCollapse (spineInc L) l (topCubes L) := by
  refine Collapse.exists_isCollapse_of_connected (spineInc_card_le_two hedge)
    (connected_topCubes hdual hcover) (t₀ := posCube σ₀) ?_ (hasFreeFace_posCube hσ₀)
  simp_all

/-! ### The incidence hypothesis from the closed surface condition -/

open scoped Classical in
/-- If every edge of `L` lies in exactly two triangles, then the incidence hypothesis of the
collapse holds: an edge is enlarged to a triangle by at most two vertices.  (An `e` which is
not a face of `L` is enlarged by none.) -/
theorem hedge_of_edgeInTwoTriangles {L : ASC V} (h : ASC.EdgeInTwoTriangles L)
    (e : Finset V) (he : e.card = 2) :
    ((univ.filter fun j => j ∉ e).filter fun j => insert j e ∈ L.faces).card ≤ 2 := by
  by_cases hef : e ∈ L.faces
  · obtain ⟨v₁, v₂, -, -, -, huniq⟩ := h e hef he
    refine le_trans (Finset.card_le_card (?_ : _ ⊆ ({v₁, v₂} : Finset V))) (by
      simpa using Finset.card_insert_le v₁ {v₂})
    intro j hj
    simp at hj
    rcases huniq j ⟨hj.1, hj.2⟩ with rfl | rfl <;> simp
  · have : ((univ.filter fun j => j ∉ e).filter fun j => insert j e ∈ L.faces) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 ?_
      intro j _ hcon
      exact hef (L.down_closed hcon (Finset.subset_insert _ _))
    rw [this]
    simp

open scoped Classical in
/-- **The collapse of Lemma 3.2 (ii) for a closed surface `L`.**  This is
`FiniteChains.exists_spine_collapse` with the incidence hypothesis replaced by the closed
surface condition itself. -/
theorem exists_spine_collapse_of_surface {L : ASC V} (hsurf : ASC.EdgeInTwoTriangles L)
    (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' → Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ)
    {σ₀ : Finset V} (hσ₀ : IsTri L σ₀) :
    ∃ l : List (Cube V), Collapse.IsCollapse (spineInc L) l (topCubes L) :=
  exists_spine_collapse (hedge_of_edgeInTwoTriangles hsurf) hdual hcover hσ₀

/-! ### A nonempty instance: the boundary of the tetrahedron -/

end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

universe u v

/-! ### Products of commutators -/

/-- The product of the commutators `[f x, f y]` over a list of pairs `(x, y)`. -/
def commWord {ι : Type*} {G : Type*} [Group G] (f : ι → G) (ps : List (ι × ι)) : G :=
  (ps.map fun p => f p.1 * f p.2 * (f p.1)⁻¹ * (f p.2)⁻¹).prod

@[simp] theorem commWord_nil {ι : Type*} {G : Type*} [Group G] (f : ι → G) :
    commWord f [] = 1 := rfl

theorem commWord_cons {ι : Type*} {G : Type*} [Group G] (f : ι → G) (p : ι × ι)
    (ps : List (ι × ι)) :
    commWord f (p :: ps) = (f p.1 * f p.2 * (f p.1)⁻¹ * (f p.2)⁻¹) * commWord f ps := rfl

/-- A homomorphism carries the product of commutators to the product of commutators of the
images. -/
theorem map_commWord {ι : Type*} {G H : Type*} [Group G] [Group H] (φ : G →* H) (f : ι → G)
    (ps : List (ι × ι)) : φ (commWord f ps) = commWord (fun i => φ (f i)) ps := by
  induction ps with
  | nil => simp
  | cons p ps ih => rw [commWord_cons, map_mul, ih, commWord_cons]; simp

theorem commWord_congr {ι : Type*} {G : Type*} [Group G] {f g : ι → G} (h : ∀ i, f i = g i)
    (ps : List (ι × ι)) : commWord f ps = commWord g ps := by
  simp only [commWord, h]

/-! ### Two general facts about normal closures -/

/-- A homomorphism carries a normal closure into any normal closure containing the images of the
generators. -/
theorem map_mem_normalClosure {G H : Type*} [Group G] [Group H] (φ : G →* H) {S : Set G}
    {N : Set H} (hS : ∀ g ∈ S, φ g ∈ Subgroup.normalClosure N) {x : G}
    (hx : x ∈ Subgroup.normalClosure S) : φ x ∈ Subgroup.normalClosure N := by
  have hle : Subgroup.normalClosure S ≤ (Subgroup.normalClosure N).comap φ :=
    Subgroup.normalClosure_le_normal (fun g hg => hS g hg)
  exact hle hx

/-! ### The surface word is a consequence of the block relators -/

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-! ### The hypothesis (B1), derived -/

/-! ### The application -/

end Davis
end FiniteChains

namespace FiniteChains
namespace SurfaceWordExpansion

universe u

variable {α Jr I : Type u}
  (ρ : Jr ⊕ PUnit.{u + 1} → FreeGroup α) (w : I → FreeGroup α) (ps : List (I × I))

/-- The formal surface word in the newly named generators. -/
def formalSurface : FreeGroup (α ⊕ I) :=
  Davis.commWord (fun i => FreeGroup.of (Sum.inr i)) ps

/-- Retained relators, word definitions, and the formal surface relator. -/
def expandedRel : (Jr ⊕ I) ⊕ PUnit.{u + 1} → FreeGroup (α ⊕ I)
  | Sum.inl (Sum.inl j) => FreeGroup.map Sum.inl (ρ (Sum.inl j))
  | Sum.inl (Sum.inr i) => FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹
  | Sum.inr _ => formalSurface (α := α) ps

/-- Eliminate each new name by substituting the word it names. -/
def foldNames : FreeGroup (α ⊕ I) →* FreeGroup α :=
  FreeGroup.lift (Sum.elim FreeGroup.of w)

 theorem foldNames_map_inl (v : FreeGroup α) :
    foldNames w (FreeGroup.map (Sum.inl (β := I)) v) = v := by
  have h : (foldNames w).comp (FreeGroup.map (Sum.inl (β := I))) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro a
    simp [foldNames]
  exact DFunLike.congr_fun h v

 theorem foldNames_formalSurface :
    foldNames w (formalSurface (α := α) ps) = Davis.commWord w ps := by
  rw [formalSurface, Davis.map_commWord]
  apply Davis.commWord_congr
  intro i
  simp [foldNames]

/-- The defining relators identify each new name with the prescribed old word. -/
 theorem name_eq_word (i : I) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inr i)) : PresGroup (expandedRel ρ w ps)) =
      QuotientGroup.mk (FreeGroup.map Sum.inl (w i)) := by
  have h : (QuotientGroup.mk
      (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹) :
        PresGroup (expandedRel ρ w ps)) = 1 :=
    (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure ⟨Sum.inl (Sum.inr i), rfl⟩)
  change (QuotientGroup.mk' (relSub (expandedRel ρ w ps)))
    (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹) = 1 at h
  rw [map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

variable (hrho : ρ (Sum.inr PUnit.unit) = Davis.commWord w ps)

include hrho

 theorem old_relator_eq_one (j : Jr ⊕ PUnit.{u + 1}) :
    (QuotientGroup.mk (FreeGroup.map (Sum.inl (β := I)) (ρ j)) :
      PresGroup (expandedRel ρ w ps)) = 1 := by
  rcases j with j | s
  · exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure ⟨Sum.inl (Sum.inl j), rfl⟩)
  · cases s
    rw [hrho]
    let q := QuotientGroup.mk' (relSub (expandedRel ρ w ps))
    change q (FreeGroup.map Sum.inl (Davis.commWord w ps)) = 1
    rw [Davis.map_commWord, Davis.map_commWord]
    have he : Davis.commWord (fun i => q (FreeGroup.map Sum.inl (w i))) ps =
        q (formalSurface (α := α) ps) := by
      rw [formalSurface, Davis.map_commWord]
      exact Davis.commWord_congr (fun i => (name_eq_word ρ w ps i).symm) ps
    rw [he]
    exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure ⟨Sum.inr PUnit.unit, rfl⟩)

/-- The old generators map into the named presentation group. -/
def inclusion : PresGroup ρ →* PresGroup (expandedRel ρ w ps) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (expandedRel ρ w ps))).comp (FreeGroup.map Sum.inl))
    (by
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨j, rfl⟩
      exact old_relator_eq_one ρ w ps hrho j)

 theorem folded_relator_eq_one (j : (Jr ⊕ I) ⊕ PUnit.{u + 1}) :
    (QuotientGroup.mk (foldNames w (expandedRel ρ w ps j)) : PresGroup ρ) = 1 := by
  rcases j with j | s
  · rcases j with j | i
    · change (QuotientGroup.mk (foldNames w (FreeGroup.map Sum.inl (ρ (Sum.inl j)))) :
        PresGroup ρ) = 1
      rw [foldNames_map_inl]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩)
    · change (QuotientGroup.mk' (relSub ρ))
        (foldNames w (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹)) = 1
      rw [map_mul, map_inv, foldNames_map_inl]
      simp [foldNames]
  · cases s
    rw [show expandedRel ρ w ps (Sum.inr PUnit.unit) = formalSurface (α := α) ps from rfl,
      foldNames_formalSurface, ← hrho]
    exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure ⟨Sum.inr PUnit.unit, rfl⟩)

/-- Word substitution induces the inverse map on presented groups. -/
def elimination : PresGroup (expandedRel ρ w ps) →* PresGroup ρ :=
  QuotientGroup.lift _ ((QuotientGroup.mk' (relSub ρ)).comp (foldNames w)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact folded_relator_eq_one ρ w ps hrho j)

 theorem elimination_inclusion (g : PresGroup ρ) :
    elimination ρ w ps hrho (inclusion ρ w ps hrho g) = g := by
  induction g using QuotientGroup.induction_on with
  | H v =>
    change (QuotientGroup.mk (foldNames w (FreeGroup.map Sum.inl v)) : PresGroup ρ) = _
    rw [foldNames_map_inl]

 theorem inclusion_elimination (g : PresGroup (expandedRel ρ w ps)) :
    inclusion ρ w ps hrho (elimination ρ w ps hrho g) = g := by
  have h : ((QuotientGroup.mk' (relSub (expandedRel ρ w ps))).comp
      (FreeGroup.map (Sum.inl (β := I)))).comp (foldNames w) =
        QuotientGroup.mk' (relSub (expandedRel ρ w ps)) := by
    apply FreeGroup.ext_hom
    rintro (a | i)
    · simp [foldNames]
    · simpa [foldNames] using (name_eq_word ρ w ps i).symm
  induction g using QuotientGroup.induction_on with
  | H v => exact DFunLike.congr_fun h v

/-- Naming all the marked words preserves the original presentation group. -/
def groupEquiv : PresGroup ρ ≃* PresGroup (expandedRel ρ w ps) where
  toFun := inclusion ρ w ps hrho
  invFun := elimination ρ w ps hrho
  left_inv := elimination_inclusion ρ w ps hrho
  right_inv := inclusion_elimination ρ w ps hrho
  map_mul' := map_mul _

end SurfaceWordExpansion
end FiniteChains

namespace FiniteChains.NamedPresentation
variable {α J I : Type} (ρ : J → FreeGroup α) (w : I → FreeGroup α)

def rel : J ⊕ I → FreeGroup (α ⊕ I)
  | .inl j => FreeGroup.map Sum.inl (ρ j)
  | .inr i => FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹

theorem name_eq_word (i : I) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inr i)) : PresGroup (rel ρ w)) =
      QuotientGroup.mk (FreeGroup.map Sum.inl (w i)) := by
  have h : (QuotientGroup.mk
      (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹) : PresGroup (rel ρ w)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨Sum.inr i, rfl⟩)
  change (QuotientGroup.mk' (relSub (rel ρ w)))
    (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹) = 1 at h
  rw [map_mul, map_inv] at h
  exact (mul_inv_eq_one.mp h)

def inclusion : PresGroup ρ →* PresGroup (rel ρ w) :=
  QuotientGroup.lift _ ((QuotientGroup.mk' (relSub (rel ρ w))).comp (FreeGroup.map Sum.inl)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩))


def elimination : PresGroup (rel ρ w) →* PresGroup ρ :=
  QuotientGroup.lift _ ((QuotientGroup.mk' (relSub ρ)).comp (SurfaceWordExpansion.foldNames w)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact (by
      cases j with
      | inl j =>
        change (QuotientGroup.mk (SurfaceWordExpansion.foldNames w (FreeGroup.map Sum.inl (ρ j))) :
          PresGroup ρ) = 1
        rw [SurfaceWordExpansion.foldNames_map_inl]
        exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j, rfl⟩)
      | inr i =>
        change (QuotientGroup.mk' (relSub ρ))
          (SurfaceWordExpansion.foldNames w
            (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹)) = 1
        rw [map_mul, map_inv, SurfaceWordExpansion.foldNames_map_inl]
        simp [SurfaceWordExpansion.foldNames]))

theorem elimination_inclusion (g : PresGroup ρ) :
    elimination ρ w (inclusion ρ w g) = g := by
  induction g using QuotientGroup.induction_on with
  | H v =>
    change (QuotientGroup.mk (SurfaceWordExpansion.foldNames w (FreeGroup.map Sum.inl v))) = _
    rw [SurfaceWordExpansion.foldNames_map_inl]

theorem inclusion_elimination (g : PresGroup (rel ρ w)) :
    inclusion ρ w (elimination ρ w g) = g := by
  have h : ((QuotientGroup.mk' (relSub (rel ρ w))).comp
      (FreeGroup.map (Sum.inl))).comp (SurfaceWordExpansion.foldNames w) =
        QuotientGroup.mk' (relSub (rel ρ w)) := by
    apply FreeGroup.ext_hom
    rintro (a | i)
    · rfl
    · simpa [SurfaceWordExpansion.foldNames] using (name_eq_word ρ w i).symm
  induction g using QuotientGroup.induction_on with
  | H v => exact DFunLike.congr_fun h v

def groupEquiv : PresGroup ρ ≃* PresGroup (rel ρ w) where
  toFun := inclusion ρ w
  invFun := elimination ρ w
  left_inv := elimination_inclusion ρ w
  right_inv := inclusion_elimination ρ w
  map_mul' := map_mul _

end FiniteChains.NamedPresentation

namespace FiniteChains.NamedPresentation
variable {α J I : Type} [DecidableEq α] [DecidableEq I]
  (ρ : J → FreeGroup α) (w : I → FreeGroup α)

def wordCoefficientMap :
    FreeGroupRing α →+* MonoidAlgebra ℤ (PresGroup (rel ρ w)) :=
  (quotRingHom ℤ (relSub (rel ρ w))).comp (freeRingMap Sum.inl)

theorem matrix_internal_relator (a : α) (j : J) :
    foxMatrixPres (rel ρ w) (Sum.inl a) (Sum.inl j) =
      wordCoefficientMap ρ w (fox a (ρ j)) := by
  change quotRingHom ℤ _ (fox (Sum.inl a) (FreeGroup.map Sum.inl (ρ j))) = _
  rw [fox_map Sum.inl Sum.inl_injective]
  rfl

theorem matrix_marked_relator (i : I) (j : J) :
    foxMatrixPres (rel ρ w) (Sum.inr i) (Sum.inl j) = 0 := by
  change quotRingHom ℤ _ (fox (Sum.inr i) (FreeGroup.map Sum.inl (ρ j))) = 0
  rw [fox_map_of_not_mem_range Sum.inl (fun _ => Sum.inr_ne_inl), map_zero]

theorem matrix_internal_name (a : α) (i : I) :
    foxMatrixPres (rel ρ w) (Sum.inl a) (Sum.inr i) =
      -wordCoefficientMap ρ w (fox a (w i)) := by
  have hf : fox (Sum.inl a) (rel ρ w (Sum.inr i)) =
      -(grp (rel ρ w (Sum.inr i)) * freeRingMap Sum.inl (fox a (w i))) := by
    change fox (Sum.inl a) (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹) = _
    rw [fox_mul, fox_of, if_neg Sum.inl_ne_inr, zero_add, fox_inv,
      fox_map Sum.inl Sum.inl_injective, mul_neg, ← mul_assoc, ← grp_mul]
    rfl
  have hg : quotRingHom ℤ (relSub (rel ρ w)) (grp (rel ρ w (Sum.inr i))) = 1 := by
    have he : (QuotientGroup.mk (rel ρ w (Sum.inr i)) : PresGroup (rel ρ w)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨Sum.inr i, rfl⟩)
    change quotRingHom ℤ _ (MonoidAlgebra.single _ 1) = _
    rw [quotRingHom_single, he]
    rfl
  rw [foxMatrixPres, hf, map_neg, map_mul, hg, one_mul]
  rfl

theorem matrix_marked_name (i k : I) :
    foxMatrixPres (rel ρ w) (Sum.inr i) (Sum.inr k) = if i = k then 1 else 0 := by simp_all [foxMatrixPres, rel, fox_mul, fox_inv, fox_map_of_not_mem_range]

end FiniteChains.NamedPresentation

namespace FiniteChains.NamedPresentation
variable {α J I G : Type} [DecidableEq α] [DecidableEq I] [Fintype J] [Fintype I]
  [Group G] (ρ : J → FreeGroup α) (w : I → FreeGroup α)
  (φ : PresGroup (rel ρ w) →* G)

def receivedWordCoefficientMap : FreeGroupRing α →+* MonoidAlgebra ℤ G :=
  (MonoidAlgebra.mapDomainRingHom ℤ φ).comp (wordCoefficientMap ρ w)

def receivedFoxBoundary (β : J ⊕ I → MonoidAlgebra ℤ G)
    (g : α ⊕ I) : MonoidAlgebra ℤ G :=
  ∑ m, β m * MonoidAlgebra.mapDomainRingHom ℤ φ (foxMatrixPres (rel ρ w) g m)

/-- Vanishing at the internal generators is an equality between the old
two-boundary and the chain of the marked word paths, not an absolute cycle. -/
theorem receivedFoxBoundary_internal (β : J ⊕ I → MonoidAlgebra ℤ G) (a : α) :
    receivedFoxBoundary ρ w φ β (Sum.inl a) =
      (∑ j, β (Sum.inl j) * receivedWordCoefficientMap ρ w φ (fox a (ρ j))) -
      ∑ i, β (Sum.inr i) * receivedWordCoefficientMap ρ w φ (fox a (w i)) := by
  rw [receivedFoxBoundary, Fintype.sum_sum_type]
  simp only [matrix_internal_relator, matrix_internal_name, map_neg, mul_neg,
    Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

theorem receivedFoxBoundary_internal_zero_iff (β : J ⊕ I → MonoidAlgebra ℤ G) :
    (∀ a, receivedFoxBoundary ρ w φ β (Sum.inl a) = 0) ↔
      ∀ a, (∑ j, β (Sum.inl j) * receivedWordCoefficientMap ρ w φ (fox a (ρ j))) =
        ∑ i, β (Sum.inr i) * receivedWordCoefficientMap ρ w φ (fox a (w i)) := by
  simp only [receivedFoxBoundary_internal, sub_eq_zero]

end FiniteChains.NamedPresentation

namespace FiniteChains.Nerve
open FreeAbelianGroup
universe u
variable {P : Type u}

/-- Retain precisely the basis lists of length `n`. The augmentation has length zero. -/
def lengthProjection (n : ℕ) : Ch P →+ Ch P := by
  classical
  exact lift (fun l => if l.length = n then of l else 0)

@[simp] theorem lengthProjection_of (n : ℕ) (l : List P) :
    lengthProjection n (of l) = if l.length = n then of l else 0 := by
  simp [lengthProjection]

theorem lengthProjection_consMap_succ (n : ℕ) (a : P) (c : Ch P) :
    lengthProjection (n + 1) (consMap a c) = consMap a (lengthProjection n c) := by
  apply ext_apply (F := (lengthProjection (n + 1)).comp (consMap a))
    (G := (consMap a).comp (lengthProjection n))
  intro l
  simp
  split_ifs <;> simp

theorem lengthProjection_consMap_zero (a : P) (c : Ch P) :
    lengthProjection 0 (consMap a c) = 0 := by
  apply ext_apply (F := (lengthProjection 0).comp (consMap a)) (G := 0)
  intro l
  simp

/-- Every face in the boundary of a list has length one less than that list. -/
theorem lengthProjection_bdryOn (n : ℕ) (l : List P) :
    lengthProjection n (bdryOn l) = if l.length = n + 1 then bdryOn l else 0 := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
    cases n with
    | zero =>
      simp only [bdryOn_cons, map_sub, lengthProjection_of, lengthProjection_consMap_zero,
        sub_zero, List.length_cons, Nat.add_right_cancel_iff]
      split_ifs with h
      · simp_all
      · rfl
    | succ n =>
      rw [bdryOn_cons, map_sub, lengthProjection_of, lengthProjection_consMap_succ, ih]
      simp
      split_ifs <;> simp

/-- Degree projection commutes with boundary, with the required degree shift. -/
theorem lengthProjection_bdry (n : ℕ) (c : Ch P) :
    lengthProjection n (bdry c) = bdry (lengthProjection (n + 1) c) := by
  apply ext_apply (F := (lengthProjection n).comp bdry)
    (G := bdry.comp (lengthProjection (n + 1)))
  intro l
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, bdry_of,
    lengthProjection_bdryOn, lengthProjection_of]
  split_ifs <;> simp

@[simp] theorem lengthProjection_idempotent (n : ℕ) (c : Ch P) :
    lengthProjection n (lengthProjection n c) = lengthProjection n c := by
  apply ext_apply (F := (lengthProjection n).comp (lengthProjection n))
   
  intro l
  simp
  split_ifs with h <;> simp [h]

variable [Preorder P]

/-- Projecting a chain to one degree preserves its support in a subposet. -/
theorem lengthProjection_mem_incOn (n : ℕ) {A : P → Prop} {c : Ch P}
    (hc : c ∈ IncOn A) : lengthProjection n c ∈ IncOn A := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [lengthProjection_of]
    split_ifs
    · exact of_mem_incOn hl.1 hl.2
    · simp
  | zero => simp
  | add x y _ _ hx hy => simpa using AddSubgroup.add_mem _ hx hy
  | neg x _ hx => simp_all

theorem lengthProjection_mem_inc (n : ℕ) {c : Ch P} (hc : c ∈ Inc P) :
    lengthProjection n c ∈ Inc P := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [lengthProjection_of]
    split_ifs
    · exact of_mem_inc hl
    · simp
  | zero => simp
  | add x y _ _ hx hy => simpa using AddSubgroup.add_mem _ hx hy
  | neg x _ hx => simp_all

end FiniteChains.Nerve

namespace FiniteChains.Davis
open RACG Mirror
variable {V : Type} [DecidableEq V] {A : CommRel V}

/-- A new cut cell has dimension `σ.card - 1` and requires a nonempty simplex. -/
def CutCell (A : CommRel V) := {σ : Finset V // σ.Nonempty ∧ IsSimplex A σ}

/-- Retained (possibly truncated) cubes and the new simplicial cut cells. -/
abbrev TruncatedCell (A : CommRel V) := QOld A ⊕ CutCell A

def TruncatedFace : TruncatedCell A → TruncatedCell A → Prop
  | .inl c, .inl d => c.1 ≤ d.1
  | .inr σ, .inr τ => σ.1 ⊆ τ.1
  | .inr σ, .inl c => σ.1 ⊆ c.1.spx ∧ c.1.sgn = 0
  | .inl _, .inr _ => False

theorem qCube_sgn_zero_of_face {c d : QCube A} (h : c ≤ d) (hc : c.sgn = 0) :
    d.sgn = 0 := by
  funext v
  by_cases hv : v ∈ d.spx
  · exact d.sgn_eq_zero v hv
  · exact (h.2 v hv).symm.trans (congrFun hc v)

instance : PartialOrder (TruncatedCell A) where
  le := TruncatedFace
  le_refl c := by
    cases c with
    | inl c => exact le_refl c.1
    | inr c => exact Finset.Subset.refl c.1
  le_trans c d e hcd hde := by
    cases c with
    | inl c =>
      cases d with
      | inl d =>
        cases e with
        | inl e => exact le_trans hcd hde
        | inr e => exact False.elim hde
      | inr d => exact False.elim hcd
    | inr c =>
      cases d with
      | inl d =>
        cases e with
        | inl e => exact ⟨hcd.1.trans hde.1, qCube_sgn_zero_of_face hde hcd.2⟩
        | inr e => exact False.elim hde
      | inr d =>
        cases e with
        | inl e => exact ⟨hcd.trans hde.1, hde.2⟩
        | inr e => exact hcd.trans hde
  le_antisymm c d hcd hdc := by
    cases c with
    | inl c =>
      cases d with
      | inl d => exact congrArg Sum.inl (Subtype.ext (le_antisymm hcd hdc))
      | inr d => exact False.elim hcd
    | inr c =>
      cases d with
      | inl d => exact False.elim hdc
      | inr d => exact congrArg Sum.inr (Subtype.ext (Finset.Subset.antisymm hcd hdc))

/-- A cut cell meets precisely the positive cubes whose directions contain its simplex. -/
theorem cut_le_old_iff (σ : CutCell A) (c : QOld A) :
    (Sum.inr σ : TruncatedCell A) ≤ Sum.inl c ↔
      σ.1 ⊆ c.1.spx ∧ c.1.sgn = 0 := Iff.rfl

/-- Retained cubes embed as their actual truncated cells. -/
def oldCellIncl : QOld A → TruncatedCell A := Sum.inl

theorem oldCellIncl_monotone : Monotone (oldCellIncl (A := A)) := fun _ _ h => h

/-- Project a cut simplex to the positive cube containing it; retained cubes are fixed.
This supplies the comparison with the older cube-poset block model. -/
def truncatedCellRetraction : TruncatedCell A → QOld A
  | .inl c => c
  | .inr σ => posQCube ⟨σ.1, σ.2⟩

theorem truncatedCellRetraction_monotone : Monotone (truncatedCellRetraction (A := A)) := by
  intro c d h
  cases c with
  | inl c =>
    cases d with
    | inl d => exact h
    | inr d => exact False.elim h
  | inr σ =>
    cases d with
    | inl d =>
      refine ⟨h.1, ?_⟩
      intro v _
      change 0 = d.1.sgn v
      rw [h.2]
      rfl
    | inr τ => exact posQCube_monotone h

omit [DecidableEq V] in
@[simp] theorem truncatedCellRetraction_old (c : QOld A) :
    truncatedCellRetraction (oldCellIncl c) = c := rfl

/-- Every cell is a face of its retained-cube image. Thus the section and retraction
have a pointwise order homotopy, including the cut cells. -/
theorem truncatedCell_le_retraction (c : TruncatedCell A) :
    c ≤ oldCellIncl (truncatedCellRetraction c) := by
  cases c with
  | inl c => exact le_refl _
  | inr σ => exact ⟨Finset.Subset.refl _, rfl⟩

variable [Fintype V]

/-- The cut incidence can also be read directly from the coordinates used by the collapse. -/
theorem cut_le_old_coordinate_iff (σ : CutCell A) (c : QOld A) :
    (Sum.inr σ : TruncatedCell A) ≤ Sum.inl c ↔
      σ.1 ⊆ freeSet (qCubeToCoordinate c.1) ∧
        qCubeToCoordinate c.1 = posCube c.1.spx := by
  rw [cut_le_old_iff, freeSet_qCubeToCoordinate]
  constructor
  · rintro ⟨hs, hz⟩
    exact ⟨hs, qCubeToCoordinate_sgn_zero c.1 hz⟩
  · rintro ⟨hs, hz⟩
    refine ⟨hs, ?_⟩
    funext v
    by_cases hv : v ∈ c.1.spx
    · exact c.1.sgn_eq_zero v hv
    · rw [← qCubeToCoordinate_parity c.1 v, hz]
      simp [posCube, hv]

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror
variable {V : Type} [DecidableEq V] {A : CommRel V}

def truncatedCellDimension : TruncatedCell A → ℕ
  | .inl c => c.1.spx.card
  | .inr σ => σ.1.card - 1

/-- Every proper face has strictly smaller dimension, including the new cut faces. -/
theorem truncatedCellDimension_strictMono : StrictMono (truncatedCellDimension (A := A)) := by
  intro c d hcd
  have hle := hcd.le
  have hne := hcd.ne
  cases c with
  | inl c =>
    cases d with
    | inl d =>
      change c.1.spx.card < d.1.spx.card
      have hc := Finset.card_le_card hle.1
      by_contra hnot
      have hs  :=
        Finset.eq_of_subset_of_card_le hle.1 (by omega)
      exact hne (congrArg Sum.inl (Subtype.ext (QCube.ext' hs hle.2)))
    | inr σ => exact False.elim hle
  | inr σ =>
    cases d with
    | inl d =>
      change σ.1.card - 1 < d.1.spx.card
      change σ.1 ⊆ d.1.spx ∧ d.1.sgn = 0 at hle
      have hc := Finset.card_le_card hle.1
      have hp := Finset.card_pos.mpr σ.2.1
      omega
    | inr τ =>
      change σ.1.card - 1 < τ.1.card - 1
      change σ.1 ⊆ τ.1 at hle
      have hc := Finset.card_le_card hle
      have hσ := Finset.card_pos.mpr σ.2.1
      have hτ := Finset.card_pos.mpr τ.2.1
      by_contra hnot
      have hs : σ.1 = τ.1 := Finset.eq_of_subset_of_card_le hle (by omega)
      exact hne (congrArg Sum.inr (Subtype.ext hs))

theorem truncatedCellDimension_monotone : Monotone (truncatedCellDimension (A := A)) :=
  truncatedCellDimension_strictMono.monotone

theorem truncatedCell_eq_of_le_of_dimension_eq {c d : TruncatedCell A}
    (hcd : c ≤ d) (hd : truncatedCellDimension c = truncatedCellDimension d) : c = d := by
  by_contra hne
  have hlt := truncatedCellDimension_strictMono (lt_of_le_of_ne hcd hne)
  omega

/-- The same indices as the geometric and oriented collapse routines. -/
def truncatedFaceIndex : TruncatedCell A → Cube V ⊕ Finset V
  | .inl c => .inl (qCubeToCoordinate c.1)
  | .inr σ => .inr σ.1

variable [Fintype V]

theorem truncatedFaceIndex_injective : Function.Injective (truncatedFaceIndex (A := A)) := by
  intro c d he
  cases c with
  | inl c =>
    cases d with
    | inl d =>
      have hcoord  := Sum.inl.inj he
      have hcube  := qCubeCoordinateEquiv.injective (Subtype.ext hcoord)
      exact congrArg Sum.inl (Subtype.ext hcube)
    | inr σ => cases he
  | inr σ =>
    cases d with
    | inl d => cases he
    | inr τ => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj he))

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

theorem mem_cofaces_of_coordinateFace {L : ASC V} {c d : Cube V}
    (hface : CoordinateFace c d) (hc : (freeSet c).card = 2)
    (hd : (freeSet d).card = 3) (hL : freeSet d ∈ L.faces) : d ∈ cofaces L c := by
  have hsub : freeSet c ⊆ freeSet d := by
    intro v hv
    have hvf := mem_freeSet.mp hv
    rcases hface v with h | h
    · simp_all
    · simp_all
  have hcard : (freeSet d \ freeSet c).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hc, hd]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hjd  := (Finset.mem_sdiff.mp
    (hj ▸ Finset.mem_singleton_self j)).1
  have hjc  := (Finset.mem_sdiff.mp
    (hj ▸ Finset.mem_singleton_self j)).2
  have hset : freeSet d = insert j (freeSet c) := by
    ext v
    constructor
    · intro hv
      by_cases hvc : v ∈ freeSet c
      · exact Finset.mem_insert_of_mem hvc
      · have hm  := Finset.mem_sdiff.mpr ⟨hv, hvc⟩
        rw [hj] at hm
        exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hm))
    · grind
  apply mem_cofaces.mpr
  refine ⟨j, (fun h => hjc (mem_freeSet.mpr h)), hset ▸ hL, ?_⟩
  funext v
  by_cases hvj : v = j
  · subst v
    simpa using mem_freeSet.mp hjd
  · rw [Function.update_of_ne hvj]
    by_cases hvd : v ∈ freeSet d
    · have hvc : v ∈ freeSet c := by
        rw [hset] at hvd
        exact (Finset.mem_insert.mp hvd).resolve_left hvj
      exact (mem_freeSet.mp hvd).trans (mem_freeSet.mp hvc).symm
    · exact ((hface v).resolve_left (fun h => hvd (mem_freeSet.mpr h))).symm

theorem truncatedCell_inc_of_le {L : ASC V} (c : TruncatedCell A) (d : QOld A)
    (hcd : c ≤ Sum.inl d) (hc : truncatedCellDimension c = 2)
    (hd : d.1.spx.card = 3) (hL : d.1.spx ∈ L.faces) :
    qCubeToCoordinate d.1 ∈ spineInc L (truncatedFaceIndex c) := by
  cases c with
  | inl c =>
    have hf := (qCubeToCoordinate_face_iff c.1 d.1).mp hcd
    have hdim : (freeSet (qCubeToCoordinate c.1)).card = 2 := by
      simpa [truncatedCellDimension] using hc
    have hc' : c.1.spx.card = 2 := hc
    simpa [spineInc, truncatedFaceIndex, hc'] using
      mem_cofaces_of_coordinateFace hf hdim
        (by simpa using hd) (by simpa using hL)
  | inr σ =>
    have hsub  := hcd.1
    have hσ : σ.1.card = 3 := by
      have hp := Finset.card_pos.mpr σ.2.1
      change σ.1.card - 1 = 2 at hc
      omega
    have he : σ.1 = d.1.spx :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have ht : IsTri L σ.1 := ⟨he ▸ hL, hσ⟩
    have ht' := he ▸ ht
    have hz := qCubeToCoordinate_sgn_zero d.1 hcd.2
    simp [spineInc, truncatedFaceIndex, ht', hz, he]

theorem truncatedCell_le_of_inc {L : ASC V} (c : TruncatedCell A) (d : QOld A)
    (hi : qCubeToCoordinate d.1 ∈ spineInc L (truncatedFaceIndex c)) :
    c ≤ Sum.inl d := by
  cases c with
  | inl c =>
    have hm : qCubeToCoordinate d.1 ∈ cofaces L (qCubeToCoordinate c.1) := by
      simp only [spineInc, truncatedFaceIndex] at hi
      split at hi
      · exact hi
      · simp at hi
    obtain ⟨j, _, _, he⟩ := mem_cofaces.mp hm
    apply (qCubeToCoordinate_face_iff c.1 d.1).mpr
    intro v
    rw [he]
    by_cases hv : v = j
    · simp_all
    · simp_all
  | inr σ =>
    have he : qCubeToCoordinate d.1 = posCube σ.1 := by
      simp only [spineInc, truncatedFaceIndex] at hi
      split at hi
      · simp_all
      · simp at hi
    have hs : d.1.spx = σ.1 := by
      have hh := congrArg freeSet he
      simpa using hh
    apply (cut_le_old_coordinate_iff σ d).mpr
    exact ⟨by simp [hs], by simpa [hs] using he⟩

end FiniteChains.Davis

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

/-- The cells of the polygon with identified boundary. -/
inductive Cell (κ ι : Type u) (M : ℕ) : Type u
  /-- A vertex of the identified boundary. -/
  | vtx (v : κ) : Cell κ ι M
  /-- An edge of the identified boundary. -/
  | bed (e : ι) : Cell κ ι M
  /-- A vertex of the collar. -/
  | cvx (p : Fin M) : Cell κ ι M
  /-- An edge of the collar. -/
  | ced (p : Fin M) : Cell κ ι M
  /-- The edge joining the boundary vertex at `p` to the collar vertex at `p`. -/
  | dia (p : Fin M) : Cell κ ι M
  /-- The edge joining the boundary vertex at `p` to the collar vertex at `p+1`. -/
  | gdi (p : Fin M) : Cell κ ι M
  /-- The triangle on the boundary edge at `p` and the collar vertex at `p+1`. -/
  | tr1 (p : Fin M) : Cell κ ι M
  /-- The triangle on the collar edge at `p` and the boundary vertex at `p`. -/
  | tr2 (p : Fin M) : Cell κ ι M
  /-- The centre of the polygon. -/
  | ctr : Cell κ ι M
  /-- The radius from the centre to the collar vertex at `p`. -/
  | rad (p : Fin M) : Cell κ ι M
  /-- The triangle of the fan on the collar edge at `p`. -/
  | inn (p : Fin M) : Cell κ ι M
  deriving DecidableEq

namespace Cell

variable {κ ι : Type u} {M : ℕ}

/-- The dimension of a cell. -/
def rk : Cell κ ι M → ℕ
  | vtx _ => 0
  | bed _ => 1
  | cvx _ => 0
  | ced _ => 1
  | dia _ => 1
  | gdi _ => 1
  | tr1 _ => 2
  | tr2 _ => 2
  | ctr => 0
  | rad _ => 1
  | inn _ => 2

instance [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] :
    Fintype (Cell κ ι M) where
  elems :=
    (Finset.univ.image vtx) ∪ (Finset.univ.image bed) ∪ (Finset.univ.image cvx) ∪
      (Finset.univ.image ced) ∪ (Finset.univ.image dia) ∪ (Finset.univ.image gdi) ∪
      (Finset.univ.image tr1) ∪ (Finset.univ.image tr2) ∪ {ctr} ∪
      (Finset.univ.image rad) ∪ (Finset.univ.image inn)
  complete := by
    intro x
    cases x <;> simp

end Cell

section Order

variable {κ ι : Type u} {M : ℕ} [NeZero M]

open Cell

/-- **The strict face order of the polygon with identified boundary.** -/
def plt (vc : Fin M → κ) (ec : Fin M → ι) : Cell κ ι M → Cell κ ι M → Prop
  | vtx v, bed e => ∃ i, ec i = e ∧ (vc i = v ∨ vc (i + 1) = v)
  | vtx v, dia p => vc p = v
  | vtx v, gdi p => vc p = v
  | cvx q, ced r => q = r ∨ q = r + 1
  | cvx q, dia r => q = r
  | cvx q, gdi r => q = r + 1
  | cvx q, rad r => q = r
  | ctr, rad _ => True
  | bed e, tr1 p => e = ec p
  | ced r, tr2 p => r = p
  | ced r, inn p => r = p
  | dia r, tr1 p => r = p + 1
  | dia r, tr2 p => r = p
  | gdi r, tr1 p => r = p
  | gdi r, tr2 p => r = p
  | rad r, inn p => r = p ∨ r = p + 1
  | vtx v, tr1 p => vc p = v ∨ vc (p + 1) = v
  | vtx v, tr2 p => vc p = v
  | cvx q, tr1 p => q = p + 1
  | cvx q, tr2 p => q = p ∨ q = p + 1
  | cvx q, inn p => q = p ∨ q = p + 1
  | ctr, inn _ => True
  | _, _ => False

variable {vc : Fin M → κ} {ec : Fin M → ι}

theorem rk_lt_of_plt {x y : Cell κ ι M} (h : plt vc ec x y) : x.rk < y.rk := by
  cases x <;> cases y <;> simp_all [plt, rk]

theorem plt_irrefl (x : Cell κ ι M) : ¬ plt vc ec x x := fun h => absurd (rk_lt_of_plt h) (by omega)

theorem not_plt_of_rk_le {x y : Cell κ ι M} (h : y.rk ≤ x.rk) : ¬ plt vc ec x y :=
  fun hh => absurd (rk_lt_of_plt hh) (by omega)

omit [NeZero M] in
theorem rk_le_two (x : Cell κ ι M) : x.rk ≤ 2 := by cases x <;> simp [rk]


/-- **The compatibility of the identification of the boundary with the identification of its
endpoints**: two positions of the polygon carrying the same edge of the surface carry, in one of
the two orders, the same pair of endpoints. -/
def Compat (vc : Fin M → κ) (ec : Fin M → ι) : Prop :=
  ∀ i j : Fin M, ec i = ec j →
    (vc i = vc j ∧ vc (i + 1) = vc (j + 1)) ∨ (vc i = vc (j + 1) ∧ vc (i + 1) = vc j)

theorem plt_trans (hc : Compat vc ec) {x y z : Cell κ ι M} (hxy : plt vc ec x y)
    (hyz : plt vc ec y z) : plt vc ec x z := by
  cases y with
  | vtx _ => exact absurd hxy (not_plt_of_rk_le (Nat.zero_le _))
  | cvx _ => exact absurd hxy (not_plt_of_rk_le (Nat.zero_le _))
  | ctr => exact absurd hxy (not_plt_of_rk_le (Nat.zero_le _))
  | tr1 _ => exact absurd hyz (not_plt_of_rk_le (rk_le_two z))
  | tr2 _ => exact absurd hyz (not_plt_of_rk_le (rk_le_two z))
  | inn _ => exact absurd hyz (not_plt_of_rk_le (rk_le_two z))
  | bed e =>
      cases x with
      | vtx v =>
          cases z with
          | tr1 p =>
              obtain ⟨i, hi, hv⟩ := hxy
              have hep : ec i = ec p := by rw [hi]; exact hyz
              rcases hc i p hep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hv with rfl | rfl
              · exact Or.inl h1.symm
              · exact Or.inr h2.symm
              · exact Or.inr h1.symm
              · exact Or.inl h2.symm
          | _ => simp [plt] at hyz
      | _ => simp [plt] at hxy
  | ced r =>
      cases x with
      | cvx q =>
          cases z with
          | tr2 p =>
              have h  := hyz
              subst h
              exact hxy
          | inn p =>
              have h  := hyz
              subst h
              exact hxy
          | _ => simp [plt] at hyz
      | _ => simp [plt] at hxy
  | dia r =>
      cases x with
      | vtx v =>
          cases z with
          | tr1 p =>
              have hr  := hyz
              subst hr
              exact Or.inr hxy
          | tr2 p =>
              have hr  := hyz
              subst hr
              exact hxy
          | _ => simp [plt] at hyz
      | cvx q =>
          cases z with
          | tr1 p =>
              have hr  := hyz
              have hq  := hxy
              show q = p + 1
              rw [hq, hr]
          | tr2 p =>
              have hr  := hyz
              have hq  := hxy
              exact Or.inl (by rw [hq, hr])
          | _ => simp [plt] at hyz
      | _ => simp [plt] at hxy
  | gdi r =>
      cases x with
      | vtx v =>
          cases z with
          | tr1 p =>
              have hr : r = p := hyz
              subst hr
              exact Or.inl hxy
          | tr2 p =>
              have hr : r = p := hyz
              subst hr
              exact hxy
          | _ => simp [plt] at hyz
      | cvx q =>
          cases z with
          | tr1 p =>
              have hr : r = p := hyz
              have hq : q = r + 1 := hxy
              show q = p + 1
              rw [hq, hr]
          | tr2 p =>
              have hr : r = p := hyz
              have hq : q = r + 1 := hxy
              show q = p ∨ q = p + 1
              exact Or.inr (by rw [hq, hr])
          | _ => simp [plt] at hyz
      | _ => simp [plt] at hxy
  | rad r =>
      cases x with
      | cvx q =>
          cases z with
          | inn p =>
              have hq : q = r := hxy
              show q = p ∨ q = p + 1
              rcases hyz with hr | hr
              · omega
              · omega
          | _ => simp [plt] at hyz
      | ctr =>
          cases z with
          | inn p => trivial
          | _ => simp [plt] at hyz
      | _ => simp [plt] at hxy

/-! ### The face poset -/

/-- **The face poset of the polygon with identified boundary.** -/
def SCell (_vc : Fin M → κ) (_ec : Fin M → ι) (_hc : Compat vc ec) : Type u := Cell κ ι M

variable (vc ec) in
/-- The order of the face poset: equality or a strict face. -/
def sle (_hc : Compat vc ec) (x y : Cell κ ι M) : Prop := x = y ∨ plt vc ec x y

instance instPartialOrderSCell (hc : Compat vc ec) : PartialOrder (SCell vc ec hc) where
  le x y := sle vc ec hc x y
  le_refl _ := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | h1
    · exact hbc
    rcases hbc with rfl | h2
    · exact Or.inr h1
    exact Or.inr (plt_trans hc h1 h2)
  le_antisymm a b hab hba := by
    rcases hab with rfl | h1
    · rfl
    rcases hba with rfl | h2
    · rfl
    exact absurd h2 (by
      intro h'
      have := rk_lt_of_plt h1
      have := rk_lt_of_plt h'
      omega)

instance instDecidableEqSCell [DecidableEq κ] [DecidableEq ι] (hc : Compat vc ec) :
    DecidableEq (SCell vc ec hc) := inferInstanceAs (DecidableEq (Cell κ ι M))

instance instFintypeSCell [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (hc : Compat vc ec) : Fintype (SCell vc ec hc) := inferInstanceAs (Fintype (Cell κ ι M))

variable (vc ec)

/-- A cell of the poset, from a cell of the polygon. -/
def toS (hc : Compat vc ec) (x : Cell κ ι M) : SCell vc ec hc := x

variable {vc ec}

theorem le_of_plt (hc : Compat vc ec) {x y : Cell κ ι M} (h : plt vc ec x y) :
    toS vc ec hc x ≤ toS vc ec hc y := Or.inr h

end Order

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb Cell

universe u

section Cells

variable {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι}

/-- The barycentric subdivision of the triangulation of the surface, as a two-complex: the order
complex of the poset of nonempty chains of cells. -/
abbrev sdCx (hc : Compat vc ec) : Complex2.{u} :=
  orderCx (NeSpx (cmpRel (SCell vc ec hc)))

/-! ### The cells -/

/-- The boundary vertex at the position `p`. -/
def cV (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (vtx (vc p))

/-- The boundary edge at the position `p`. -/
def cE (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (bed (ec p))

/-- The collar vertex at the position `p`. -/
def cW (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (cvx p)

/-- The collar edge at the position `p`. -/
def cF (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (ced p)

/-- The edge from the boundary vertex at `p` to the collar vertex at `p`. -/
def cD (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (dia p)

/-- The edge from the boundary vertex at `p` to the collar vertex at `p+1`. -/
def cG (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (gdi p)

/-- The outer triangle at the position `p`. -/
def cT1 (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (tr1 p)

/-- The inner triangle of the collar at the position `p`. -/
def cT2 (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (tr2 p)

/-- The centre of the polygon. -/
def cC (hc : Compat vc ec) : SCell vc ec hc := toS vc ec hc ctr

/-- The radius at the position `p`. -/
def cR (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (rad p)

/-- The triangle of the fan at the position `p`. -/
def cI (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (inn p)

variable (hc : Compat vc ec)

/-! ### The incidences -/

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV_le_cE (p : Fin M) : cV hc p ≤ cE hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc p)) (bed (ec p)) from ⟨p, rfl, Or.inl rfl⟩)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV1_le_cE (p : Fin M) : cV hc (p + 1) ≤ cE hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc (p + 1))) (bed (ec p)) from ⟨p, rfl, Or.inr rfl⟩)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV_le_cD (p : Fin M) : cV hc p ≤ cD hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc p)) (dia p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW_le_cD (p : Fin M) : cW hc p ≤ cD hc p :=
  le_of_plt hc (show plt vc ec (cvx p) (dia p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV_le_cG (p : Fin M) : cV hc p ≤ cG hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc p)) (gdi p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW1_le_cG (p : Fin M) : cW hc (p + 1) ≤ cG hc p :=
  le_of_plt hc (show plt vc ec (cvx (p + 1)) (gdi p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW_le_cF (p : Fin M) : cW hc p ≤ cF hc p :=
  le_of_plt hc (show plt vc ec (cvx p) (ced p) from Or.inl rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW1_le_cF (p : Fin M) : cW hc (p + 1) ≤ cF hc p :=
  le_of_plt hc (show plt vc ec (cvx (p + 1)) (ced p) from Or.inr rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cC_le_cR (p : Fin M) : cC hc ≤ cR hc p :=
  le_of_plt hc (show plt vc ec ctr (rad p) from trivial)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW_le_cR (p : Fin M) : cW hc p ≤ cR hc p :=
  le_of_plt hc (show plt vc ec (cvx p) (rad p) from rfl)

/-! ### The faces of the three triangles -/

omit [DecidableEq κ] [DecidableEq ι] in
theorem cE_le_cT1 (p : Fin M) : cE hc p ≤ cT1 hc p :=
  le_of_plt hc (show plt vc ec (bed (ec p)) (tr1 p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cD1_le_cT1 (p : Fin M) : cD hc (p + 1) ≤ cT1 hc p :=
  le_of_plt hc (show plt vc ec (dia (p + 1)) (tr1 p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cG_le_cT1 (p : Fin M) : cG hc p ≤ cT1 hc p :=
  le_of_plt hc (show plt vc ec (gdi p) (tr1 p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV_le_cT1 (p : Fin M) : cV hc p ≤ cT1 hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc p)) (tr1 p) from Or.inl rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV1_le_cT1 (p : Fin M) : cV hc (p + 1) ≤ cT1 hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc (p + 1))) (tr1 p) from Or.inr rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW1_le_cT1 (p : Fin M) : cW hc (p + 1) ≤ cT1 hc p :=
  le_of_plt hc (show plt vc ec (cvx (p + 1)) (tr1 p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cD_le_cT2 (p : Fin M) : cD hc p ≤ cT2 hc p :=
  le_of_plt hc (show plt vc ec (dia p) (tr2 p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cF_le_cT2 (p : Fin M) : cF hc p ≤ cT2 hc p :=
  le_of_plt hc (show plt vc ec (ced p) (tr2 p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cG_le_cT2 (p : Fin M) : cG hc p ≤ cT2 hc p :=
  le_of_plt hc (show plt vc ec (gdi p) (tr2 p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV_le_cT2 (p : Fin M) : cV hc p ≤ cT2 hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc p)) (tr2 p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW_le_cT2 (p : Fin M) : cW hc p ≤ cT2 hc p :=
  le_of_plt hc (show plt vc ec (cvx p) (tr2 p) from Or.inl rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW1_le_cT2 (p : Fin M) : cW hc (p + 1) ≤ cT2 hc p :=
  le_of_plt hc (show plt vc ec (cvx (p + 1)) (tr2 p) from Or.inr rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cR_le_cI (p : Fin M) : cR hc p ≤ cI hc p :=
  le_of_plt hc (show plt vc ec (rad p) (inn p) from Or.inl rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cR1_le_cI (p : Fin M) : cR hc (p + 1) ≤ cI hc p :=
  le_of_plt hc (show plt vc ec (rad (p + 1)) (inn p) from Or.inr rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cF_le_cI (p : Fin M) : cF hc p ≤ cI hc p :=
  le_of_plt hc (show plt vc ec (ced p) (inn p) from rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cC_le_cI (p : Fin M) : cC hc ≤ cI hc p :=
  le_of_plt hc (show plt vc ec ctr (inn p) from trivial)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW_le_cI (p : Fin M) : cW hc p ≤ cI hc p :=
  le_of_plt hc (show plt vc ec (cvx p) (inn p) from Or.inl rfl)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW1_le_cI (p : Fin M) : cW hc (p + 1) ≤ cI hc p :=
  le_of_plt hc (show plt vc ec (cvx (p + 1)) (inn p) from Or.inr rfl)

/-! ### The paths -/

/-- The boundary edge at `p`, crossed from the vertex at `p` to the vertex at `p+1`. -/
def bdEdge (p : Fin M) :
    List ((orderCx (NeSpx (cmpRel (SCell vc ec hc)))).E × Bool) :=
  edgeHop (cV_le_cE hc p) ++ edgeHopRev (cV1_le_cE hc p)

/-- From the collar vertex at `p` to the boundary vertex at `p`. -/
def delta (p : Fin M) :
    List ((orderCx (NeSpx (cmpRel (SCell vc ec hc)))).E × Bool) :=
  edgeHop (cW_le_cD hc p) ++ edgeHopRev (cV_le_cD hc p)

/-- Along the collar, from `p` to `p+1`. -/
def gam (p : Fin M) :
    List ((orderCx (NeSpx (cmpRel (SCell vc ec hc)))).E × Bool) :=
  edgeHop (cW_le_cF hc p) ++ edgeHopRev (cW1_le_cF hc p)

/-- The diagonal, from the boundary vertex at `p` to the collar vertex at `p+1`. -/
def gg (p : Fin M) :
    List ((orderCx (NeSpx (cmpRel (SCell vc ec hc)))).E × Bool) :=
  edgeHop (cV_le_cG hc p) ++ edgeHopRev (cW1_le_cG hc p)

/-- From the centre to the collar vertex at `p`. -/
def alph (p : Fin M) :
    List ((orderCx (NeSpx (cmpRel (SCell vc ec hc)))).E × Bool) :=
  edgeHop (cC_le_cR hc p) ++ edgeHopRev (cW_le_cR hc p)

/-- From the centre to the boundary vertex at `p`. -/
def ray (p : Fin M) :
    List ((orderCx (NeSpx (cmpRel (SCell vc ec hc)))).E × Bool) :=
  alph hc p ++ delta hc p

theorem isPath_bdEdge (p : Fin M) :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (bdEdge hc p)
      (spx1 (cV hc p)) (spx1 (cV hc (p + 1))) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_delta (p : Fin M) :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (delta hc p)
      (spx1 (cW hc p)) (spx1 (cV hc p)) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_gam (p : Fin M) :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (gam hc p)
      (spx1 (cW hc p)) (spx1 (cW hc (p + 1))) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_gg (p : Fin M) :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (gg hc p)
      (spx1 (cV hc p)) (spx1 (cW hc (p + 1))) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_alph (p : Fin M) :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (alph hc p)
      (spx1 (cC hc)) (spx1 (cW hc p)) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_ray (p : Fin M) :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (ray hc p)
      (spx1 (cC hc)) (spx1 (cV hc p)) :=
  (isPath_alph hc p).append (isPath_delta hc p)

/-! ### The paths inside the stars of the three triangles -/

theorem pathIn_bdEdge_T1 (p : Fin M) :
    PathIn (StarCh (cT1 hc p)) (bdEdge hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cV_le_cT1 hc p) (cE_le_cT1 hc p))
    (pathIn_edgeHopRev _ (cV1_le_cT1 hc p) (cE_le_cT1 hc p))

theorem pathIn_gg_T1 (p : Fin M) : PathIn (StarCh (cT1 hc p)) (gg hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cV_le_cT1 hc p) (cG_le_cT1 hc p))
    (pathIn_edgeHopRev _ (cW1_le_cT1 hc p) (cG_le_cT1 hc p))

theorem pathIn_delta1_T1 (p : Fin M) : PathIn (StarCh (cT1 hc p)) (delta hc (p + 1)) :=
  pathIn_append' (pathIn_edgeHop _ (cW1_le_cT1 hc p) (cD1_le_cT1 hc p))
    (pathIn_edgeHopRev _ (cV1_le_cT1 hc p) (cD1_le_cT1 hc p))

theorem pathIn_delta_T2 (p : Fin M) : PathIn (StarCh (cT2 hc p)) (delta hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cW_le_cT2 hc p) (cD_le_cT2 hc p))
    (pathIn_edgeHopRev _ (cV_le_cT2 hc p) (cD_le_cT2 hc p))

theorem pathIn_gam_T2 (p : Fin M) : PathIn (StarCh (cT2 hc p)) (gam hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cW_le_cT2 hc p) (cF_le_cT2 hc p))
    (pathIn_edgeHopRev _ (cW1_le_cT2 hc p) (cF_le_cT2 hc p))

theorem pathIn_gg_T2 (p : Fin M) : PathIn (StarCh (cT2 hc p)) (gg hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cV_le_cT2 hc p) (cG_le_cT2 hc p))
    (pathIn_edgeHopRev _ (cW1_le_cT2 hc p) (cG_le_cT2 hc p))

theorem pathIn_alph_I (p : Fin M) : PathIn (StarCh (cI hc p)) (alph hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cC_le_cI hc p) (cR_le_cI hc p))
    (pathIn_edgeHopRev _ (cW_le_cI hc p) (cR_le_cI hc p))

theorem pathIn_alph1_I (p : Fin M) : PathIn (StarCh (cI hc p)) (alph hc (p + 1)) :=
  pathIn_append' (pathIn_edgeHop _ (cC_le_cI hc p) (cR1_le_cI hc p))
    (pathIn_edgeHopRev _ (cW1_le_cI hc p) (cR1_le_cI hc p))

theorem pathIn_gam_I (p : Fin M) : PathIn (StarCh (cI hc p)) (gam hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cW_le_cI hc p) (cF_le_cI hc p))
    (pathIn_edgeHopRev _ (cW1_le_cI hc p) (cF_le_cI hc p))

end Cells

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel

universe u

/-! ### The cycle graph -/




/-! ### The labels -/

section Labels

variable {α : Type u}

/-- The label of the vertex at the position `p` of the cycle: even positions are corners of the
word and carry the base vertex of the rose, odd positions are midpoints of letters and carry the
midpoint of the loop of the corresponding generator. -/
def vertLab (l : List (α × Bool)) (p : ℕ) : Rose α :=
  if p % 2 = 0 then Rose.base
  else
    match l[p / 2]? with
    | some q => Rose.mid q.1
    | none => Rose.base

/-- The label of the edge joining the positions `p` and `p+1` of the cycle: the first half of the
letter `p/2` for even `p`, its second half for odd `p`, the halves being taken in the order
prescribed by the sign of the letter. -/
def edgeLab (l : List (α × Bool)) (p : ℕ) : Rose α :=
  match l[p / 2]? with
  | some q => Rose.edg q.1 (if p % 2 = 0 then !q.2 else q.2)
  | none => Rose.base

@[simp] theorem vertLab_of_even {l : List (α × Bool)} {p : ℕ} (hp : p % 2 = 0) :
    vertLab l p = Rose.base := if_pos hp

theorem vertLab_of_odd {l : List (α × Bool)} {p : ℕ} {q : α × Bool} (hp : p % 2 = 1)
    (hq : l[p / 2]? = some q) : vertLab l p = Rose.mid q.1 := by
  simp [vertLab, hp, hq]

theorem edgeLab_eq {l : List (α × Bool)} {p : ℕ} {q : α × Bool} (hq : l[p / 2]? = some q) :
    edgeLab l p = Rose.edg q.1 (if p % 2 = 0 then !q.2 else q.2) := by
  simp [edgeLab, hq]

theorem getElem?_half {l : List (α × Bool)} {p : ℕ} (hp : p < 2 * l.length) :
    ∃ q, l[p / 2]? = some q :=
  ⟨l[p / 2]'(by omega), List.getElem?_eq_getElem (by omega)⟩

/-- The vertex at a position lies under the edge that starts at it. -/
theorem vertLab_le_edgeLab {l : List (α × Bool)} {p : ℕ} (hp : p < 2 * l.length) :
    vertLab l p ≤ edgeLab l p := by
  obtain ⟨q, hq⟩ := getElem?_half hp
  rcases Nat.even_or_odd p with he | ho
  · have h0  := Nat.even_iff.1 he
    rw [vertLab_of_even h0, edgeLab_eq hq]
    exact Rose.base_le_edg _ _
  · have h1  := Nat.odd_iff.1 ho
    rw [vertLab_of_odd h1 hq, edgeLab_eq hq, if_neg (by omega)]
    exact Rose.mid_le_edg _ _

/-- The vertex at the next position lies under the same edge. -/
theorem vertLab_succ_le_edgeLab {l : List (α × Bool)} {p : ℕ} (hp : p + 1 < 2 * l.length) :
    vertLab l (p + 1) ≤ edgeLab l p := by
  obtain ⟨q, hq⟩ := getElem?_half (Nat.lt_of_succ_lt hp)
  rcases Nat.even_or_odd p with he | ho
  · have h0  := Nat.even_iff.1 he
    have hhalf : (p + 1) / 2 = p / 2 := by omega
    rw [vertLab_of_odd (by omega) (by rw [hhalf]; exact hq), edgeLab_eq hq,
      if_pos h0]
    exact Rose.mid_le_edg _ _
  · have h1  := Nat.odd_iff.1 ho
    rw [vertLab_of_even (by omega), edgeLab_eq hq]
    exact Rose.base_le_edg _ _

/-- Every edge of the cycle carries a one-cell of the rose, so the base vertex lies under it. -/
theorem base_le_edgeLab {l : List (α × Bool)} {p : ℕ} (hp : p < 2 * l.length) :
    (Rose.base : Rose α) ≤ edgeLab l p := by grind [edgeLab_eq, getElem, Rose.base_le_edg, edgeLab]

/-! ### The label of a simplex -/







end Labels

/-! ### The attaching map -/



end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel Cell

universe u

section Label

variable {α J : Type u} {w : J → List (α × Bool)} {j₀ : J}
  {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι}
  {vlab : κ → Rose α} {elb : ι → Rose α}

/-! ### The position arithmetic -/

theorem fin_succ_val (p : Fin M) : (p + 1).val = (p.val + 1) % M := by grind

/-! ### The circle of the relator -/

variable (w j₀) in
/-- The point of the attaching circle of the relator `j₀` carried by the collar vertex at the
position `p`. -/
def cVtx (p : Fin M) : TCirc w :=
  TCirc.pt w j₀ (p.val / 2) (if p.val % 2 = 0 then CPos.cor else CPos.cmid)

variable (w j₀) in
/-- The point of the attaching circle of the relator `j₀` carried by the collar edge at the
position `p`. -/
def cEdg (p : Fin M) : TCirc w :=
  TCirc.pt w j₀ (p.val / 2) (if p.val % 2 = 0 then CPos.cedgL else CPos.cedgR)

variable (hM : M = 2 * (w j₀).length)

include hM

omit [NeZero M] in
theorem half_lt (p : Fin M) : p.val / 2 < (w j₀).length := by omega

omit [NeZero M] in
theorem aFun_cVtx (p : Fin M) : aFun w (cVtx w j₀ p) = vertLab (w j₀) p.val := by
  obtain ⟨q, hq⟩ := getElem?_half (l := w j₀) (p := p.val) (by have := p.isLt; omega)
  by_cases h : p.val % 2 = 0
  · rw [cVtx, if_pos h, aFun_pt_cor, vertLab_of_even h]
  · rw [cVtx, if_neg h, aFun_pt_cmid_of_get w hq, vertLab_of_odd (by omega) hq]




/-! ### The labels of the boundary -/

omit [NeZero M] in
theorem vertLab_le_edgeLab' (p : Fin M) :
    vertLab (w j₀) p.val ≤ edgeLab (w j₀) p.val :=
  vertLab_le_edgeLab (by have := p.isLt; omega)

theorem vertLab_succ_le_edgeLab' (p : Fin M) :
    vertLab (w j₀) (p + 1).val ≤ edgeLab (w j₀) p.val := by
  have hlt := p.isLt
  have hsucc := fin_succ_val p
  rcases Nat.lt_or_ge (p.val + 1) M with hlt1 | hge
  · have hval : (p + 1).val = p.val + 1 := by rw [hsucc, Nat.mod_eq_of_lt hlt1]
    rw [hval]
    exact vertLab_succ_le_edgeLab (by omega)
  · have hval : (p + 1).val = 0 := by
      rw [hsucc, show p.val + 1 = M by omega, Nat.mod_self]
    rw [hval, vertLab_of_even rfl]
    exact base_le_edgeLab (by omega)

/-! ### The marking -/

variable (w j₀ vc ec vlab elb) in
/-- **The marking of the cells of the surface** by the cells of the model of the presentation
complex. -/
def gLab : Cell κ ι M → PresPos w
  | vtx v => iRose w (vlab v)
  | bed e => iRose w (elb e)
  | cvx p => iCirc w (cVtx w j₀ p)
  | ced p => iCirc w (cEdg w j₀ p)
  | dia p => iRose w (vlab (vc p))
  | gdi p => iRose w (elb (ec p))
  | tr1 p => iRose w (elb (ec p))
  | tr2 p => iRose w (elb (ec p))
  | ctr => apexOf w j₀
  | rad _ => apexOf w j₀
  | inn _ => apexOf w j₀

variable (hvlab : ∀ p : Fin M, vlab (vc p) = vertLab (w j₀) p.val)
  (helb : ∀ p : Fin M, elb (ec p) = edgeLab (w j₀) p.val)

include hvlab helb

/-! ### The marking is monotone -/

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab helb in
theorem iCirc_cVtx_le_apex (p : Fin M) : iCirc w (cVtx w j₀ p) ≤ apexOf w j₀ :=
  iCirc_le_apexOf w _ (half_lt hM p)





omit [DecidableEq κ] [DecidableEq ι] hvlab in
theorem iCirc_cVtx_succ_le_bed (p : Fin M) :
    iCirc w (cVtx w j₀ (p + 1)) ≤ iRose w (elb (ec p)) := by
  refine le_trans (iCirc_le_iRose_aFun w _) ((iRose_monotone w) ?_)
  rw [aFun_cVtx hM (p + 1), helb p]
  exact vertLab_succ_le_edgeLab' hM p

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] in
theorem vlab_le_elb (p : Fin M) : iRose w (vlab (vc p)) ≤ iRose w (elb (ec p)) := by
  refine (iRose_monotone w) ?_
  rw [hvlab p, helb p]
  exact vertLab_le_edgeLab' hM p

omit [DecidableEq κ] [DecidableEq ι] in
theorem vlab_succ_le_elb (p : Fin M) :
    iRose w (vlab (vc (p + 1))) ≤ iRose w (elb (ec p)) := by
  refine (iRose_monotone w) ?_
  rw [hvlab (p + 1), helb p]
  exact vertLab_succ_le_edgeLab' hM p

omit [DecidableEq κ] [DecidableEq ι] in
/-- **The marking is monotone on strict faces.** -/
theorem gLab_le_of_plt {x y : Cell κ ι M} (h : plt vc ec x y) :
    gLab w j₀ vc ec vlab elb x ≤ gLab w j₀ vc ec vlab elb y := by
  cases x with
  | vtx v =>
      cases y with
      | bed e =>
          obtain ⟨i, hi, hv⟩ := h
          rw [← hi]
          rcases hv with rfl | rfl
          · exact vlab_le_elb hM hvlab helb i
          · exact vlab_succ_le_elb hM hvlab helb i
      | dia p =>
          have hv  := h
          show iRose w (vlab v) ≤ iRose w (vlab (vc p))
          rw [hv]
      | gdi p =>
          have hv : vc p = v := h
          show iRose w (vlab v) ≤ iRose w (elb (ec p))
          rw [← hv]
          exact vlab_le_elb hM hvlab helb p
      | tr1 p =>
          show iRose w (vlab v) ≤ iRose w (elb (ec p))
          rcases h with hv | hv
          · rw [← hv]; exact vlab_le_elb hM hvlab helb p
          · rw [← hv]; exact vlab_succ_le_elb hM hvlab helb p
      | tr2 p =>
          have hv : vc p = v := h
          show iRose w (vlab v) ≤ iRose w (elb (ec p))
          rw [← hv]
          exact vlab_le_elb hM hvlab helb p
      | _ => simp [plt] at h
  | cvx q =>
      cases y with
      | ced r =>
          show iCirc w (cVtx w j₀ q) ≤ iCirc w (cEdg w j₀ r)
          rcases h with rfl | rfl
          · exact (iCirc_monotone w) (by
            by_cases h : q.val % 2 = 0
            · rw [cVtx, cEdg, if_pos h, if_pos h]
              exact TCirc.cor_le_cedgL w (half_lt hM q)
            · rw [cVtx, cEdg, if_neg h, if_neg h]
              exact TCirc.cmid_le_cedgR w (half_lt hM q))
          · exact (iCirc_monotone w) (by
            have hlt := r.isLt
            have hsucc := fin_succ_val r
            by_cases h : r.val % 2 = 0
            · -- the next position is the midpoint of the same letter
              have hlt1 : r.val + 1 < M := by omega
              have hval : (r + 1).val = r.val + 1 := by rw [hsucc, Nat.mod_eq_of_lt hlt1]
              have hodd : (r + 1).val % 2 ≠ 0 := by rw [hval]; omega
              have hhalf : (r + 1).val / 2 = r.val / 2 := by rw [hval]; omega
              rw [cVtx, cEdg, if_neg hodd, if_pos h, hhalf]
              exact TCirc.cmid_le_cedgL w (half_lt hM r)
            · -- the next position is the corner in front of the next letter
              rw [cVtx, cEdg, if_neg h]
              rcases Nat.lt_or_ge (r.val + 1) M with hlt1 | hge
              · have hval : (r + 1).val = r.val + 1 := by rw [hsucc, Nat.mod_eq_of_lt hlt1]
                have heven : (r + 1).val % 2 = 0 := by rw [hval]; omega
                have hhalf : (r + 1).val / 2 = r.val / 2 + 1 := by rw [hval]; omega
                have hcs : TCirc.csucc w j₀ (r.val / 2) = r.val / 2 + 1 := by
                  rw [TCirc.csucc, Nat.mod_eq_of_lt (by omega)]
                rw [if_pos heven, hhalf, ← hcs]
                exact TCirc.cor_csucc_le_cedgR w (half_lt hM r)
              · have hval : (r + 1).val = 0 := by
                  rw [hsucc, show r.val + 1 = M by omega, Nat.mod_self]
                have heven : (r + 1).val % 2 = 0 := by rw [hval]
                have hhalf : (r + 1).val / 2 = 0 := by rw [hval]
                have hcs : TCirc.csucc w j₀ (r.val / 2) = 0 := by
                  rw [TCirc.csucc, show r.val / 2 + 1 = (w j₀).length by omega, Nat.mod_self]
                rw [if_pos heven, hhalf, ← hcs]
                exact TCirc.cor_csucc_le_cedgR w (half_lt hM r))
      | dia r =>
          have hq : q = r := h
          show iCirc w (cVtx w j₀ q) ≤ iRose w (vlab (vc r))
          rw [hq]
          exact (by
            rw [hvlab r, ← aFun_cVtx hM r]
            exact iCirc_le_iRose_aFun w _)
      | gdi r =>
          have hq : q = r + 1 := h
          show iCirc w (cVtx w j₀ q) ≤ iRose w (elb (ec r))
          rw [hq]
          exact iCirc_cVtx_succ_le_bed hM helb r
      | rad r =>
          show iCirc w (cVtx w j₀ q) ≤ apexOf w j₀
          exact iCirc_cVtx_le_apex hM q
      | tr1 p =>
          have hq : q = p + 1 := h
          show iCirc w (cVtx w j₀ q) ≤ iRose w (elb (ec p))
          rw [hq]
          exact iCirc_cVtx_succ_le_bed hM helb p
      | tr2 p =>
          show iCirc w (cVtx w j₀ q) ≤ iRose w (elb (ec p))
          rcases h with rfl | rfl
          · exact (by
            refine le_trans (iCirc_le_iRose_aFun w _) ((iRose_monotone w) ?_)
            rw [aFun_cVtx hM q, helb q]
            exact vertLab_le_edgeLab' hM q)
          · exact iCirc_cVtx_succ_le_bed hM helb p
      | inn p =>
          show iCirc w (cVtx w j₀ q) ≤ apexOf w j₀
          exact iCirc_cVtx_le_apex hM q
      | _ => simp [plt] at h
  | ctr =>
      cases y with
      | rad p => exact le_refl _
      | inn p => exact le_refl _
      | _ => simp [plt] at h
  | bed e =>
      cases y with
      | tr1 p =>
          have he : e = ec p := h
          show iRose w (elb e) ≤ iRose w (elb (ec p))
          rw [he]
      | _ => simp [plt] at h
  | ced r =>
      cases y with
      | tr2 p =>
          have hr : r = p := h
          show iCirc w (cEdg w j₀ r) ≤ iRose w (elb (ec p))
          rw [hr]
          exact (by
            rw [helb p, ← (show aFun w (cEdg w j₀ p) = edgeLab (w j₀) p.val by
              obtain ⟨q, hq⟩ := getElem?_half (l := w j₀) (p := p.val) (by have := p.isLt; omega)
              by_cases h : p.val % 2 = 0
              · rw [cEdg, if_pos h, aFun_pt_cedgL_of_get w hq, edgeLab_eq hq, if_pos h]
              · rw [cEdg, if_neg h, aFun_pt_cedgR_of_get w hq, edgeLab_eq hq, if_neg h])]
            exact iCirc_le_iRose_aFun w _)
      | inn p =>
          show iCirc w (cEdg w j₀ r) ≤ apexOf w j₀
          exact (iCirc_le_apexOf w _ (half_lt hM r))
      | _ => simp [plt] at h
  | dia r =>
      cases y with
      | tr1 p =>
          have hr : r = p + 1 := h
          show iRose w (vlab (vc r)) ≤ iRose w (elb (ec p))
          rw [hr]
          exact vlab_succ_le_elb hM hvlab helb p
      | tr2 p =>
          have hr : r = p := h
          show iRose w (vlab (vc r)) ≤ iRose w (elb (ec p))
          rw [hr]
          exact vlab_le_elb hM hvlab helb p
      | _ => simp [plt] at h
  | gdi r =>
      cases y with
      | tr1 p =>
          have hr : r = p := h
          show iRose w (elb (ec r)) ≤ iRose w (elb (ec p))
          rw [hr]
      | tr2 p =>
          have hr : r = p := h
          show iRose w (elb (ec r)) ≤ iRose w (elb (ec p))
          rw [hr]
      | _ => simp [plt] at h
  | rad r =>
      cases y with
      | inn p => exact le_refl _
      | _ => simp [plt] at h
  | tr1 p => simp [plt] at h
  | tr2 p => simp [plt] at h
  | inn p => simp [plt] at h

variable (hc : Compat vc ec)

/-- **The marking as a monotone map of the face poset of the surface.** -/
def gHom : SCell vc ec hc →o PresPos w where
  toFun x := gLab w j₀ vc ec vlab elb x
  monotone' := by
    rintro x y (rfl | h)
    · exact le_refl _
    · exact gLab_le_of_plt hM hvlab helb h

omit [DecidableEq κ] [DecidableEq ι] in
@[simp] theorem gHom_apply (x : Cell κ ι M) :
    gHom hM hvlab helb hc (toS vc ec hc x) = gLab w j₀ vc ec vlab elb x := rfl

/-- **The attaching map of the surface block**: the marking, read on the chains of the
barycentric subdivision. -/
def surfAtt : NeSpx (cmpRel (SCell vc ec hc)) →o PresPos w :=
  nerveAtt (gHom hM hvlab helb hc)

end Label

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb Cell

universe u

section Filling

variable {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

/-! ### The three elementary homotopies -/

/-- **Crossing the boundary edge at `p`** is homotopic to going to the collar vertex at `p+1`
along the diagonal and coming back to the boundary: the homotopy is the triangle `tr1 p`. -/
theorem htpy_bdEdge (p : Fin M) :
    Htpy (sdCx hc) (spx1 (cV hc p)) (spx1 (cV hc (p + 1)))
      (bdEdge hc p) (gg hc p ++ delta hc (p + 1)) := by
  refine htpy_of_loop_nil (isPath_bdEdge hc p)
    ((isPath_gg hc p).append (isPath_delta hc (p + 1))) ?_
  refine htpy_nil_of_star (cT1 hc p) (starCh_spx1 (cV_le_cT1 hc p)) ?_ ?_
  · exact (isPath_bdEdge hc p).append
      (isPath_revPath ((isPath_gg hc p).append (isPath_delta hc (p + 1))))
  · exact pathIn_append' (pathIn_bdEdge_T1 hc p)
      (pathIn_revPath (pathIn_append' (pathIn_gg_T1 hc p) (pathIn_delta1_T1 hc p)))

/-- **The diagonal is homotopic to the path through the collar**: the homotopy is the triangle
`tr2 p`. -/
theorem htpy_gg (p : Fin M) :
    Htpy (sdCx hc) (spx1 (cV hc p)) (spx1 (cW hc (p + 1)))
      (revPath (delta hc p) ++ gam hc p) (gg hc p) := by
  refine htpy_of_loop_nil ((isPath_revPath (isPath_delta hc p)).append (isPath_gam hc p))
    (isPath_gg hc p) ?_
  refine htpy_nil_of_star (cT2 hc p) (starCh_spx1 (cV_le_cT2 hc p)) ?_ ?_
  · exact ((isPath_revPath (isPath_delta hc p)).append (isPath_gam hc p)).append
      (isPath_revPath (isPath_gg hc p))
  · exact pathIn_append'
      (pathIn_append' (pathIn_revPath (pathIn_delta_T2 hc p)) (pathIn_gam_T2 hc p))
      (pathIn_revPath (pathIn_gg_T2 hc p))

/-- **The fan contracts the collar**: the ray to the collar vertex at `p` followed by the collar
edge is homotopic to the ray to the collar vertex at `p+1`; the homotopy is the triangle
`inn p`. -/
theorem htpy_alph (p : Fin M) :
    Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cW hc (p + 1)))
      (alph hc p ++ gam hc p) (alph hc (p + 1)) := by
  refine htpy_of_loop_nil ((isPath_alph hc p).append (isPath_gam hc p))
    (isPath_alph hc (p + 1)) ?_
  refine htpy_nil_of_star (cI hc p) (starCh_spx1 (cC_le_cI hc p)) ?_ ?_
  · exact ((isPath_alph hc p).append (isPath_gam hc p)).append
      (isPath_revPath (isPath_alph hc (p + 1)))
  · exact pathIn_append' (pathIn_append' (pathIn_alph_I hc p) (pathIn_gam_I hc p))
      (pathIn_revPath (pathIn_alph1_I hc p))

/-! ### The rays sweep the polygon -/

/-- **One step of the sweep**: the ray to the boundary vertex at `p`, followed by the boundary
edge at `p`, is homotopic to the ray to the boundary vertex at `p+1`. -/
theorem htpy_ray_step (p : Fin M) :
    Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cV hc (p + 1)))
      (ray hc p ++ bdEdge hc p) (ray hc (p + 1)) := by
  have hA := htpy_bdEdge hc p
  have hB := htpy_gg hc p
  have hC := htpy_alph hc p
  -- the collar edge replaces the diagonal
  have hD : Htpy (sdCx hc) (spx1 (cW hc p)) (spx1 (cW hc (p + 1)))
      (delta hc p ++ gg hc p) (gam hc p) := by
    have h1  :=
      htpy_append_left (isPath_delta hc p) (isPath_gg hc p) hB.symm
    have h3  :=
      htpy_append_right ((isPath_delta hc p).append (isPath_revPath (isPath_delta hc p)))
        (isPath_gam hc p) (htpy_append_revPath (isPath_delta hc p))
    refine h1.trans ?_
    simpa [List.append_assoc] using h3
  have e1 : Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cV hc (p + 1)))
      (ray hc p ++ bdEdge hc p)
      (alph hc p ++ (delta hc p ++ (gg hc p ++ delta hc (p + 1)))) := by
    simpa [ray, List.append_assoc] using
      htpy_append_left (isPath_ray hc p) (isPath_bdEdge hc p) hA
  have e2 : Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cV hc (p + 1)))
      (alph hc p ++ (delta hc p ++ (gg hc p ++ delta hc (p + 1))))
      (alph hc p ++ (gam hc p ++ delta hc (p + 1))) := by
    have inner  :=
      htpy_append_right ((isPath_delta hc p).append (isPath_gg hc p))
        (isPath_delta hc (p + 1)) hD
    simpa [List.append_assoc] using
      htpy_append_left (isPath_alph hc p)
        (((isPath_delta hc p).append (isPath_gg hc p)).append (isPath_delta hc (p + 1))) inner
  have e3 : Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cV hc (p + 1)))
      (alph hc p ++ (gam hc p ++ delta hc (p + 1))) (ray hc (p + 1)) := by
    simpa [ray, List.append_assoc] using
      htpy_append_right ((isPath_alph hc p).append (isPath_gam hc p))
        (isPath_delta hc (p + 1)) hC
  exact e1.trans (e2.trans e3)

/-! ### The boundary loop -/

/-- The position `n` of the boundary, read cyclically. -/
def cyc (M : ℕ) [NeZero M] (n : ℕ) : Fin M := ⟨n % M, Nat.mod_lt _ (NeZero.pos M)⟩

theorem cyc_succ (n : ℕ) : cyc M (n + 1) = cyc M n + 1 := by grind [Nat.add_mod, cyc]

theorem cyc_self : cyc M M = cyc M 0 := by simp_all [cyc]

/-- **The boundary path**: the first `n` edges of the boundary of the polygon. -/
def bdPath : ℕ → List ((sdCx hc).E × Bool)
  | 0 => []
  | n + 1 => bdPath n ++ bdEdge hc (cyc M n)

theorem isPath_bdPath (n : ℕ) :
    IsPath (sdCx hc).src (sdCx hc).tgt (bdPath hc n)
      (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M n))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h := ih.append (isPath_bdEdge hc (cyc M n))
      rw [← cyc_succ] at h
      exact h

/-- **The boundary path is swept by the rays.** -/
theorem htpy_bdPath (n : ℕ) :
    Htpy (sdCx hc) (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M n)))
      (bdPath hc n) (revPath (ray hc (cyc M 0)) ++ ray hc (cyc M n)) := by
  induction n with
  | zero => exact (htpy_revPath_append (isPath_ray hc (cyc M 0))).symm
  | succ n ih =>
      have h1  :=
        htpy_append_right (isPath_bdPath hc n) (isPath_bdEdge hc (cyc M n)) ih
      have h2  :=
        htpy_append_left (isPath_revPath (isPath_ray hc (cyc M 0)))
          ((isPath_ray hc (cyc M n)).append (isPath_bdEdge hc (cyc M n)))
          (htpy_ray_step hc (cyc M n))
      have h3 : Htpy (sdCx hc) (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M n + 1)))
          (bdPath hc (n + 1)) (revPath (ray hc (cyc M 0)) ++ ray hc (cyc M n + 1)) := by
        refine (show Htpy (sdCx hc) (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M n + 1)))
            (bdPath hc (n + 1))
            (revPath (ray hc (cyc M 0)) ++ (ray hc (cyc M n) ++ bdEdge hc (cyc M n)))
          from by simpa [bdPath, List.append_assoc] using h1).trans h2
      rw [cyc_succ]
      exact h3

/-- **The boundary of the polygon bounds**: the loop which goes once around the boundary of the
polygon, based at the vertex of the position `0`, is null-homotopic in the barycentric
subdivision of the triangulation of the surface. -/
theorem htpy_bdLoop_nil :
    Htpy (sdCx hc) (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M 0))) (bdPath hc M) [] := by
  have h := htpy_bdPath hc M
  rw [cyc_self] at h
  exact h.trans (htpy_revPath_append (isPath_ray hc (cyc M 0)))

end Filling

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel Cell

universe u

section Reading

variable {α J : Type u} {w : J → List (α × Bool)} {j₀ : J}
  {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι}
  {vlab : κ → Rose α} {elb : ι → Rose α}
  (hM : M = 2 * (w j₀).length)
  (hvlab : ∀ p : Fin M, vlab (vc p) = vertLab (w j₀) p.val)
  (helb : ∀ p : Fin M, elb (ec p) = edgeLab (w j₀) p.val)
  (hc : Compat vc ec)

/-- The loop of a letter, written out; the universe-polymorphic form of
`FiniteChains.Davis.letterLoop_eq`. -/
theorem letterLoop_eq' (q : α × Bool) :
    letterLoop w q =
      [ordPos ((iRose_monotone w) (Rose.base_le_edg q.1 (!q.2))),
       ordNeg ((iRose_monotone w) (Rose.mid_le_edg q.1 (!q.2))),
       ordPos ((iRose_monotone w) (Rose.mid_le_edg q.1 q.2)),
       ordNeg ((iRose_monotone w) (Rose.base_le_edg q.1 q.2))] := by
  obtain ⟨i, b⟩ := q
  cases b <;> rfl

include hM hvlab helb

/-! ### The values of the attaching map on the boundary -/

theorem att_V (p : Fin M) :
    surfAtt hM hvlab helb hc (spx1 (cV hc p)) = iRose w (vertLab (w j₀) p.val) := by
  rw [surfAtt, nerveAtt_spx1]
  show iRose w (vlab (vc p)) = _
  rw [hvlab p]

theorem att_E (p : Fin M) :
    surfAtt hM hvlab helb hc (spx1 (cE hc p)) = iRose w (edgeLab (w j₀) p.val) := by
  rw [surfAtt, nerveAtt_spx1]
  show iRose w (elb (ec p)) = _
  rw [helb p]

theorem att_VE (p : Fin M) :
    surfAtt hM hvlab helb hc (spx2 (cV_le_cE hc p)) = iRose w (edgeLab (w j₀) p.val) := by
  rw [surfAtt, nerveAtt_spx2]
  show iRose w (elb (ec p)) = _
  rw [helb p]

theorem att_V1E (p : Fin M) :
    surfAtt hM hvlab helb hc (spx2 (cV1_le_cE hc p)) = iRose w (edgeLab (w j₀) p.val) := by
  rw [surfAtt, nerveAtt_spx2]
  show iRose w (elb (ec p)) = _
  rw [helb p]

/-! ### The image of one boundary edge -/

/-- The image of the two-edge crossing of the boundary edge at `p`. -/
theorem mapPath_bdEdge (p : Fin M)
    (h1 : iRose w (vertLab (w j₀) p.val) ≤ iRose w (edgeLab (w j₀) p.val))
    (h0 : iRose w (edgeLab (w j₀) p.val) ≤ iRose w (edgeLab (w j₀) p.val))
    (h2 : iRose w (vertLab (w j₀) (p + 1).val) ≤ iRose w (edgeLab (w j₀) p.val)) :
    mapPath (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
        (bdEdge hc p)
      = [ordPos h1, ordNeg h0, ordPos h0, ordNeg h2] := by
  have e1 := att_V hM hvlab helb hc p
  have e2 := att_VE hM hvlab helb hc p
  have e3 := att_E hM hvlab helb hc p
  have e4 := att_V hM hvlab helb hc (p + 1)
  have e5 := att_V1E hM hvlab helb hc p
  have c1 := ordPos_congr e1 e2
    ((surfAtt hM hvlab helb hc).monotone (spx1_le_spx2_left (cV_le_cE hc p))) h1
  have c2 := ordNeg_congr e3 e2
    ((surfAtt hM hvlab helb hc).monotone (spx1_le_spx2_right (cV_le_cE hc p))) h0
  have c3 := ordPos_congr e3 e5
    ((surfAtt hM hvlab helb hc).monotone (spx1_le_spx2_right (cV1_le_cE hc p))) h0
  have c4 := ordNeg_congr e4 e5
    ((surfAtt hM hvlab helb hc).monotone (spx1_le_spx2_left (cV1_le_cE hc p))) h2
  exact congrArg₂ List.cons c1 (congrArg₂ List.cons c2 (congrArg₂ List.cons c3
    (congrArg₂ List.cons c4 rfl)))

/-- The two backtrackings in the image of a boundary edge cancel. -/
theorem htpy_mapPath_bdEdge (p : Fin M) (rv rv' re : Rose α)
    (hv : vertLab (w j₀) p.val = rv) (hv' : vertLab (w j₀) (p + 1).val = rv')
    (he : edgeLab (w j₀) p.val = re)
    (h1 : iRose w rv ≤ iRose w re) (h2 : iRose w rv' ≤ iRose w re) :
    Htpy (orderCx (PresPos w)) (iRose w rv) (iRose w rv')
      (mapPath (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
        (bdEdge hc p))
      [ordPos h1, ordNeg h2] := by
  subst hv
  subst hv'
  subst he
  rw [mapPath_bdEdge hM hvlab helb hc p h1 (le_refl _) h2]
  have hcancel := htpy_ordNeg_ordPos (le_refl (iRose w (edgeLab (w j₀) p.val)))
  have hh := hcancel.congr_append (r := [ordPos h1]) (s := [ordNeg h2])
    (isPath_ordPos h1) (isPath_ordNeg h2)
  simpa using hh

/-! ### The letter read along the boundary -/

/-- **The boundary of the polygon reads the word**: crossing the two boundary edges of the
letter `k` gives the loop of that letter in the model of the presentation complex. -/
theorem htpy_mapPath_letter (k : ℕ) (hk : k < (w j₀).length) :
    Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w)
      (mapPath (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
        (bdEdge hc (cyc M (2 * k)) ++ bdEdge hc (cyc M (2 * k + 1))))
      (letterLoop w ((w j₀)[k]'hk)) := by
  set q : α × Bool := (w j₀)[k]'hk with hqdef
  have hlen  := hM
  have hq : (w j₀)[k]? = some q := List.getElem?_eq_getElem hk
  -- the two positions of the letter
  have h2k : 2 * k < M := by omega
  have h2k1 : 2 * k + 1 < M := by omega
  have hv0 : (cyc M (2 * k)).val = 2 * k := Nat.mod_eq_of_lt h2k
  have hv1 : (cyc M (2 * k + 1)).val = 2 * k + 1 := Nat.mod_eq_of_lt h2k1
  have hsucc : cyc M (2 * k) + 1 = cyc M (2 * k + 1) := (cyc_succ (2 * k)).symm
  -- the labels
  have hq0 : (w j₀)[(2 * k) / 2]? = some q := by
    rw [show (2 * k) / 2 = k by omega]; exact hq
  have hq1 : (w j₀)[(2 * k + 1) / 2]? = some q := by
    rw [show (2 * k + 1) / 2 = k by omega]; exact hq
  have hvert0 : vertLab (w j₀) (cyc M (2 * k)).val = Rose.base := by
    rw [hv0]; exact vertLab_of_even (by omega)
  have hedge0 : edgeLab (w j₀) (cyc M (2 * k)).val = Rose.edg q.1 (!q.2) := by
    rw [hv0, edgeLab_eq hq0, if_pos (by omega)]
  have hvert1 : vertLab (w j₀) (cyc M (2 * k) + 1).val = Rose.mid q.1 := by
    rw [hsucc, hv1]
    exact vertLab_of_odd (by omega) hq1
  have hvert1' : vertLab (w j₀) (cyc M (2 * k + 1)).val = Rose.mid q.1 := by
    rw [hv1]; exact vertLab_of_odd (by omega) hq1
  have hedge1 : edgeLab (w j₀) (cyc M (2 * k + 1)).val = Rose.edg q.1 q.2 := by
    rw [hv1, edgeLab_eq hq1, if_neg (by omega)]
  have hvert2 : vertLab (w j₀) (cyc M (2 * k + 1) + 1).val = Rose.base := by
    have hval : (cyc M (2 * k + 1) + 1).val = (2 * k + 2) % M := by
      rw [fin_succ_val, hv1]
    rw [hval]
    refine vertLab_of_even ?_
    rcases Nat.lt_or_ge (2 * k + 2) M with hlt | hge
    · simp_all
    · simp_all
  -- the two halves of the letter
  have hA := htpy_mapPath_bdEdge hM hvlab helb hc (cyc M (2 * k)) Rose.base (Rose.mid q.1)
    (Rose.edg q.1 (!q.2)) hvert0 hvert1 hedge0
    ((iRose_monotone w) (Rose.base_le_edg q.1 (!q.2)))
    ((iRose_monotone w) (Rose.mid_le_edg q.1 (!q.2)))
  have hB := htpy_mapPath_bdEdge hM hvlab helb hc (cyc M (2 * k + 1)) (Rose.mid q.1) Rose.base
    (Rose.edg q.1 q.2) hvert1' hvert2 hedge1
    ((iRose_monotone w) (Rose.mid_le_edg q.1 q.2))
    ((iRose_monotone w) (Rose.base_le_edg q.1 q.2))
  have e0 : (surfAtt hM hvlab helb hc) (spx1 (cV hc (cyc M (2 * k)))) = iRose w Rose.base := by
    rw [att_V hM hvlab helb hc, hvert0]
  have e1 : (surfAtt hM hvlab helb hc) (spx1 (cV hc (cyc M (2 * k) + 1)))
      = iRose w (Rose.mid q.1) := by rw [att_V hM hvlab helb hc, hvert1]
  have e1' : (surfAtt hM hvlab helb hc) (spx1 (cV hc (cyc M (2 * k + 1))))
      = iRose w (Rose.mid q.1) := by rw [att_V hM hvlab helb hc, hvert1']
  have e2 : (surfAtt hM hvlab helb hc) (spx1 (cV hc (cyc M (2 * k + 1) + 1)))
      = iRose w Rose.base := by rw [att_V hM hvlab helb hc, hvert2]
  have hpathA : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt
      (mapPath (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
        (bdEdge hc (cyc M (2 * k)))) (iRose w Rose.base) (iRose w (Rose.mid q.1)) := by
    rw [← e0, ← e1]
    exact isPath_mapPath
      (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
      (isPath_bdEdge hc (cyc M (2 * k)))
  have hpathB : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt
      (mapPath (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
        (bdEdge hc (cyc M (2 * k + 1)))) (iRose w (Rose.mid q.1)) (iRose w Rose.base) := by
    rw [← e1', ← e2]
    exact isPath_mapPath
      (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
      (isPath_bdEdge hc (cyc M (2 * k + 1)))
  have hcomb := Htpy.append_congr hpathA hpathB hA hB
  rw [mapPath_append, letterLoop_eq' q]
  simpa [PresModel.ptBase, PresModel.iRose] using hcomb

end Reading

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel Cell

section GenusWord

variable {α : Type} (a b : ℕ → α)

/-- The letter at the position `k` of the surface word. -/
def sLet (k : ℕ) : α × Bool :=
  if k % 4 = 0 then (a (k / 4), true)
  else if k % 4 = 1 then (b (k / 4), true)
  else if k % 4 = 2 then (a (k / 4), false)
  else (b (k / 4), false)

/-- **The surface word of genus `n`**: the product of the commutators
`a_h b_h a_h⁻¹ b_h⁻¹`, written out as a list of letters. -/
def surfWord : ℕ → List (α × Bool)
  | 0 => []
  | n + 1 => surfWord n ++ [(a n, true), (b n, true), (a n, false), (b n, false)]

@[simp] theorem surfWord_length (n : ℕ) : (surfWord a b n).length = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [surfWord, ih]; omega

theorem surfWord_getElem? (n k : ℕ) (hk : k < 4 * n) :
    (surfWord a b n)[k]? = some (sLet a b k) := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge k (4 * n) with hlt | hge
      · have hlen : k < (surfWord a b n).length := by rw [surfWord_length]; exact hlt
        show (surfWord a b n ++ _)[k]? = _
        rw [List.getElem?_append_left hlen]
        exact ih hlt
      · have hlen  := surfWord_length a b n
        show (surfWord a b n ++
          [(a n, true), (b n, true), (a n, false), (b n, false)])[k]? = _
        rw [List.getElem?_append_right (by omega), hlen]
        have hdiv : k / 4 = n := by omega
        have hk4 : k - 4 * n < 4 := by omega
        interval_cases h : (k - 4 * n)
        · have hmod : k % 4 = 0 := by omega
          simp [sLet, hmod, hdiv]
        · have hmod : k % 4 = 1 := by omega
          simp [sLet, hmod, hdiv]
        · have hmod : k % 4 = 2 := by omega
          simp [sLet, hmod, hdiv]
        · have hmod : k % 4 = 3 := by omega
          simp [sLet, hmod, hdiv]

/-! ### The surface word as a product of commutators -/

/-- The two distinguished generators of the block of the genus `h`. -/
def genLw : ℕ × Bool → List (α × Bool) := fun x => if x.2 then [(b x.1, true)] else [(a x.1, true)]

/-- The list of pairs of distinguished generators of the surface block. -/
def genPairs (n : ℕ) : List ((ℕ × Bool) × (ℕ × Bool)) :=
  (List.range n).map (fun h => ((h, false), (h, true)))

theorem commWord_append {ι G : Type} [Group G] (f : ι → G) (l l' : List (ι × ι)) :
    commWord f (l ++ l') = commWord f l * commWord f l' := by
  simp [commWord, List.prod_append]

/-- **The surface word is the product of the commutators of the distinguished generators.** -/
theorem mk_surfWord (n : ℕ) :
    FreeGroup.mk (surfWord a b n)
      = commWord (fun x => FreeGroup.mk (genLw a b x)) (genPairs n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hrange : List.range (n + 1) = List.range n ++ [n] := by
        simp [List.range_succ]
      have hpairs : genPairs (n + 1) = genPairs n ++ [((n, false), (n, true))] := by
        simp [genPairs, hrange]
      show FreeGroup.mk (surfWord a b n ++
        [(a n, true), (b n, true), (a n, false), (b n, false)]) = _
      rw [← FreeGroup.mul_mk, ih, hpairs, commWord_append]
      congr 1

end GenusWord

/-! ### The identification of the boundary of the polygon -/

section GenusData

variable {α : Type} (a b : ℕ → α) (q : ℕ) [NeZero q]

instance neZero_eight_mul : NeZero (8 * q) := ⟨by have := Nat.pos_of_neZero q; omega⟩

/-- The vertices of the surface: the single corner, and the midpoint of each side. -/
abbrev KVtx : Type := Option (Fin q × Bool)

/-- The edges of the surface: for every pair of identified sides, its two halves. -/
abbrev IEdg : Type := Fin q × Bool × Bool

omit [NeZero q] in
theorem genus_hlt (p : Fin (8 * q)) : p.val / 2 / 4 < q := by omega

/-- **The identification of the vertices of the polygon**: all corners become one vertex, the
midpoint of a side is identified with the midpoint of the side paired with it. -/
def gvc (p : Fin (8 * q)) : KVtx q :=
  if p.val % 2 = 0 then none
  else some (⟨p.val / 2 / 4, genus_hlt q p⟩, decide (p.val / 2 % 4 % 2 = 1))

/-- **The identification of the edges of the polygon**: the two sides of a pair are identified
with reversed orientation, so the two halves are exchanged. -/
def gec (p : Fin (8 * q)) : IEdg q :=
  (⟨p.val / 2 / 4, genus_hlt q p⟩, decide (p.val / 2 % 4 % 2 = 1),
    xor (decide (p.val % 2 = 1)) (decide (2 ≤ p.val / 2 % 4)))

/-- The label of a vertex of the surface. -/
def gvlab : KVtx q → Rose α
  | none => Rose.base
  | some (h, i) => Rose.mid (if i then b h.val else a h.val)

/-- The label of an edge of the surface. -/
def gelb : IEdg q → Rose α := fun x => Rose.edg (if x.2.1 then b x.1.val else a x.1.val) x.2.2

omit [NeZero q] in
theorem genus_hM : 8 * q = 2 * (surfWord a b q).length := by
  rw [surfWord_length]; omega

omit [NeZero q] in
/-- **The boundary of the polygon reads the surface word, on the vertices.** -/
theorem genus_hvlab (p : Fin (8 * q)) :
    gvlab a b q (gvc q p) = vertLab (surfWord a b q) p.val := by
  have hlt := p.isLt
  set k := p.val with hk
  by_cases hpar : k % 2 = 0
  · rw [gvc, if_pos hpar]
    rw [vertLab_of_even hpar]
    rfl
  · have hodd : k % 2 = 1 := by omega
    have hs : k / 2 < 4 * q := by omega
    have hget  :=
      surfWord_getElem? a b q (k / 2) hs
    rw [gvc, if_neg hpar, vertLab_of_odd hodd hget]
    have hr : k / 2 % 4 = 0 ∨ k / 2 % 4 = 1 ∨ k / 2 % 4 = 2 ∨ k / 2 % 4 = 3 := by omega
    show Rose.mid (if (decide (k / 2 % 4 % 2 = 1)) then b (k / 2 / 4) else a (k / 2 / 4))
      = Rose.mid (sLet a b (k / 2)).1
    rcases hr with h | h | h | h <;> simp [sLet, h]

omit [NeZero q] in
/-- **The boundary of the polygon reads the surface word, on the edges.** -/
theorem genus_helb (p : Fin (8 * q)) :
    gelb a b q (gec q p) = edgeLab (surfWord a b q) p.val := by
  have hlt := p.isLt
  set k := p.val with hk
  have hs : k / 2 < 4 * q := by omega
  have hget  :=
    surfWord_getElem? a b q (k / 2) hs
  rw [edgeLab_eq hget]
  have hr : k / 2 % 4 = 0 ∨ k / 2 % 4 = 1 ∨ k / 2 % 4 = 2 ∨ k / 2 % 4 = 3 := by omega
  have hpar : k % 2 = 0 ∨ k % 2 = 1 := by omega
  show Rose.edg (if (decide (k / 2 % 4 % 2 = 1)) then b (k / 2 / 4) else a (k / 2 / 4))
      (xor (decide (k % 2 = 1)) (decide (2 ≤ k / 2 % 4)))
    = Rose.edg (sLet a b (k / 2)).1 (if k % 2 = 0 then !(sLet a b (k / 2)).2
        else (sLet a b (k / 2)).2)
  rcases hr with h | h | h | h <;> rcases hpar with h2 | h2 <;>
    simp [sLet, h, h2]

/-- **The identification is consistent**: two positions of the polygon carrying the same edge of
the surface carry the same pair of endpoints. -/
theorem genus_compat : Compat (gvc q) (gec q) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  -- the three components of the equality of the edge labels
  have h1 : i.val / 2 / 4 = j.val / 2 / 4 := congrArg Fin.val (congrArg Prod.fst hij)
  have h2 : (decide (i.val / 2 % 4 % 2 = 1)) = decide (j.val / 2 % 4 % 2 = 1) :=
    congrArg (fun x => x.2.1) hij
  have h3 : xor (decide (i.val % 2 = 1)) (decide (2 ≤ i.val / 2 % 4))
      = xor (decide (j.val % 2 = 1)) (decide (2 ≤ j.val / 2 % 4)) :=
    congrArg (fun x => x.2.2) hij
  have h2' : i.val / 2 % 4 % 2 = j.val / 2 % 4 % 2 := by
    by_cases hA : i.val / 2 % 4 % 2 = 1 <;> by_cases hB : j.val / 2 % 4 % 2 = 1 <;>
      simp [hA, hB] at h2 ⊢ <;> omega
  have hsucci  := fin_succ_val i
  have hsuccj  := fin_succ_val j
  by_cases hsame : i.val / 2 % 4 = j.val / 2 % 4
  · -- the same side of the polygon: the same position
    have hpar : i.val % 2 = j.val % 2 := by
      rw [hsame] at h3
      by_cases hA : i.val % 2 = 1 <;> by_cases hB : j.val % 2 = 1 <;>
        simp [hA, hB] at h3 ⊢
      all_goals omega
    have hij' : i.val = j.val := by omega
    have : i = j := Fin.ext hij'
    subst this
    exact Or.inl ⟨rfl, rfl⟩
  · -- the two paired sides: the positions are mirrored
    have hpar : i.val % 2 ≠ j.val % 2 := by
      intro hp
      rw [hp] at h3
      by_cases hA : 2 ≤ i.val / 2 % 4 <;> by_cases hB : 2 ≤ j.val / 2 % 4 <;>
        simp [hA, hB] at h3 <;> omega
    refine Or.inr ⟨?_, ?_⟩
    · -- `vc i = vc (j+1)`
      rcases Nat.lt_or_ge (i.val % 2) 1 with hI | hI
      · -- `i` is a corner, `j` is a midpoint, so `j+1` is a corner
        have hIe : i.val % 2 = 0 := by omega
        have hJo : j.val % 2 = 1 := by omega
        have hJ1 : (j + 1).val % 2 = 0 := by
          rw [hsuccj]
          rcases Nat.lt_or_ge (j.val + 1) (8 * q) with hlt | hge
          · rw [Nat.mod_eq_of_lt hlt]; omega
          · have : j.val + 1 = 8 * q := by omega
            rw [this, Nat.mod_self]
        rw [gvc, gvc, if_pos hIe, if_pos hJ1]
      · -- `i` is a midpoint, `j` is a corner, so `j+1` is a midpoint of the same pair
        have hIo : i.val % 2 = 1 := by omega
        have hJe : j.val % 2 = 0 := by omega
        have hJlt : j.val + 1 < 8 * q := by omega
        have hJ1v : (j + 1).val = j.val + 1 := by rw [hsuccj, Nat.mod_eq_of_lt hJlt]
        have hJ1o : (j + 1).val % 2 = 1 := by rw [hJ1v]; omega
        have hJ1h : (j + 1).val / 2 = j.val / 2 := by rw [hJ1v]; omega
        rw [gvc, gvc, if_neg (by omega), if_neg (by omega)]
        simp
        omega
    · -- `vc (i+1) = vc j`
      rcases Nat.lt_or_ge (i.val % 2) 1 with hI | hI
      · -- `i+1` is a midpoint of the same pair as `j`
        have hIe : i.val % 2 = 0 := by omega
        have hJo : j.val % 2 = 1 := by omega
        have hIlt : i.val + 1 < 8 * q := by omega
        have hI1v : (i + 1).val = i.val + 1 := by rw [hsucci, Nat.mod_eq_of_lt hIlt]
        have hI1h : (i + 1).val / 2 = i.val / 2 := by rw [hI1v]; omega
        rw [gvc, gvc, if_neg (by omega), if_neg (by omega)]
        simp
        omega
      · -- `i+1` is a corner, and so is `j`
        have hIo : i.val % 2 = 1 := by omega
        have hJe : j.val % 2 = 0 := by omega
        have hI1 : (i + 1).val % 2 = 0 := by
          rw [hsucci]
          rcases Nat.lt_or_ge (i.val + 1) (8 * q) with hlt | hge
          · rw [Nat.mod_eq_of_lt hlt]; omega
          · have : i.val + 1 = 8 * q := by omega
            rw [this, Nat.mod_self]
        rw [gvc, gvc, if_pos hI1, if_pos hJe]

end GenusData

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb Cell

universe u

/-! ### Classes of loops -/

section Pi1Calc

variable {X : Complex2.{u}} {a : X.V}

theorem pi1_mk_append {p q : List (X.E × Bool)} (hp : IsPath X.src X.tgt p a a)
    (hq : IsPath X.src X.tgt q a a) (hpq : IsPath X.src X.tgt (p ++ q) a a) :
    Pi1.mk (⟨p ++ q, hpq⟩ : Loop X a) = Pi1.mk ⟨p, hp⟩ * Pi1.mk ⟨q, hq⟩ := rfl

theorem pi1_mk_rev {p : List (X.E × Bool)} (hp : IsPath X.src X.tgt p a a)
    (hr : IsPath X.src X.tgt (revPath p) a a) :
    Pi1.mk (⟨revPath p, hr⟩ : Loop X a) = (Pi1.mk ⟨p, hp⟩)⁻¹ := rfl

theorem pi1_mk_congr {p p' : List (X.E × Bool)} (hp : IsPath X.src X.tgt p a a)
    (hp' : IsPath X.src X.tgt p' a a) (e : p = p') :
    Pi1.mk (⟨p, hp⟩ : Loop X a) = Pi1.mk ⟨p', hp'⟩ := by simp_all

theorem pi1_mk_eq_one {p : List (X.E × Bool)} (hp : IsPath X.src X.tgt p a a)
    (h : Htpy X a a p []) : Pi1.mk (⟨p, hp⟩ : Loop X a) = 1 :=
  Quotient.sound h

end Pi1Calc

/-- A product of commutators only depends on the values of its function at the elements of the
pairs which occur in the list. -/
theorem commWord_congr_on {ι : Type*} {G : Type*} [Group G] {f g : ι → G}
    {ps : List (ι × ι)} (h : ∀ p ∈ ps, f p.1 = g p.1 ∧ f p.2 = g p.2) :
    commWord f ps = commWord g ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨h1, h2⟩ := h p (List.mem_cons_self ..)
      rw [commWord_cons, commWord_cons, h1, h2, ih (fun r hr => h r (List.mem_cons_of_mem _ hr))]

/-! ### Congruences for the crossings -/



section Rev

variable {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

/-- **A side glued to another one with reversed orientation gives the reversed crossing.** -/
theorem bdEdge_rev {p p' : Fin M} (he : ec p' = ec p) (hv : vc p' = vc (p + 1))
    (hv' : vc (p' + 1) = vc p) : bdEdge hc p' = revPath (bdEdge hc p) := by
  have hE : cE hc p' = cE hc p := congrArg (fun k => toS vc ec hc (bed k)) he
  have hV : cV hc p' = cV hc (p + 1) := congrArg (fun k => toS vc ec hc (vtx k)) hv
  have hV' : cV hc (p' + 1) = cV hc p := congrArg (fun k => toS vc ec hc (vtx k)) hv'
  rw [bdEdge, bdEdge, revPath_append, revPath_edgeHop, revPath_edgeHopRev]
  simp_all

/-! ### The boundary path cut into sides -/

/-- The crossing of the two positions `m` and `m+1`, i.e. of a whole side of the polygon. -/
def pPath (m : ℕ) : List ((sdCx hc).E × Bool) :=
  bdEdge hc (cyc M m) ++ bdEdge hc (cyc M (m + 1))

theorem pPath_eq (m : ℕ) :
    pPath hc m = bdEdge hc (cyc M m) ++ bdEdge hc (cyc M (m + 1)) := rfl

theorem bdPath_succ (m : ℕ) : bdPath hc (m + 1) = bdPath hc m ++ bdEdge hc (cyc M m) := rfl

theorem bdPath_add_two (m : ℕ) : bdPath hc (m + 2) = bdPath hc m ++ pPath hc m := by
  rw [bdPath_succ, bdPath_succ, pPath_eq, List.append_assoc]

end Rev

end Davis
end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel Cell

namespace Genus

variable (q : ℕ) [NeZero q]

/-- The face poset of the closed surface of genus `q`. -/
abbrev gc : Compat (gvc q) (gec q) := genus_compat q

/-- The base vertex: the single corner of the polygon. -/
def gBase : NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))) :=
  spx1 (cV (gc q) (cyc (8 * q) 0))

/-! ### Elementary computations with the identifications -/

theorem cyc_mod_two (k : ℕ) : (cyc (8 * q) k).val % 2 = k % 2 :=
  Nat.mod_mod_of_dvd k ⟨4 * q, by ring⟩

theorem cyc_val_of_lt {k : ℕ} (hk : k < 8 * q) : (cyc (8 * q) k).val = k :=
  Nat.mod_eq_of_lt hk

/-- Every corner of the polygon is the same vertex of the surface. -/
theorem gvc_even {k : ℕ} (hk : k % 2 = 0) : gvc q (cyc (8 * q) k) = none := by simp_all [cyc_mod_two, hk, gvc, if_pos]

theorem gvc_congr_lt {k k' : ℕ} (hk : k < 8 * q) (hk' : k' < 8 * q) (ho : k % 2 = 1)
    (ho' : k' % 2 = 1) (h1 : k / 2 / 4 = k' / 2 / 4)
    (h2 : (k / 2 % 4 % 2 = 1) ↔ (k' / 2 % 4 % 2 = 1)) :
    gvc q (cyc (8 * q) k) = gvc q (cyc (8 * q) k') := by simp_all [gvc, if_neg, cyc_val_of_lt]

theorem gec_congr_lt {k k' : ℕ} (hk : k < 8 * q) (hk' : k' < 8 * q)
    (h1 : k / 2 / 4 = k' / 2 / 4)
    (h2 : (k / 2 % 4 % 2 = 1) ↔ (k' / 2 % 4 % 2 = 1))
    (h3 : xor (decide (k % 2 = 1)) (decide (2 ≤ k / 2 % 4))
      = xor (decide (k' % 2 = 1)) (decide (2 ≤ k' / 2 % 4))) :
    gec q (cyc (8 * q) k) = gec q (cyc (8 * q) k') := by simp_all [gec, cyc_val_of_lt]

/-- All the corners of the polygon are one and the same cell. -/
theorem cV_even {k : ℕ} (hk : k % 2 = 0) :
    cV (gc q) (cyc (8 * q) k) = cV (gc q) (cyc (8 * q) 0) :=
  congrArg (fun x => toS (gvc q) (gec q) (gc q) (vtx x))
    ((gvc_even q hk).trans (gvc_even q (k := 0) rfl).symm)

/-! ### The sides of the polygon, and the pairing -/

/-- The side of the polygon starting at the position `m`. -/
abbrev gPath (m : ℕ) : List ((sdCx (gc q)).E × Bool) := pPath (gc q) m

theorem isPath_gPath {m : ℕ} (hm : m % 2 = 0) :
    IsPath (sdCx (gc q)).src (sdCx (gc q)).tgt (gPath q m) (gBase q) (gBase q) := by
  have h1 := isPath_bdEdge (gc q) (cyc (8 * q) m)
  rw [← cyc_succ] at h1
  have h2 := isPath_bdEdge (gc q) (cyc (8 * q) (m + 1))
  rw [← cyc_succ] at h2
  have h3 := h1.append h2
  rw [cV_even q hm, cV_even q (k := m + 1 + 1) (by omega)] at h3
  exact h3

theorem isPath_bdPath8 (n : ℕ) :
    IsPath (sdCx (gc q)).src (sdCx (gc q)).tgt (bdPath (gc q) (8 * n)) (gBase q) (gBase q) := by
  have h := isPath_bdPath (gc q) (8 * n)
  rw [cV_even q (k := 8 * n) (by omega)] at h
  exact h

/-- The two sides of a pair are inverse edge paths: the first half. -/
theorem bdEdge_rev_a {h : ℕ} (hh : h < q) :
    bdEdge (gc q) (cyc (8 * q) (8 * h + 4))
      = revPath (bdEdge (gc q) (cyc (8 * q) (8 * h + 1))) := by
  refine bdEdge_rev (gc q) ?_ ?_ ?_
  · refine gec_congr_lt q (by omega) (by omega) (by omega) (by omega) ?_
    have e1 : (8 * h + 4) % 2 = 0 := by omega
    have e2 : (8 * h + 4) / 2 % 4 = 2 := by omega
    have e3 : (8 * h + 1) % 2 = 1 := by omega
    have e4 : (8 * h + 1) / 2 % 4 = 0 := by omega
    rw [e1, e2, e3, e4]
    decide
  · rw [← cyc_succ]
    exact (gvc_even q (by omega)).trans (gvc_even q (by omega)).symm
  · rw [← cyc_succ]
    exact gvc_congr_lt q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The two sides of a pair are inverse edge paths: the second half. -/
theorem bdEdge_rev_b {h : ℕ} (hh : h < q) :
    bdEdge (gc q) (cyc (8 * q) (8 * h + 5))
      = revPath (bdEdge (gc q) (cyc (8 * q) (8 * h))) := by
  refine bdEdge_rev (gc q) ?_ ?_ ?_
  · refine gec_congr_lt q (by omega) (by omega) (by omega) (by omega) ?_
    have e1 : (8 * h + 5) % 2 = 1 := by omega
    have e2 : (8 * h + 5) / 2 % 4 = 2 := by omega
    have e3 : (8 * h) % 2 = 0 := by omega
    have e4 : (8 * h) / 2 % 4 = 0 := by omega
    rw [e1, e2, e3, e4]
    decide
  · rw [← cyc_succ]
    exact gvc_congr_lt q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [← cyc_succ]
    exact (gvc_even q (by omega)).trans (gvc_even q (by omega)).symm

/-- The two sides of the second pair are inverse edge paths: the first half. -/
theorem bdEdge_rev_c {h : ℕ} (hh : h < q) :
    bdEdge (gc q) (cyc (8 * q) (8 * h + 6))
      = revPath (bdEdge (gc q) (cyc (8 * q) (8 * h + 3))) := by
  refine bdEdge_rev (gc q) ?_ ?_ ?_
  · refine gec_congr_lt q (by omega) (by omega) (by omega) (by omega) ?_
    have e1 : (8 * h + 6) % 2 = 0 := by omega
    have e2 : (8 * h + 6) / 2 % 4 = 3 := by omega
    have e3 : (8 * h + 3) % 2 = 1 := by omega
    have e4 : (8 * h + 3) / 2 % 4 = 1 := by omega
    rw [e1, e2, e3, e4]
    decide
  · rw [← cyc_succ]
    exact (gvc_even q (by omega)).trans
      (gvc_even q (by omega)).symm
  · rw [← cyc_succ]
    exact gvc_congr_lt q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The two sides of the second pair are inverse edge paths: the second half. -/
theorem bdEdge_rev_d {h : ℕ} (hh : h < q) :
    bdEdge (gc q) (cyc (8 * q) (8 * h + 7))
      = revPath (bdEdge (gc q) (cyc (8 * q) (8 * h + 2))) := by
  refine bdEdge_rev (gc q) ?_ ?_ ?_
  · refine gec_congr_lt q (by omega) (by omega) (by omega) (by omega) ?_
    have e1 : (8 * h + 7) % 2 = 1 := by omega
    have e2 : (8 * h + 7) / 2 % 4 = 3 := by omega
    have e3 : (8 * h + 2) % 2 = 0 := by omega
    have e4 : (8 * h + 2) / 2 % 4 = 1 := by omega
    rw [e1, e2, e3, e4]
    decide
  · rw [← cyc_succ]
    exact gvc_congr_lt q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [← cyc_succ]
    exact (gvc_even q (by omega)).trans
      (gvc_even q (by omega)).symm

/-- **The side `4h+2` of the polygon is the side `4h` reversed.** -/
theorem gPath_rev_a {h : ℕ} (hh : h < q) :
    gPath q (8 * h + 4) = revPath (gPath q (8 * h)) := by simp_all [pPath_eq, revPath_append, bdEdge_rev_a, bdEdge_rev_b, gPath]

/-- **The side `4h+3` of the polygon is the side `4h+1` reversed.** -/
theorem gPath_rev_b {h : ℕ} (hh : h < q) :
    gPath q (8 * h + 6) = revPath (gPath q (8 * h + 2)) := by simp_all [pPath_eq, revPath_append, bdEdge_rev_c, bdEdge_rev_d, gPath]

/-! ### The classes of the sides in the fundamental group -/

/-- The class of the side of the polygon starting at an even position. -/
def gcl {m : ℕ} (hm : m % 2 = 0) : Pi1 (sdCx (gc q)) (gBase q) :=
  Pi1.mk ⟨gPath q m, isPath_gPath q hm⟩

/-- The class of the first `8n` sides of the polygon. -/
def bcl (n : ℕ) : Pi1 (sdCx (gc q)) (gBase q) :=
  Pi1.mk ⟨bdPath (gc q) (8 * n), isPath_bdPath8 q n⟩

theorem gcl_congr {m m' : ℕ} (hm : m % 2 = 0) (hm' : m' % 2 = 0) (e : m = m') :
    gcl q hm = gcl q hm' := by simp_all

theorem gcl_inv {m m' : ℕ} (hm : m % 2 = 0) (hm' : m' % 2 = 0)
    (e : gPath q m' = revPath (gPath q m)) : gcl q hm' = (gcl q hm)⁻¹ := by
  rw [gcl, gcl]
  exact (pi1_mk_congr _ (e ▸ isPath_gPath q hm') e).trans
    (pi1_mk_rev (isPath_gPath q hm) _)

/-- The generators of the block: the side `4h` (for `i = false`) and the side `4h+1`
(for `i = true`) of the polygon. -/
theorem gIdx_even (x : ℕ × Bool) : (8 * x.1 + (if x.2 then 2 else 0)) % 2 = 0 := by grind

def gGen (x : ℕ × Bool) : Pi1 (sdCx (gc q)) (gBase q) :=
  gcl q (m := 8 * x.1 + (if x.2 then 2 else 0)) (gIdx_even x)

/-- The sides of the block of the genus `h`, concatenated. -/
abbrev gBlock (n : ℕ) : List ((sdCx (gc q)).E × Bool) :=
  ((gPath q (8 * n) ++ gPath q (8 * n + 2)) ++ gPath q (8 * n + 4)) ++ gPath q (8 * n + 6)

theorem bdPath_block (n : ℕ) :
    bdPath (gc q) (8 * (n + 1)) = bdPath (gc q) (8 * n) ++ gBlock q n := by
  have e8 : 8 * (n + 1) = 8 * n + 2 + 2 + 2 + 2 := by ring
  rw [e8, bdPath_add_two, bdPath_add_two, bdPath_add_two, bdPath_add_two]
  simp


/-- **The class of the first `n` blocks of the boundary is the product of the first `n`
commutators.** -/
theorem bcl_eq_commWord {n : ℕ} (hn : n ≤ q) :
    bcl q n = commWord (gGen q) (genPairs n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hlt : n < q := by omega
      have hpairs : genPairs (n + 1) = genPairs n ++ [((n, false), (n, true))] := by
        simp [genPairs, List.range_succ]
      rw [(show bcl q (n + 1) = bcl q n * (gGen q (n, false) * gGen q (n, true)
      * (gGen q (n, false))⁻¹ * (gGen q (n, true))⁻¹) by
        have h0 : (8 * n) % 2 = 0 := by omega
        have h2 : (8 * n + 2) % 2 = 0 := by omega
        have h4 : (8 * n + 4) % 2 = 0 := by omega
        have h6 : (8 * n + 6) % 2 = 0 := by omega
        -- the four sides of the block
        have e4  := gcl_inv q h0 h4 (gPath_rev_a q hlt)
        have e6  := gcl_inv q h2 h6 (gPath_rev_b q hlt)
        have eF : gGen q (n, false) = gcl q h0 := gcl_congr q _ _ (by norm_num)
        have eT : gGen q (n, true) = gcl q h2 := gcl_congr q _ _ (by norm_num)
        -- the class of the block is the commutator
        have hblock : Pi1.mk ⟨gBlock q n, ((((isPath_gPath q h0).append (isPath_gPath q h2)).append
              (isPath_gPath q h4)).append (isPath_gPath q h6))⟩
            = gcl q h0 * gcl q h2 * gcl q h4 * gcl q h6 := by
          rw [gcl, gcl, gcl, gcl]
          rw [pi1_mk_append (((isPath_gPath q h0).append (isPath_gPath q h2)).append
            (isPath_gPath q h4)) (isPath_gPath q h6)]
          rw [pi1_mk_append ((isPath_gPath q h0).append (isPath_gPath q h2)) (isPath_gPath q h4)]
          rw [pi1_mk_append (isPath_gPath q h0) (isPath_gPath q h2)]
        rw [bcl, bcl]
        rw [pi1_mk_congr (isPath_bdPath8 q (n + 1))
          (((isPath_bdPath8 q n).append ((((isPath_gPath q h0).append (isPath_gPath q h2)).append
            (isPath_gPath q h4)).append (isPath_gPath q h6)))) (bdPath_block q n)]
        rw [pi1_mk_append (isPath_bdPath8 q n) ((((isPath_gPath q h0).append (isPath_gPath q h2)).append
            (isPath_gPath q h4)).append (isPath_gPath q h6)), hblock, eF, eT, e4, e6]), ih (by omega), hpairs, commWord_append, commWord_cons, commWord_nil,
        mul_one]

/-! ### The filling -/

/-- **The loop of the distinguished generator `(h, i)` of the block**: the side `4h + i` of the
polygon, traversed once. -/
def gSig (x : ℕ × Bool) : List ((sdCx (gc q)).E × Bool) :=
  gPath q (8 * (x.1 % q) + (if x.2 then 2 else 0))

theorem gSig_eq (x : ℕ × Bool) :
    gSig q x = gPath q (8 * (x.1 % q) + (if x.2 then 2 else 0)) := rfl


theorem isPath_gSig (x : ℕ × Bool) :
    IsPath (sdCx (gc q)).src (sdCx (gc q)).tgt (gSig q x) (gBase q) (gBase q) :=
  isPath_gPath q (gIdx_even (x.1 % q, x.2))

theorem cls_gSig {x : ℕ × Bool} (hx : x.1 < q) :
    Pi1.mk (⟨gSig q x, isPath_gSig q x⟩ : Loop (sdCx (gc q)) (gBase q)) = gGen q x :=
  pi1_mk_congr _ _ (by rw [gSig_eq, Nat.mod_eq_of_lt hx])

/-- **The surface relator is filled**: the product of the commutators of the classes of the
loops of the distinguished generators is trivial in the fundamental group of the surface of
genus `q`. -/
theorem genus_hfilling :
    commWord (fun x => Pi1.mk (⟨gSig q x, isPath_gSig q x⟩ : Loop (sdCx (gc q)) (gBase q)))
      (genPairs q) = 1 := by
  have hstep : ∀ p ∈ genPairs q,
      Pi1.mk ⟨gSig q p.1, isPath_gSig q p.1⟩ = gGen q p.1 ∧
      Pi1.mk ⟨gSig q p.2, isPath_gSig q p.2⟩ = gGen q p.2 := by
    intro p hp
    simp only [genPairs, List.mem_map, List.mem_range] at hp
    obtain ⟨h, hh, rfl⟩ := hp
    have hmod  := Nat.mod_eq_of_lt hh
    exact ⟨cls_gSig q (by exact hh), cls_gSig q (by exact hh)⟩
  rw [commWord_congr_on hstep, ← bcl_eq_commWord q (le_refl q), bcl]
  exact pi1_mk_eq_one _ (htpy_bdLoop_nil (gc q))

end Genus

end Davis
end FiniteChains
end
