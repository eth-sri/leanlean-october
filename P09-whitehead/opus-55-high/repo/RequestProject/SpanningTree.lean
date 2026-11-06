import RequestProject.CombPi1


/-!
# Spanning trees of combinatorial two-complexes

Theorem A is stated for arbitrary connected two-complexes, whereas the whole algebraic part
of the project works with *presentation* complexes (one vertex).  The bridge between the two
is the classical collapse of a spanning tree.  This file provides the first half of that
bridge: spanning trees themselves.

* `FiniteChains.Comb.SpanningTree K` — a spanning tree of the one-skeleton of `K`, described
  by the data that is actually used later: a root, a height function, and for every vertex
  other than the root a distinguished oriented *tree edge* going one step closer to the root;
  the tree edges are exactly the distinguished ones;
* `FiniteChains.Comb.SpanningTree.treePath` — the tree path from the root to a vertex, defined
  by recursion on the height, together with `treePath_isPath` (it is an edge path from the root
  to the vertex) and `isTree_of_mem_treePath` (it only uses tree edges);
* `FiniteChains.Comb.SpanningTree.exists_of_isConnected` — **every connected two-complex has a
  spanning tree**: take for the height the distance from the root and for the tree edge at a
  vertex the last edge of a shortest path.  No finiteness whatsoever is needed.
-/

namespace FiniteChains.Comb

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
  up_src : ∀ (a : K.V) (ha : a ≠ root), gSrcX K (up a ha) = a
  /-- `up a` ends one step closer to the root. -/
  up_ht : ∀ (a : K.V) (ha : a ≠ root), ht (gTgtX K (up a ha)) + 1 = ht a
  /-- The tree edges are exactly the edges `up a`, `a ≠ root`. -/
  isTree_iff : ∀ e, isTree e ↔ ∃ (a : K.V) (ha : a ≠ root), (up a ha).1 = e

namespace SpanningTree

variable (T : SpanningTree K)

/-- The parent of a non-root vertex: the other endpoint of its tree edge. -/
def parent a (ha : a ≠ T.root) := gTgtX K (T.up a ha)

theorem ht_parent ha : T.ht (T.parent a ha) + 1 = T.ht a :=
  T.up_ht a ha

theorem isTree_up ha : T.isTree (T.up a ha).1 :=
  (T.isTree_iff _).2 (by grind)

open Classical in
/-- The tree path from the root to a vertex. -/
noncomputable def treePath (T : SpanningTree K) (a : K.V) : List (K.E × Bool) :=
  if h : a = T.root then [] else
    treePath T (T.parent a h) ++ [revGerm (T.up a h)]
  termination_by T.ht a
  decreasing_by
    have h' := T.ht_parent h
    omega

@[simp] theorem treePath_root : T.treePath T.root = [] := by
  rw [treePath]
  simp

theorem treePath_of_ne ha :
    T.treePath a = T.treePath (T.parent a ha) ++ [revGerm (T.up a ha)] := by
  rw [treePath]
  simp_all

/-- The tree path from the root to `a` is an edge path from the root to `a`. -/
theorem treePath_isPath a : IsPathX K (T.treePath a) T.root a := by
  induction hn : T.ht a using Nat.strong_induction_on generalizing a with
  | _ n ih =>
      by_cases ha : a = T.root
      · subst ha
        simp
      · have hp := T.ht_parent ha
        have hlt : T.ht (T.parent a ha) < n := by omega
        have hrest := ih _ hlt _ rfl
        rw [T.treePath_of_ne ha]
        refine isPath_append_iff.mpr ⟨T.parent a ha, hrest, ?_⟩
        have h1 : gSrcX K (revGerm (T.up a ha)) = T.parent a ha := by
          aesop
        have h2 : gTgtX K (revGerm (T.up a ha)) = a := by
          simpa using T.up_src a ha
        simp_all

/-- Every edge of a tree path is a tree edge. -/
theorem isTree_of_mem_treePath a {g} (hg : g ∈ T.treePath a) :
    T.isTree g.1 := by
  induction hn : T.ht a using Nat.strong_induction_on generalizing a g with
  | _ n ih =>
      by_cases ha : a = T.root
      · simp_all
      · have hp := T.ht_parent ha
        have hlt : T.ht (T.parent a ha) < n := by omega
        rw [T.treePath_of_ne ha, List.mem_append] at hg
        rcases hg with hg | hg
        · tauto
        · simp [List.mem_singleton] at hg
          subst hg
          exact T.isTree_up ha

/-! ### Existence -/

section Existence

/-- The lengths of edge paths from a fixed vertex. -/
def reach (K : Complex2.{u}) (r a : K.V) := {n | ∃ p : List (K.E × Bool),
  p.length = n ∧ IsPathX K p r a}

theorem reach_nonempty (hconn : IsConnected K) r a :
    (reach K r a).Nonempty := by
  cases' hconn r a with p hp
  exact ⟨p.length, p, rfl, hp⟩

/-- **Every connected two-complex has a spanning tree**, rooted at any prescribed vertex. -/
theorem exists_of_isConnected (hconn : IsConnected K) r :
    ∃ T : SpanningTree K, T.root = r := by
  classical
  set d : K.V → ℕ := fun a => sInf (reach K r a) with hd
  have hmem : ∀ a, d a ∈ reach K r a := fun a =>
    Nat.sInf_mem (reach_nonempty hconn r a)
  have hle : ∀ a p, IsPathX K p r a → d a ≤ p.length :=
    fun a p hp => Nat.sInf_le (by tauto)
  have hd_root : d r = 0 := Nat.le_antisymm (hle r [] rfl) (Nat.zero_le _)
  have hd_eq_zero : ∀ a, d a = 0 → a = r := by
    intro a ha
    obtain ⟨p, hlen, hp⟩ := hmem a
    rw [ha, List.length_eq_zero_iff] at hlen
    simp_all
  have hstep : ∀ a, a ≠ r → ∃ g : K.E × Bool,
      gSrcX K g = a ∧ d (gTgtX K g) + 1 = d a := by
    intro a ha
    obtain ⟨p, hlen, hp⟩ := hmem a
    have hne : p ≠ [] := by
      grind
    obtain ⟨q, g, rfl⟩ : ∃ (q : List (K.E × Bool)) (g : K.E × Bool), p = q ++ [g] :=
      ⟨p.dropLast, p.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    obtain ⟨m, hq, hg⟩ := isPath_append_iff.1 hp
    have hgs : gSrcX K g = m := hg.1.symm
    have hgt : gTgtX K g = a := by
      simp_all
    refine ⟨revGerm g, by simpa using hgt, ?_⟩
    have h2 : d a ≤ d m + 1 := by
      obtain ⟨q', hlen', hq'⟩ := hmem m
      have hpath : IsPathX K (q' ++ [g]) r a :=
        isPath_append_iff.mpr (by simp_all)
      grind
    have hmt : gTgtX K (revGerm g) = m := by simpa using hgs
    grind
  choose upg hupsrc hupht using hstep
  exact ⟨{ root := r
           ht := d
           isTree := fun e => ∃ (a : K.V) (ha : a ≠ r), (upg a ha).1 = e
           up := upg
           ht_root := hd_root
           ht_eq_zero := hd_eq_zero
           up_src := hupsrc
           up_ht := hupht
           isTree_iff := fun _ => Iff.rfl }, rfl⟩
