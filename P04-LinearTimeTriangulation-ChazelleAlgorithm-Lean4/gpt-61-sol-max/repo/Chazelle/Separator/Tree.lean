module

public meta import Chazelle.Arithmetic

public import Chazelle.Separator.Maps
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Rooted spanning trees of a combinatorial map (planar separators, part 3a)

A `SpanTree M` is a rooted spanning tree of the map `M` given by parent darts and levels: every
non-root vertex `v` has a dart `par v` at `v` whose head is one level closer to the root.  The
tree darts are the darts `par v` and `opp (par v)`.

* `parent`, `IsAnc` (reflexive ancestor relation, `IsAnc v u`: `v` lies on the root path of `u`),
  `level_iterate_parent` (levels drop by one along the root path), `isAnc_root`;
* `eq_of_isAnc_of_level_eq`: a root path has at most one vertex on each level;
* `treeDarts`, `card_treeDarts : |treeDarts| = 2 (V - 1)`;
* `exists_bfsTree`: every connected map has a BFS tree from any root whose levels are the graph
  distances from the root, so every dart joins levels differing by at most one
  (`dist_head_le`); `reachable_of_connected`: the underlying graph of a connected map is
  connected.
-/

namespace Chazelle.Separator

@[expose] public section

open Equiv Finset

namespace CombMap

variable {V F D : Type*}

/-- A rooted spanning tree of a map, given by parent darts and levels. -/
structure SpanTree (M : CombMap V F D) where
  /-- the root -/
  root : V
  /-- the depth of a vertex -/
  level : V → ℕ
  /-- the dart from a non-root vertex to its parent -/
  par : V → D
  level_root : level root = 0
  vert_par : ∀ v, v ≠ root → M.vert (par v) = v
  level_head_par : ∀ v, v ≠ root → level (M.head (par v)) + 1 = level v

namespace SpanTree

variable {M : CombMap V F D} (T : SpanTree M)

section Basic

variable [DecidableEq V]

/-- The parent of a vertex (the root is its own parent). -/
def parent (v : V) : V := if v = T.root then T.root else M.head (T.par v)

/-- `IsAnc v u`: `v` lies on the tree path from `u` to the root (reflexive). -/
def IsAnc (v u : V) : Prop := ∃ n : ℕ, T.parent^[n] u = v

/-- The root is its own parent. -/
theorem parent_root : T.parent T.root = T.root := by simp [parent]

/-- The parent of a non-root vertex is the head of its parent dart. -/
theorem parent_of_ne {v : V} (hv : v ≠ T.root) : T.parent v = M.head (T.par v) := by
  grind [parent]

omit [DecidableEq V] in
/-- Non-root vertices have positive level. -/
theorem level_pos {v : V} (hv : v ≠ T.root) : 0 < T.level v := by
  have := T.level_head_par v hv; omega

/-- The root is the only vertex of level `0`. -/
theorem eq_root_of_level_eq_zero {v : V} (hv : T.level v = 0) : v = T.root := by
  by_contra h; have := T.level_pos h; omega

/-- The parent is one level up. -/
theorem level_parent (v : V) : T.level (T.parent v) = T.level v - 1 := by
  by_cases hv : v = T.root
  · subst hv; simp [parent_root, T.level_root]
  · rw [T.parent_of_ne hv]; have := T.level_head_par v hv; omega

/-- The `n`-th ancestor is `n` levels up (truncated). -/
theorem level_iterate_parent (n : ℕ) (u : V) :
    T.level (T.parent^[n] u) = T.level u - n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', T.level_parent, ih]; omega

/-- Enough steps up reach the root. -/
theorem iterate_parent_eq_root {n : ℕ} {u : V} (hn : T.level u ≤ n) :
    T.parent^[n] u = T.root :=
  T.eq_root_of_level_eq_zero (by rw [T.level_iterate_parent]; omega)

/-- Every vertex is its own ancestor. -/
theorem isAnc_refl (u : V) : T.IsAnc u u := ⟨0, rfl⟩

/-- The parent is an ancestor. -/
theorem isAnc_parent_self (u : V) : T.IsAnc (T.parent u) u := ⟨1, rfl⟩

/-- The ancestor relation is transitive. -/
theorem IsAnc.trans {w v u : V} (h1 : T.IsAnc w v) (h2 : T.IsAnc v u) : T.IsAnc w u := by
  obtain ⟨m, rfl⟩ := h1
  obtain ⟨n, rfl⟩ := h2
  exact ⟨m + n, by rw [Function.iterate_add_apply]⟩

section
variable {v u : V}
/-- Ancestors have smaller levels. -/
theorem IsAnc.level_le (h : T.IsAnc v u) : T.level v ≤ T.level u := by
  obtain ⟨n, rfl⟩ := h
  rw [T.level_iterate_parent]; omega

/-- An ancestor of the parent is an ancestor. -/
theorem IsAnc.of_parent (h : T.IsAnc v (T.parent u)) : T.IsAnc v u :=
  h.trans T (T.isAnc_parent_self u)

/-- If `v` is an ancestor of `u` but not of its parent, then `u = v`. -/
theorem eq_of_isAnc_of_not_parent (h : T.IsAnc v u) (hp : ¬ T.IsAnc v (T.parent u)) :
    u = v := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | n
  · exact hn
  · exact absurd ⟨n, by simp_all⟩ hp


end

/-- A non-root vertex is not an ancestor of its parent. -/
theorem not_isAnc_parent {v : V} (hv : v ≠ T.root) : ¬ T.IsAnc v (T.parent v) := by
  intro h
  have h1 := h.level_le
  rw [T.level_parent] at h1
  have := T.level_pos hv
  omega

/-- A root path has at most one vertex on each level. -/
theorem eq_of_isAnc_of_level_eq {v v' u : V} (h : T.IsAnc v u) (h' : T.IsAnc v' u)
    (hl : T.level v = T.level v') : v = v' := by
  obtain ⟨n, rfl⟩ := h
  obtain ⟨n', rfl⟩ := h'
  grind [Chazelle.Separator.CombMap.SpanTree.level_iterate_parent, Chazelle.Separator.CombMap.SpanTree.iterate_parent_eq_root]

end Basic

/-! ### Tree darts -/

section TreeDarts

/-- A tree dart: `par v` or its opposite, for a non-root vertex `v`. -/
def IsTreeDart (d : D) : Prop := ∃ v, v ≠ T.root ∧ (d = T.par v ∨ d = M.opp (T.par v))

section
variable {v w : V} (hv : v ≠ T.root) (hw : w ≠ T.root)
include hv hw
/-- A parent dart is never the opposite of a parent dart. -/
theorem par_ne_opp_par :
    T.par v ≠ M.opp (T.par w) := by
  intro h
  have h1 : T.level (M.head (T.par w)) + 1 = T.level w := T.level_head_par w hw
  have h2 : T.level (M.head (T.par v)) + 1 = T.level v := T.level_head_par v hv
  have e1 : M.head (T.par w) = v := by
    rw [← T.vert_par v hv, h]; rfl
  have e2 : M.head (T.par v) = w := by
    rw [← T.vert_par w hw, h, head, M.opp_opp]
  grind

/-- Parent darts of distinct vertices are distinct. -/
theorem par_injective (h : T.par v = T.par w) :
    v = w := by
  rw [← T.vert_par v hv, ← T.vert_par w hw, h]


end

variable [Fintype V] [DecidableEq V] [DecidableEq D]

/-- The finite set of tree darts. -/
def treeDarts : Finset D :=
  ((Finset.univ.filter (· ≠ T.root)).image T.par) ∪
    ((Finset.univ.filter (· ≠ T.root)).image (fun v => M.opp (T.par v)))

/-- Membership in the tree darts. -/
theorem mem_treeDarts {d : D} : d ∈ T.treeDarts ↔ T.IsTreeDart d := by
  simp only [treeDarts, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, IsTreeDart]
  ram_grind

/-- The tree darts form an edge set. -/
theorem opp_mem_treeDarts {d : D} (hd : d ∈ T.treeDarts) : M.opp d ∈ T.treeDarts := by
  rw [mem_treeDarts] at hd ⊢
  obtain ⟨v, hv, rfl | rfl⟩ := hd
  · grind [Chazelle.Separator.CombMap.SpanTree.IsTreeDart]
  · exact ⟨v, hv, Or.inl (M.opp_opp _)⟩

/-- A spanning tree has `V - 1` edges: `|treeDarts| = 2 (V - 1)`. -/
theorem card_treeDarts : T.treeDarts.card = 2 * (Fintype.card V - 1) := by
  unfold treeDarts
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injOn, Finset.card_image_of_injOn]
    · have : (Finset.univ.filter (· ≠ T.root)).card = Fintype.card V - 1 := by
        rw [Finset.filter_ne' Finset.univ T.root, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ]
      omega
    · intro v hv w hw h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
      exact T.par_injective hv hw (M.opp_injective h)
    · intro v hv w hw h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
      exact T.par_injective hv hw h
  · rw [Finset.disjoint_left]
    grind [Chazelle.Separator.CombMap.SpanTree.par_ne_opp_par]

end TreeDarts

end SpanTree

/-! ### Breadth-first trees -/

section BFS

variable (M : CombMap V F D)

/-- A connected map has a connected underlying graph: every vertex is reachable from `r`. -/
theorem reachable_of_connected (hM : M.Connected) (r u : V) : M.graph.Reachable r u := by
  obtain ⟨d0, hd0⟩ := M.vert_surj r
  obtain ⟨d, rfl⟩ := M.vert_surj u
  refine hM {x | M.graph.Reachable r (M.vert x)} ?_ ?_ d0 (by simp [hd0]) d
  · intro x hx; simpa [M.vert_rot] using hx
  · intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    by_cases h : M.vert x = M.vert (M.opp x)
    · rwa [← h]
    · exact hx.trans (SimpleGraph.Adj.reachable ⟨h, x, rfl, rfl⟩)

/-- Every non-root vertex has a neighbour one step closer to `r`. -/
theorem exists_dart_toward (hM : M.Connected) (r v : V) (hv : v ≠ r) :
    ∃ d, M.vert d = v ∧ M.graph.dist r (M.head d) + 1 = M.graph.dist r v := by
  obtain ⟨p, hp⟩ := (M.reachable_of_connected hM v r).exists_walk_length_eq_dist
  cases p with
  | nil => simp_all
  | cons hadj q =>
    rename_i w
    obtain ⟨_, d, hd, hdw⟩ := id hadj
    refine ⟨d, hd, ?_⟩
    rw [hdw]
    rw [SimpleGraph.Walk.length_cons] at hp
    have h1 := SimpleGraph.dist_le q
    obtain ⟨q', hq'⟩ := (M.reachable_of_connected hM w r).exists_walk_length_eq_dist
    have h2 := SimpleGraph.dist_le (SimpleGraph.Walk.cons hadj q')
    rw [SimpleGraph.Walk.length_cons] at h2
    rw [SimpleGraph.dist_comm (u := r), SimpleGraph.dist_comm (u := r)]
    omega

variable [DecidableEq V]

/-- **BFS tree.**  A connected map has a spanning tree rooted at any vertex `r` whose levels are
the graph distances from `r`; in particular every dart joins levels differing by at most one. -/
theorem exists_bfsTree (hM : M.Connected) (r : V) :
    ∃ T : SpanTree M, T.root = r ∧ (∀ v, T.level v = M.graph.dist r v) := by
  classical
  obtain ⟨d0, -⟩ := M.vert_surj r
  let par : V → D := fun v =>
    if hv : v = r then d0 else Classical.choose (M.exists_dart_toward hM r v hv)
  refine ⟨⟨r, fun v => M.graph.dist r v, par, by simp, ?_, ?_⟩, rfl, fun v => rfl⟩
  all_goals grind

end BFS

end CombMap

end

end Chazelle.Separator
