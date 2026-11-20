module

public import Chazelle.Separator.LiptonTarjan

/-!
# Recursive separation into clusters (planar separators, part 5)

The form of the separator theorem used by Chazelle's Lemma 3.6 (p. 514): the vertices of a
planar graph on `μ` nodes can be split into a set `D*` of `O(μ^{2/3})` nodes and clusters of at
most `μ^{2/3}` nodes such that no path joins two clusters without passing through `D*`.

**Theorem** (`planar_clusters`).  For every planar map on `n` vertices and every `k ≥ 1` there are
`D* ⊆ V` with `k·|D*| ≤ 7n` and a cluster labelling `cl : V → V` of the vertices off `D*`, constant
along every edge off `D*`, all of whose clusters have at most `k²` vertices.
(`planar_clusters_cube`: if `n ≤ k³` then `|D*| ≤ 7k²`; with `k = ⌈n^{1/3}⌉` this is
`|D*| = O(n^{2/3})`, clusters `≤ k² = O(n^{2/3})`.)

Proof (Frederickson-style, but without separating subgraphs: every split is done in the one
triangulated map, with the weights restricted to the piece being split):

1. BFS levels; a residue class `ρ` of levels modulo `k` holds at most `n/k` vertices (`H`); the
   other vertices fall into *slabs* of at most `k` consecutive levels, and no edge joins two
   slabs off `H`.
2. Inside a slab, a piece `P` with more than `s = k²` vertices is split by the face separator of
   the triangulation with weights `1_P` (`exists_face_separator`): the separator meets the slab
   in at most `3k` vertices (three root paths), the label classes have at most `|P|/2` vertices
   and are not adjacent off the separator.  Recursing (`exists_split`) with the potential
   `s·|D_P| ≤ 3k (2|P| − s)` (`sum_split_bound`) gives `k·|D_slab| ≤ 6 |slab|`.
-/

namespace Chazelle.Separator

@[expose] public section

open Finset

/-- The numerical heart of the recursion: pieces of size at most `M/2` with total at most `M`,
`M > s`, satisfy `s + Σ (2 m_d − s) ≤ 2M − s` (truncated subtraction). -/
theorem sum_split_bound {ι : Type*} [DecidableEq ι] (L : Finset ι) (m : ι → ℕ) (M s : ℕ)
    (hsum : ∑ d ∈ L, m d ≤ M) (hhalf : ∀ d ∈ L, 2 * m d ≤ M) (hMs : s < M) :
    s + ∑ d ∈ L, (2 * m d - s) ≤ 2 * M - s := by
  set J := L.filter (fun d => s < 2 * m d)
  have hJ : ∑ d ∈ L, (2 * m d - s) = ∑ d ∈ J, (2 * m d - s) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    split_ifs with h
    · rfl
    · omega
  have hkey : ∑ d ∈ J, (2 * m d - s) + J.card * s = 2 * ∑ d ∈ J, m d := by
    rw [Finset.mul_sum, ← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have := (Finset.mem_filter.mp hd).2
    omega
  have hJsum : ∑ d ∈ J, m d ≤ M :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)) hsum
  rw [hJ]
  rcases Nat.lt_or_ge J.card 2 with h | h
  · rcases (show J.card = 0 ∨ J.card = 1 by omega) with h0 | h1
    · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]; omega
    · obtain ⟨d, hd⟩ := Finset.card_eq_one.mp h1
      have hdL : d ∈ L := (Finset.mem_filter.mp (hd ▸ Finset.mem_singleton_self d)).1
      rw [hd, Finset.card_singleton, Finset.sum_singleton, Finset.sum_singleton] at hkey
      rw [hd, Finset.sum_singleton]
      have := hhalf d hdL
      omega
  · have : 2 * s ≤ J.card * s := Nat.mul_le_mul_right s h
    omega

namespace CombMap

variable {V F D : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype D]
  [DecidableEq D]

namespace SpanTree

variable {M : CombMap V F D} (T : SpanTree M)

end SpanTree

/-! ### Slabs of levels -/

section Slabs

end Slabs

end CombMap

end

end Chazelle.Separator
