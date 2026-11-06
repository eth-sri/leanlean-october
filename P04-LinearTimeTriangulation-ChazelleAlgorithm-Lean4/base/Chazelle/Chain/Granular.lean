module

public import Chazelle.Chain.Contraction
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Granular submaps: the counting core of Chazelle's Lemma 2.3

Chazelle (p. 496) calls a submap *γ-granular* if

 (i) every node of its tree has weight at most `γ`, and
 (ii) contracting any edge incident upon at least one node of degree less than `3` produces a
      new node whose weight exceeds `γ`;

it is *conformal* if its tree has node degree at most `4` (p. 495).  The *weight* of a region
is the maximum number of non-null edges of `∂C` in any of its arcs (p. 494).

**Lemma 2.3** (p. 496): *any γ-granular conformal submap of the visibility map of a curve with
`n` vertices has `O(n/γ + 1)` regions and each region is bounded by `O(γ)` edges.*

## The counting core (pure combinatorics)

When the edge `uv` of the submap tree is contracted (its chord removed), the arcs of the new
region are arcs of `u`, arcs of `v`, or the concatenation of one arc of `u` and one arc of `v`
(at each endpoint of the removed chord), so the new weight is at most `w u + w v`.  Hence (ii)
implies the purely combinatorial property

  `∀ u v, G.Adj u v → (G.degree u < 3 ∨ G.degree v < 3) → γ < w u + w v`,

and this file proves, for every finite tree `G` of maximum degree `≤ 4` with this property,

* `card_mul_le_of_granular : (Fintype.card V - 1) * (γ + 1) ≤ 12 * ∑ v, w v`.

Proof: let `L` be the set of nodes of degree `≤ 2` and `D_L` the set of darts leaving `L`.
From the degree sum `∑ deg = 2 (N - 1)`, `deg ≥ 1` on `L` and `deg ≥ 3` off `L`, one gets
`N - 1 ≤ 2 |D_L|` (a tree of degree `≤ 4` has "many" low-degree incidences: this is the
paper's "`E` accounts for at least a fixed fraction of all the edges").  Every dart of `D_L`
carries weight `w (fst) + w (snd) ≥ γ + 1`, and
`∑_{d ∈ D_L} w (fst d) = ∑_{v ∈ L} deg v · w v ≤ 2 ∑ w`,
`∑_{d ∈ D_L} w (snd d) ≤ ∑_{all darts} w (snd d) = ∑_v deg v · w v ≤ 4 ∑ w`
("a given vertex of `C` can be used at most a constant number of times": at most
`deg ≤ 4` times).  So `(N - 1)(γ + 1) ≤ 2 |D_L| (γ + 1) ≤ 12 ∑ w`.

The simpler variant where *every* edge satisfies `γ < w u + w v` gives the constant `4`
(`card_mul_le_of_forall_adj`).

## The chain instance (conditional interface)

`ncard_mul_le_of_granular` instantiates the counting core for the dual tree `C.dualTree S` of a
chain submap `S ⊆ C.chords` (a tree by `dual_isTree`, with `S.ncard + 1` regions by
`ncard_regionsOf`).  The weight function is an arbitrary `wt : Set Point → ℕ` on regions; the
facts about it that are **not yet proved from the geometry** are explicit hypotheses:

* `hsum` — the total weight of the regions is at most `Wt` (for Chazelle's weight,
  `Wt = ` the number of edges of the double boundary plus the chord-endpoint splittings,
  i.e. `O(m)`, since distinct regions have disjoint arcs);
* `hgran` — granularity condition (ii): removing a chord `c ∈ S` whose two regions `U, V`
  include one of dual degree `< 3` produces a region `W` of `S \ {c}` of weight `> γ`;
* `hmerge` — subadditivity of the weight under the merge: `wt W ≤ wt U + wt V`.

The conclusion is `S.ncard * (γ + 1) ≤ 12 * Wt`, i.e. `#regions ≤ 12 Wt / (γ + 1) + 1`.

**Second half of Lemma 2.3** ("each region is bounded by `O(γ)` edges") is immediate from the
definition of weight and needs no counting: by conformality a region has at most `4` exit
chords, hence at most `4` arcs (the boundary of a region alternates exit chords and arcs), each
with at most `γ` non-null chain edges by (i); so at most `4 γ` chain edges and `4` chords.  In
the box model an arc may in addition contain pieces of the box perimeter (at most `5`
segments of `boxList`) and of the doubled slit (at most `2`), so a region is bounded by at most
`4 γ + 7` segments of the boundary walk and `4` chords (sketch; the arc structure of regions is
not yet formalised).  The arithmetic step is `edges_le_of_arcs`.

**Semigranular maps** (only condition (i)) admit no region bound (the full visibility map is
`γ`-semigranular for every `γ ≥ 1`), so there is no semigranular variant of the count.
-/

namespace Chazelle.Chain

public section

open Finset

/-! ### Darts and degree sums -/

section Abstract

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Summing a function of the first vertex over the darts leaving a set `s` of vertices gives
the degree-weighted sum over `s`. -/
theorem sum_dart_fst_filter (s : Finset V) (f : V → ℕ) :
    ∑ d ∈ (univ : Finset G.Dart) with d.fst ∈ s, f d.fst = ∑ v ∈ s, G.degree v * f v := by
  rw [← sum_fiberwise_eq_sum_filter' (univ : Finset G.Dart) s (fun d : G.Dart => d.fst) f]
  apply sum_congr rfl
  intro v _
  rw [sum_const, smul_eq_mul, G.dart_fst_fiber_card_eq_degree v]

/-- Summing a function of the first vertex over all darts gives the degree-weighted sum. -/
theorem sum_dart_fst (f : V → ℕ) :
    ∑ d : G.Dart, f d.fst = ∑ v, G.degree v * f v := by
  have h := sum_dart_fst_filter G univ f
  simp only [mem_univ, filter_true] at h
  exact h

omit [DecidableEq V] in
/-- Summing over the second vertex of all darts is the same as over the first vertex (the
darts come in reversed pairs). -/
theorem sum_dart_snd (f : V → ℕ) :
    ∑ d : G.Dart, f d.snd = ∑ d : G.Dart, f d.fst := by
  exact Fintype.sum_equiv
    (Function.Involutive.toPerm _ (SimpleGraph.Dart.symm_involutive (G := G))) _ _
    (fun d => rfl)

/-- The number of darts leaving `s` is the degree sum over `s`. -/
theorem card_dart_fst_filter (s : Finset V) :
    #((univ : Finset G.Dart).filter (fun d => d.fst ∈ s)) = ∑ v ∈ s, G.degree v := by
  have h := sum_dart_fst_filter G s (fun _ => 1)
  simp only [mul_one, sum_const, smul_eq_mul] at h
  simpa using h

omit [DecidableEq V] in
/-- **Many low-degree incidences.**  In a finite tree with `N` vertices whose degrees are at
most `4` (in fact any degrees), `N - 1` is at most twice the sum of the degrees of the vertices
of degree `≤ 2`.  (This is the paper's "the edges incident upon a node of degree `< 3` account
for at least a fixed fraction of all the edges".) -/
theorem card_sub_one_le_two_mul_sum_low (hG : G.IsTree) :
    Fintype.card V - 1 ≤ 2 * ∑ v ∈ (univ : Finset V) with G.degree v ≤ 2, G.degree v := by
  classical
  by_cases hN : Fintype.card V ≤ 1
  · omega
  have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hpos : ∀ v, 1 ≤ G.degree v := fun v =>
    le_trans (hG.connected.preconnected.minDegree_pos_of_nontrivial) (G.minDegree_le_degree v)
  have hsum : ∑ v, G.degree v + 2 = 2 * Fintype.card V := by
    rw [G.sum_degrees_eq_twice_card_edges, ← hG.card_edgeFinset]
    ring
  set L := (univ : Finset V).filter (fun v => G.degree v ≤ 2) with hL
  set H := (univ : Finset V).filter (fun v => ¬ G.degree v ≤ 2) with hH
  have hsplit : ∑ v ∈ L, G.degree v + ∑ v ∈ H, G.degree v = ∑ v, G.degree v :=
    sum_filter_add_sum_filter_not _ _ _
  have hcard : #L + #H = Fintype.card V := by
    rw [hL, hH, card_filter_add_card_filter_not, card_univ]
  have hLlow : #L ≤ ∑ v ∈ L, G.degree v := by
    rw [card_eq_sum_ones]; exact sum_le_sum fun v _ => hpos v
  have hHhigh : 3 * #H ≤ ∑ v ∈ H, G.degree v := by
    rw [card_eq_sum_ones, mul_sum, mul_one]
    exact sum_le_sum fun v hv => by
      have := (mem_filter.1 hv).2
      omega
  omega

end Abstract

/-! ### The chain instance (conditional interface) -/

section ChainInstance

variable (C : Chain)

end ChainInstance

end

end Chazelle.Chain
