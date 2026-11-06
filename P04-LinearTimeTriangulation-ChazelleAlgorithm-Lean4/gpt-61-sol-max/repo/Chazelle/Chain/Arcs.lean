module

public import Chazelle.Chain.Contraction

/-!
# Edge sides of the double boundary and the regions they face (Chazelle §2.2)

Chazelle (p. 490) thickens the chain `C` into an infinitesimally thin polygon whose boundary
is the *double boundary* `∂C`; every edge of `C` contributes two edges of `∂C`, one on each
side.  The boundary of a region of a submap alternates *exit chords* and *arcs* (pieces of
`∂C`), and the *weight* of a region counts the edges of `∂C` on its arcs (p. 494).

This file gives a Euclidean meaning to "the side `β` of the chain edge `k` near the point of
parameter `t` belongs to the region `R`", in the box model of `docs/design-subchain-model.md`,
and cuts the sides of the chain edges into the pieces that bound the regions of a submap.

## Edge-side offsets

For the chain edge `k` (from `vertex k` to `vertex (k+1)`), a parameter `t` and a side
`b : Bool` (`true` = left of the direction of the edge, `false` = right) the *side point*
`edgeOffset k b t δ = offset (vertex k) (vertex (k+1)) t (± δ)` is the point of the edge at
parameter `t` pushed by `δ` to the side `b` (`Chazelle.Jordan.offset`).

* `eventually_edgeOffset_mem_dom`: for every `t ∈ (0, 1)` and both sides, the side points are
  in `dom C` for all small `δ > 0` — no point of the relative interior of a chain edge is on the
  slit (the slit meets the chain only at the topmost vertex) or on another edge.
* `exists_free_nbhd`: **near a point of the relative interior of a chain edge that is not an
  endpoint of a chord of `S`, all side points are in the free set of `S`** (in the box, off the
  chain, off the slit and off the chords), uniformly for nearby parameters and small `δ > 0`.
  The exceptional parameters are the *cut parameters* `cutSet S k`, the parameters of the chord
  endpoints on the open edge (`exists_ball_free`, `exists_free_nbhd_side` for the one-sided
  versions).

## Facing a region

The side `(k, b)` *faces* the region `R` at the parameter `t` (`FacesAt k b t R`) if the side
points `edgeOffset k b t δ` lie in `R` for all small `δ > 0`.

* `facesAt_unique`: a side faces at most one region at a given parameter;
* `exists_facesAt_nbhd`: off the cut parameters it faces some region, and the same region at
  all nearby parameters (the side points of a small parallelogram along the edge form a
  connected subset of the free set); `existsUnique_facesAt`: **off the cut parameters a side
  faces exactly one region**;
* `exists_facesAt_Ioo`: on an open interval of parameters free of cuts, a side faces a single
  region.

## Pieces and incidences

The cut parameters of edge `k` are finitely many (`cutSet_finite`): a chord meets the chain
only at its two endpoints.  They cut each side of the edge into *pieces*: a piece is a triple
`(k, b, a)` with `a = 0` or `a` a cut parameter, and covers the open parameter interval
`Ioo a (nextCut S k a)` up to the next cut parameter (or `1`).

* `exists_pieceFaces`, `pieceFaces_unique`: **each piece faces exactly one region**;
* `facesAt_iff_exists_piece`: **structure of the facing set** — off the cut parameters, the side
  `(k, b)` faces `R` at `t` iff `t` lies in a piece facing `R`; so the set of parameters at which
  a side faces `R` is, up to the finitely many cut parameters, a finite union of open intervals
  whose endpoints are cut parameters (chord endpoints) or edge endpoints (`0`, `1`)
  (`facesSet_eq`, `startsFacing_finite`).
* The *incidences* `incidences S` are the pairs `(R, x)` of a region and a piece facing it;
  `ncard_incidences_eq : #incidences = #pieces`.
  `ncard_incidences_le`: **`#incidences ≤ 2m + 4|S|`**, via
  `ncard_incidences_le_chordEnds : #incidences ≤ 2 m + 2 #(chord endpoints on C)` (every cut
  parameter starts one new piece on each side of its edge) and
  `ncard_chordEndsOn_le : #(chord endpoints on C) ≤ 2 |S|`.

## Chords arriving at a cut parameter

A chord of `S` through the point of parameter `t` of edge `k` *arrives from the side `b`*
(`ChordFromSide S k b t`) if it has a point strictly on the side `b` of the line of the edge.

* `exists_facesAt_nbhd_side`: if no chord arrives from the side `b` at `t`, the side `b` faces a
  single region at all parameters near `t` (the cut at `t` is invisible from that side);
* `facesAt_ne_of_chordFromSide`: if a chord arrives from the side `b` at `t₀`, the side `b` faces
  different regions just before and just after `t₀` (the chord separates, Lemma 2.1 /
  `chord_separates`, and each side of it near `t₀` is joined to the side points by a free
  quarter-disk);
* `pieceFaces_next_iff`: hence two consecutive pieces of the same side face the same region iff
  no chord arrives from that side at the cut parameter between them.
-/

namespace Chazelle.Chain

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Geometry (lerp)

/-! ### Sides -/


variable (C : Chain)

section
variable (k : ℕ)
include k


theorem vertex_succ_eq : C.vertex (k + 1) = C.P.vtx ((C.edgeIdx k + 1) % C.P.n) := by
  unfold vertex
  rw [edgeIdx_succ]


end

/-- The chain edges have distinct indices in `P`. -/
theorem edgeIdx_inj {j k : ℕ} (hj : j < C.m) (hk : k < C.m) (h : C.edgeIdx j = C.edgeIdx k) :
    j = k := by
  unfold edgeIdx at h
  have h1 : C.s + j ≡ C.s + k [MOD C.P.n] := h
  have h2 : j ≡ k [MOD C.P.n] := Nat.ModEq.add_left_cancel' C.s h1
  exact Nat.ModEq.eq_of_lt_of_lt h2 (by have := C.m_lt; omega) (by have := C.m_lt; omega)

/-! ### Cut parameters -/


/-! ### Side points near an open edge are free -/

/-! ### Facing a region -/


/-! ### Chord endpoints on the chain -/

/-- The cardinality of a finite union is at most the sum of the cardinalities. -/
theorem ncard_biUnion_finset_le {ι α : Type*} (T : Finset ι) (s : ι → Set α) :
    (⋃ i ∈ T, s i).ncard ≤ ∑ i ∈ T, (s i).ncard := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    rw [Finset.sum_insert haT, Finset.set_biUnion_insert]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

/-! ### Pieces -/









/-! ### Chords arriving at a cut parameter -/

/-! ### Incidences and their number -/

end

end Chazelle.Chain
