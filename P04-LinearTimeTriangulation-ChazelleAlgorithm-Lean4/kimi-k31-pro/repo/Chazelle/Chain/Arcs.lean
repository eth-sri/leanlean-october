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

/-- The sign of a side: `true` (left side) `↦ 1`, `false` (right side) `↦ -1`. -/
def boolSgn (b : Bool) : ℝ := if b then 1 else -1

variable (C : Chain)

/-- The point of the chain edge `k` at parameter `t`. -/
def edgeLerp (k : ℕ) (t : ℝ) : Point := lerp (C.vertex k) (C.vertex (k + 1)) t

/-- The *side point* of the chain edge `k` at parameter `t`, pushed by `δ` to the side `b`
(`true`: left of the direction `vertex k → vertex (k+1)`, `false`: right). -/
def edgeOffset (k : ℕ) (b : Bool) (t δ : ℝ) : Point :=
  offset (C.vertex k) (C.vertex (k + 1)) t (boolSgn b * δ)

theorem vertex_succ_eq (k : ℕ) : C.vertex (k + 1) = C.P.vtx ((C.edgeIdx k + 1) % C.P.n) := by
  unfold vertex
  rw [edgeIdx_succ]

/-- The chain edges have distinct indices in `P`. -/
theorem edgeIdx_inj {j k : ℕ} (hj : j < C.m) (hk : k < C.m) (h : C.edgeIdx j = C.edgeIdx k) :
    j = k := by
  unfold edgeIdx at h
  have h1  := h
  have h2  := Nat.ModEq.add_left_cancel' C.s h1
  exact Nat.ModEq.eq_of_lt_of_lt h2 (by have := C.m_lt; omega) (by have := C.m_lt; omega)

/-! ### Cut parameters -/

/-- The *cut parameters* of the chain edge `k` for the submap `S`: the parameters `t ∈ (0, 1)`
of the points of the open edge lying on a chord of `S` (necessarily chord endpoints). -/
def cutSet (S : Set (Set Point)) (k : ℕ) : Set ℝ :=
  {t | t ∈ Ioo (0 : ℝ) 1 ∧ C.edgeLerp k t ∈ ⋃₀ S}

/-! ### Side points near an open edge are free -/

/-! ### Facing a region -/

/-- The side `b` of the chain edge `k` *faces* the set `R` at the parameter `t`: the side points
`edgeOffset k b t δ` lie in `R` for all small `δ > 0`. -/
def FacesAt (k : ℕ) (b : Bool) (t : ℝ) (R : Set Point) : Prop :=
  ∀ᶠ δ in 𝓝[>] (0 : ℝ), C.edgeOffset k b t δ ∈ R

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

/-- The next cut parameter after `a` on the chain edge `k` (or `1` if there is none). -/
noncomputable def nextCut (S : Set (Set Point)) (k : ℕ) (a : ℝ) : ℝ :=
  sInf (insert 1 {c | c ∈ C.cutSet S k ∧ a < c})

section NextCut

variable {S : Set (Set Point)} {k : ℕ}

end NextCut

/-- The *pieces* of the sides of the chain edges cut by the chord endpoints of `S`: a piece is
a triple `(k, b, a)` (edge `k < m`, side `b`, start parameter `a`) where `a = 0` or `a` is a cut
parameter; it covers the parameters `Ioo a (nextCut S k a)`. -/
def pieces (S : Set (Set Point)) : Set (ℕ × Bool × ℝ) :=
  {x | x.1 < C.m ∧ (x.2.2 = 0 ∨ x.2.2 ∈ C.cutSet S x.1)}

/-- The open parameter interval covered by a piece. -/
noncomputable def pieceSet (S : Set (Set Point)) (x : ℕ × Bool × ℝ) : Set ℝ :=
  Ioo x.2.2 (C.nextCut S x.1 x.2.2)

section PieceFacts

variable {S : Set (Set Point)} {x : ℕ × Bool × ℝ}

end PieceFacts

/-- The piece `x` faces the region `R`: at every parameter of the piece, the side of the piece
faces `R`. -/
def PieceFaces (S : Set (Set Point)) (x : ℕ × Bool × ℝ) (R : Set Point) : Prop :=
  ∀ t ∈ C.pieceSet S x, C.FacesAt x.1 x.2.1 t R

/-! ### Chords arriving at a cut parameter -/

/-! ### Incidences and their number -/

end

end Chazelle.Chain
