module

public import Chazelle.Visibility.Chord

/-!
# The horizontal visibility map

`visibilityMap P` is the set of all vertex chords of `P` (`chords P`, see `Chord.lean`), and
`chordUnion P` their union: a closed subset of the filled region.  The *regions* of the map are
the connected components of the free interior `freeRegion P = (P.filled \ P.boundary) \
chordUnion P`.

This file proves the elementary structure only: the free interior is open, every region is a
nonempty open preconnected subset of it, two regions are equal or disjoint, and the regions
cover the free interior (`regions_open`, `regions_nonempty`, `regions_eq_or_disjoint`,
`sUnion_regions`).  That each region is (the interior of) a trapezoid with horizontal top and
bottom is *not* proved here.
-/

namespace Chazelle.Visibility

@[expose] public section

open Set Filter Topology
open Chazelle.Jordan

section
variable (P : Polygon)
include P
/-- The union of all vertex chords. -/
def chordUnion : Set Point := ⋃₀ chords P

/-- The free interior: the interior region minus all chords. -/
def freeRegion : Set Point := (P.filled \ P.boundary) \ chordUnion P

/-- The regions of the visibility map: the connected components of the free interior. -/
def regions : Set (Set Point) :=
  {C | ∃ z ∈ freeRegion P, C = connectedComponentIn (freeRegion P) z}

/-- The union of the chords is closed (finitely many closed segments). -/
theorem isClosed_chordUnion : IsClosed (chordUnion P) :=
  (chords_finite P).isClosed_sUnion fun _ hS => chords_isClosed hS


end

section
variable {P : Polygon}
/-- Every chord lies in the filled region. -/
theorem chordSet_subset_filled (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : chordSet P i σ ⊆ P.filled := by
  intro p hp
  rcases mem_chordSet_cases hP hi h hp with rfl | rfl | hint
  · exact boundary_subset_filled P ⟨i, hi, Geometry.left_mem_segment _ _⟩
  · exact boundary_subset_filled P (chordEnd_mem_boundary hP hi h)
  simp_all

/-- The free interior is open. -/
theorem isOpen_freeRegion (hP : P.Simple) : IsOpen (freeRegion P) :=
  (isOpen_filled_sdiff_boundary hP).sdiff (isClosed_chordUnion P)

/-- Every region lies in the free interior. -/
theorem regions_subset {C : Set Point} (hC : C ∈ regions P) : C ⊆ freeRegion P := by
  obtain ⟨z, -, rfl⟩ := hC
  exact connectedComponentIn_subset _ _

/-- Two regions are equal or disjoint. -/
theorem regions_eq_or_disjoint {C D : Set Point} (hC : C ∈ regions P)
    (hD : D ∈ regions P) : C = D ∨ Disjoint C D := by
  obtain ⟨z, -, rfl⟩ := hC
  obtain ⟨w, -, rfl⟩ := hD
  by_cases h : Disjoint (connectedComponentIn (freeRegion P) z)
      (connectedComponentIn (freeRegion P) w)
  · simp_all
  · left
    obtain ⟨p, hpz, hpw⟩ := not_disjoint_iff.1 h
    rw [connectedComponentIn_eq hpz, connectedComponentIn_eq hpw]


end

end

end Chazelle.Visibility
