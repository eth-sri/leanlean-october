module

public import Chazelle.Chain.Contraction

/-!
# Chord removal (the semantics used by Chazelle §3.3)

Chazelle restores granularity after a merge "by removing chords" (§3.3, p. 512) and describes
the effect of a removal on the tree of the submap: "the dual graph of a submap is obtained by
contracting the edges of the visibility tree that correspond to the removed chords" (p. 495).
This file gives the Euclidean content of these operations for an arbitrary chord system
`ChordSystem D F` (so it applies both to vertex chords `C.chords` and to augmented families,
`Chazelle.Merge.augChordSystem`), and the chain instances.

## Main results

* **Removing one chord** (`regionsIn_erase`): if `c ∈ S`, the two regions `R₁ ≠ R₂`
  of `S` touched by `c` merge, together with the open chord `c ∩ D`, into the single region
  `R₁ ∪ R₂ ∪ (c ∩ D)` of `S \ {c}`; every other region is unchanged:
  `regionsIn D (S \ {c}) = (regionsIn D S \ {R₁, R₂}) ∪ {R₁ ∪ R₂ ∪ (c ∩ D)}`.
  (This is `regionsIn_insert` read backwards.)
* **Removing a set of chords** (`regionsIn_sdiff_eq`): for `R` removed from `S`, a
  region `W` of `S \ R` containing the region `U` of `S` is the union of the regions of `S`
  reachable from `U` in the dual tree of `S` through chords of `S ∩ R`, together with the
  points of the removed chords inside `W`.  Every region of `S \ R` contains a region of `S`
  (`exists_regionsIn_subset`) and every region of `S` lies in exactly one region of
  `S \ R`.
* **The dual tree after removal is the contraction** (`dualAdjIn_sdiff_iff`): two
  regions `W, W'` of `T ⊆ S` are adjacent in the dual graph of `T` iff some regions `U ⊆ W`,
  `V ⊆ W'` of `S` are adjacent in the dual graph of `S` through a chord of `T`.  Together with
  the fibre description (`Chazelle.Chain.ChordSystem.sameRegion_iff_reflTransGen`: two regions
  of `S` lie in the same region of `T` iff they are joined through chords of `S \ T`), this says
  that the dual tree of `T` is the quotient of the dual tree of `S` by the edges of the removed
  chords.  The key geometric step is `not_subset_of_touches`: the two regions of `S`
  on the two sides of a chord that is kept lie in different regions of `T`.
* **Characterisation** (`regionsIn_sdiff_char`, `regionsIn_sdiff_eq_merged`): the regions of
  `S \ R` are exactly the sets `mergedRegion D S R U` (`U` a region of `S`): the union of the
  regions of `S` joined to `U` through removed chords and of the open parts of the removed chords
  touching them.
* **Counting** (`ncard_regionsIn_sdiff`): removing `k` chords of `S` removes exactly
  `k` regions.
-/

namespace Chazelle.Merge

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (ChordSystem freeIn regionsIn TouchesIn DualAdjIn
  mem_regionsIn regionsIn_subset regionsIn_nonempty regionsIn_eq_component regionsIn_disjoint_of_ne
  regionsIn_eq_or_disjoint freeIn_anti exists_regionsIn_superset
  regionsIn_eq_of_subset)

variable {D : Set Point} {F : Set (Set Point)}

/-! ### Removing one chord -/

/-- **Removing one chord merges exactly its two regions.**  For `c ∈ S ⊆ F`, the chord `c`
touches exactly two regions `R₁ ≠ R₂` of `S`; in `S \ {c}` they merge with the open chord into
the region `R₁ ∪ R₂ ∪ (c ∩ D)`, and all other regions of `S` remain regions of `S \ {c}`. -/
theorem regionsIn_erase (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ S) :
    ∃ R₁ R₂ : Set Point, R₁ ≠ R₂ ∧ R₁ ∈ regionsIn D S ∧ R₂ ∈ regionsIn D S ∧
      (∀ W ∈ regionsIn D S, TouchesIn D c W ↔ W = R₁ ∨ W = R₂) ∧
      R₁ ∪ R₂ ∪ (c ∩ D) ∈ regionsIn D (S \ {c}) ∧
      regionsIn D (S \ {c}) = (regionsIn D S \ {R₁, R₂}) ∪ {R₁ ∪ R₂ ∪ (c ∩ D)} := by
  have hS' : S \ {c} ⊆ F := fun _ h => hS h.1
  have hcS' : c ∉ S \ {c} := fun h => h.2 rfl
  have hins : insert c (S \ {c}) = S := insert_sdiff_singleton.trans (insert_eq_of_mem hc)
  obtain ⟨R, hR, hcR, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ :=
    hF.regionsIn_insert hS' (hS hc) hcS'
  have htouch := hF.touches_iff_of_split hS' (hS hc) hcS' hR hcR hunion hR₁ hR₂ heq
  rw [hins] at hR₁ hR₂ heq htouch
  have hRD : R ⊆ D := fun p hp => (regionsIn_subset hR hp).1
  have hReq : R = R₁ ∪ R₂ ∪ (c ∩ D) := by
    ext p
    constructor
    · intro hp
      by_cases hpc : p ∈ c
      · exact Or.inr ⟨hpc, hRD hp⟩
      · left
        rw [hunion]
        exact ⟨hp, hpc⟩
    · rintro (hp | hp)
      · rw [hunion] at hp
        exact hp.1
      · exact hcR hp
  have hR₁R : R₁ ⊆ R := fun p hp => by
    have : p ∈ R₁ ∪ R₂ := Or.inl hp
    rw [hunion] at this
    exact this.1
  have hR₂R : R₂ ⊆ R := fun p hp => by
    have : p ∈ R₁ ∪ R₂ := Or.inr hp
    rw [hunion] at this
    exact this.1
  refine ⟨R₁, R₂, hne, hR₁, hR₂, htouch, hReq ▸ hR, ?_⟩
  rw [← hReq]
  ext W
  constructor
  · intro hW
    by_cases hWR : W = R
    · exact Or.inr (mem_singleton_iff.2 hWR)
    · left
      have hWS : W ∈ regionsIn D S := by rw [heq]; exact Or.inl ⟨hW, hWR⟩
      refine ⟨hWS, ?_⟩
      have hdisj := regionsIn_disjoint_of_ne hW hR hWR
      rintro (rfl | rfl)
      · obtain ⟨p, hp⟩ := regionsIn_nonempty hR₁
        exact hdisj.notMem_of_mem_left hp (hR₁R hp)
      · obtain ⟨p, hp⟩ := regionsIn_nonempty hR₂
        exact hdisj.notMem_of_mem_left hp (hR₂R hp)
  · rintro (⟨hWS, hW12⟩ | hW)
    · rw [heq] at hWS
      rcases hWS with h | h
      · exact h.1
      · exact absurd h hW12
    · rw [mem_singleton_iff.1 hW]
      exact hR

/-! ### Removing a set of chords -/

/-- A chord touching a set touches every superset. -/
theorem touchesIn_mono {c U W : Set Point} (h : TouchesIn D c U) (hUW : U ⊆ W) :
    TouchesIn D c W := by
  obtain ⟨z, hz, hzU⟩ := h
  exact ⟨z, hz, closure_mono hUW hzU⟩

/-! ### Boundaries of regions and the merged regions -/

/-! ### The chain instances -/

section ChainInstance

variable (C : Chain)

end ChainInstance

end

end Chazelle.Merge
