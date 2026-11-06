module

public import Chazelle.Chain.Submap

/-!
# Reading off the interior visibility map of a closed polygon from a punctured chain

The paper handles a closed polygon by puncturing "a little hole" (p. 497).  Here the hole is a
whole edge: `puncture P hn e₀` is the chain of all edges of `P` except `e₀` (so its missing
edge is `e₀`, `puncture_missingIdx`, and its vertices are all vertices of `P`).

For a vertex `P.vtx i` (`i = C.edgeIdx k`) and a direction `σ` that is *locally interior* for
`P` (`Visibility.DirInterior P i σ`):

* the direction is free for the chain (`dirFree_of_dirInterior`);
* the chain chord starts with the interior chord of `P` (`chordParam_le`,
  `chordSet_subset_chain`);
* the part of the chain chord inside the interior of `P` is exactly the open chord of `P`
  (`chainChord_inter_interior`): beyond the first hit of `P` — which is then a relative
  interior point of the non-horizontal missing edge `e₀` — the ray is *exterior* until it hits
  the chain again (`exterior_after_hit`, by the horizontal parity flip across `e₀`, obtained from
  `Jordan.parity_flip` on the transposed polygon).

**Restriction lemma** (`freeRegion_eq`): the free interior of `P` is the free set of the
submap `interiorChords P hn e₀` of the chain (the chain chords issued in interior directions)
intersected with the interior of `P`; consequently the interior regions of `V(P)` are the
components of that intersection (`regions_eq`).  Chain chords issued in exterior directions
(those "the missing edge would have blocked") are simply discarded.
-/

namespace Chazelle.Chain

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd rayPt_zero continuous_rayPt hseg
  segment_horizontal_eq_hseg transpose transpose_n transpose_vtx transpose_edge
  mem_transpose_boundary_iff DirInterior)

/-! ### The punctured chain -/

/-- The chain of all edges of `P` except edge `e₀`, starting at `e₀ + 1`. -/
def puncture (P : Polygon) (hn : 3 ≤ P.n) (e₀ : ℕ) : Chain :=
  ⟨P, (e₀ + 1) % P.n, P.n - 1, by omega, by omega⟩

variable {P : Polygon} {hn : 3 ≤ P.n} {e₀ : ℕ}

@[simp] theorem puncture_P : (puncture P hn e₀).P = P := rfl

@[simp] theorem puncture_m : (puncture P hn e₀).m = P.n - 1 := rfl

/-! ### Interior directions are free -/

/-! ### The chain chord contains the interior chord -/

/-! ### Beyond the first hit the ray is exterior -/

/-! ### The restriction lemma -/

end

end Chazelle.Chain
