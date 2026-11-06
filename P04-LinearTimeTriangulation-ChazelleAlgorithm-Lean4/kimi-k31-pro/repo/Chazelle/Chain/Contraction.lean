module

public import Chazelle.Chain.DualTree

/-!
# Contraction: the regions of a coarser submap

Domain-parametrised port of the second half of `Chazelle/Visibility/DualTree.lean`
(`SameRegion`, `sameRegion_iff_reflTransGen`, `subset_iff_reflTransGen`) to a `ChordSystem D F`.

For submaps `T ⊆ S ⊆ F`, two regions `U, V` of `S` lie in a common region of the coarser
submap `T` iff they are joined, in the dual graph of `S`, by a walk whose edges all come from
chords of `S \ T` (`ChordSystem.sameRegion_iff_reflTransGen`).  This is the formal content of
the paper's "the dual graph of a submap is obtained by contracting the edges of the visibility
tree that correspond to the removed chords" (p. 495): a region of `T` is the union of the
regions of `S` in one component of the forest obtained by keeping only the edges of `S \ T`.

The chain instance is `Chain.sameRegion_iff_reflTransGen`.
-/

namespace Chazelle.Chain

@[expose] public section

open Set Filter Topology Metric

variable {D : Set Point} {F : Set (Set Point)}

/-- Two regions containing a common nonempty set coincide. -/
theorem regionsIn_eq_of_subset {T : Set (Set Point)} {W W' : Set Point}
    (hW : W ∈ regionsIn D T) (hW' : W' ∈ regionsIn D T) {U : Set Point} (hU : U.Nonempty)
    (h1 : U ⊆ W) (h2 : U ⊆ W') : W = W' := by
  obtain ⟨p, hp⟩ := hU
  rw [regionsIn_eq_component hW (h1 hp), regionsIn_eq_component hW' (h2 hp)]

/-- Every region of a submap lies in a region of any coarser submap. -/
theorem exists_regionsIn_superset {S T : Set (Set Point)} (hT : T ⊆ S)
    {U : Set Point} (hU : U ∈ regionsIn D S) : ∃ W ∈ regionsIn D T, U ⊆ W := by
  obtain ⟨u, hu, rfl⟩ := hU
  have huT  := freeIn_anti D hT hu
  exact ⟨_, mem_regionsIn huT, connectedComponentIn_mono u (freeIn_anti D hT)⟩

/-! ### The chain instance -/

variable (C : Chain)

end

end Chazelle.Chain
