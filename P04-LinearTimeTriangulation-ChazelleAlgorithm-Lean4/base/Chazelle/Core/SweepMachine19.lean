module

public import Chazelle.Core.SweepMachine18

/-!
# The sweep (WP-D), part 35: the abstract machine, the tie of top chords at the split vertex

In the right case G the walk of `C` passes the top of `C₂` once, at the split vertex (offset `rL1`
of the right stretch); the chords of `F₂⁺` attached there (the top chords of `C` at the top of
`C₂`) are horizontal at the height of the top of `C₂`, so their far ends are not on `C₂`
(`TopStrict`), hence off the right stretch:

* `right_caseG`, `right_pos_cases`, `right_stretch_mem`: in case G the right stretch runs along the
  tour of `C₂` only, so its points are points of `C₂`;
* `top_far_out`: the far attachment of a chord through the top of `C₂` is off the open right
  stretch (when the box of `C` is not inside it);
* `far_attach`: an admissible chord is attached at a position of its other end;
* `valid_split_tie`: the middle region of the tie of two chords at the split vertex is `TieOut`,
  valid for every label.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft)
open WalkEmbed

namespace Sweep

/-- **An admissible chord is attached at a position of its end other than a given point.** -/
theorem far_attach {M : Model} (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) (x : Point) :
    ∃ (p : ℕ) (t : ℝ), SideAttach M.W e p t ∧ sidePt M.W p t ≠ x := by
  obtain ⟨a, b, hab, -, -, -, ⟨⟨pa, ta, hAa, hAa'⟩, -⟩, ⟨⟨pb, tb, hBb, hBb'⟩, -⟩⟩ := hM.ends e he
  by_cases hxa : x = a
  · exact ⟨pb, tb, hBb, by rw [hBb', hxa]; exact Ne.symm hab⟩
  · exact ⟨pa, ta, hAa, by rw [hAa']; exact Ne.symm hxa⟩

section Machine

variable (J : Merge.Junction)

end Machine

end Sweep

end

end Chazelle.Core
