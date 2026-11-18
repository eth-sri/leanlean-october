module

public import Chazelle.Core.SweepEvStopLab

/-!
# The sweep (WP-D), stage 2: the middle of a split tie with a partner ending on `C₂` (contract)

`SplitGapTask` (mathematics): in case G (`0 < rδ`), let two chords `e ≠ e'` of `F₂⁺` be attached
at the split vertex of the right stretch (the copy `(gW + rL1, 0)` of the top `u` of `C₂`), `e`
also attached on the `C₁` part, `e'` also attached at a point `Y ≠ u` of the open right stretch (a
second point of `C₂` at the height of `u`: no `TopStrict`).  Then the region `G` on the same side
of both (the middle region of the tie) has a gap label (`GapLab`), as a label (`RLabel`) or a
virtual label (`VLabel`).

Intended proof: `e'` is an augmented chord of `C₂` (`partner_cases`), horizontal at the height
of `u` from `u` to `Y`; the points just above (below) it near `u` lie on one side of the slit of
`C₂` (`copy_facts`, `split_copy`, `other_copy_not_cut`) and form, with the points just beyond `Y`,
a connected set above the top height avoiding the chords of `S₂` (all at heights `≤ u.2`); so the
region of `S₂` faced just after `Y` (or just before, by the direction of the walk edge) in the
walk of `C₂` is faced along the slit — a gap label — and `G` is faced at `Y` in the walk of `C`
(`rlabel_after2` / `rlabel_before2`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Sweep
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

/-- **Task SG (mathematics): the middle region of a split tie with a partner ending on `C₂`.** -/
def SplitGapTask : Prop :=
  ∀ (J : Merge.Junction) (Q : Polygon) (S₂ : Set (Set Point)), J.P.Simple →
    (chainModel J.right).ChordFamily Q S₂ → (chainModel J.whole).ChordFamily Q (F₂plus J S₂) →
    0 < rδ J →
    ∀ e ∈ F₂plus J S₂, ∀ e' ∈ F₂plus J S₂, e' ≠ e →
    SideAttach (chainModel J.whole).W e ((gW J + rL1 J) % (chainModel J.whole).W.n) 0 →
    SideAttach (chainModel J.whole).W e' ((gW J + rL1 J) % (chainModel J.whole).W.n) 0 →
    (∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ (Lst J : ℝ) ≤ oW J (q + s)) →
    (∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e' q s ∧
      sidePt (chainModel J.whole).W q s ≠
        sidePt (chainModel J.whole).W ((gW J + rL1 J) % (chainModel J.whole).W.n) 0 ∧
      0 < oW J (q + s) ∧ oW J (q + s) < Lst J) →
    ∀ ρ : ℝ, (ρ = 1 ∨ ρ = -1) → ∀ G ∈ (chainModel J.whole).regions (F₂plus J S₂),
      SideOf (chainModel J.whole) ρ e G → SideOf (chainModel J.whole) ρ e' G →
      ∃ Vg, GapLab J S₂ Vg ∧ (RLabel J S₂ G Vg ∨ VLabel J S₂ G Vg)

end

end SweepEv

end Chazelle.Core
