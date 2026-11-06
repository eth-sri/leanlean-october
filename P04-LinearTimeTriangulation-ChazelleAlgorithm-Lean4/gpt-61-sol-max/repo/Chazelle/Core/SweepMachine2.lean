module

public import Chazelle.Core.SweepMachine1

/-!
# The sweep (WP-D), part 18: the abstract machine, labels across chords

The machine processes the chords attached at an event key one by one, in the order in which the
walk turns around the key (a tie at a walk vertex has two chords: the one bounding the region before
the key, then the one bounding the region after it).  Its label is attached to **the side of the
last crossed chord**: `SideLabel J S₂ e ρ λ` says that `λ` is a valid label (`Valid`) of every
region of `F₂⁺` on the side `ρ` of the chord `e` (there is exactly one).

* `sideLabel_of_valid`: a valid label of a region on a side of a chord is a side label.
* `sideLabel_fused` (rule for a fused chord `e ⊆ c ∈ S₂` attached in the stretch away from the
  base and the split vertex): the region of `S₂` on the same side of `c`.
* `sideLabel_faced` (rule for a chord attached alone at a stretch position): the region of `S₂`
  faced in the model of `C₂` just after or just before the counterpart position
  (`rlabel_of_faced`).
* `sideLabel_tie_middle`: at a tie at a walk vertex the middle region is on the same side of both
  chords, so a side label passes from one chord to the other.
* `AfterOK`: the label is valid for the region faced just after an event key;
  `afterOK_unique`, `afterOK_tie`: it is the side label of the chord bounding that region;
  `valid_of_afterOK`: it is valid for every non-cut position up to the next cut (the queries).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft freeIn regionsIn)
open WalkEmbed

namespace Sweep

section Machine

variable (J : Merge.Junction)

/-- `λ` is a valid label of every region of `F₂⁺` on the side `ρ` of the chord `e`. -/
def SideLabel (S₂ : Set (Set Point)) (e : Set Point) (ρ : ℝ) (L : Set Point) : Prop :=
  ∀ G ∈ (chainModel J.whole).regions (F₂plus J S₂), SideOf (chainModel J.whole) ρ e G →
    Valid J S₂ G L

/-- **Rule for a fused chord**: `e ⊆ c ∈ S₂` attached at the stretch position `d` (not the base,
not the split vertex): the side labels of `e` are the regions of `S₂` on the same side of `c`. -/
theorem sideLabel_fused (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {e c : Set Point}
    (he : e ∈ F₂plus J S₂) (hc : c ∈ S₂) (hec : e ⊆ c) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    (hA : SideAttach (chainModel J.whole).W e
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {V : Set Point} (hV : V ∈ (chainModel J.right).regions S₂)
    (hVs : SideOf (chainModel J.right) ρ c V) : SideLabel J S₂ e ρ V :=
  fun _G hG hS => valid_of_vlabel J hP hS₂ hF hG hV
    ⟨e, c, ρ, d, t, he, hc, hec, hρ, hd, ht0, ht1, hsec, hA, hS, hVs⟩

end Machine

end Sweep

end

end Chazelle.Core
