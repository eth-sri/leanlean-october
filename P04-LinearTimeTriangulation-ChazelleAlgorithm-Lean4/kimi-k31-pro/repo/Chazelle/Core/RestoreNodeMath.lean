module

public import Chazelle.Core.RestoreDescGeo

/-!
# WP-E, the search: the side of a node chord in a stretch

Offsets `0 < v < L` of a stretch (keys of `Cα`'s model rotated to the stretch start).  The node
chord has its ends at offsets `da`, `βb`.  An end in the open stretch is tested; the test leaves
the offsets `v` with `sideInArc d α' v ↔ s` (`EndInfo`), where an arrival `α'` in the open
stretch is at the other end (M2').  `stretch_side`: all offsets left by both tests are on the same
side of the node chord (`witness_side` when an end is in the open stretch, `side_const` when none
is).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Chain (sideInArc)

/-- **What the test at an end leaves**: if the end `d` is in the open stretch, the offsets
satisfying `G` are those on one side of the arrival `α'`, which is at the other end `d'` when it
is in the open stretch. -/
def EndInfo (L d d' : ℝ) (G : ℝ → Prop) : Prop :=
  0 < d → d < L → ∃ α' : ℝ, ∃ s : Prop, 0 ≤ α' ∧ (0 < α' → α' < L → α' = d') ∧
    ∀ v, G v ↔ (sideInArc d α' v ↔ s)

/-- With both ends outside the open stretch, the side is constant on it. -/
theorem side_const {L d b v w : ℝ} (hd : d = 0 ∨ L ≤ d) (hb : b = 0 ∨ L ≤ b) (hv0 : 0 < v)
    (hvL : v < L) (hw0 : 0 < w) (hwL : w < L) : sideInArc d b v ↔ sideInArc d b w := by
  rcases hd with rfl | hd <;> rcases hb with rfl | hb <;> unfold sideInArc <;>
    split_ifs with h <;> constructor <;> intro h' <;>
    first
    | (left; linarith)
    | (right; linarith)
    | (exact ⟨by linarith, by linarith⟩)
    | (exfalso; rcases h' with h' | h' <;> linarith)

theorem out_of {L y : ℝ} (hy : 0 ≤ y) (h : ¬ (0 < y ∧ y < L)) : y = 0 ∨ L ≤ y := by
  rcases hy.lt_or_eq with hy | hy
  · right; by_contra h'; exact h ⟨hy, lt_of_not_ge h'⟩
  · left; exact hy.symm

/-- **The side of the node chord is the same for all offsets left by the tests.** -/
theorem stretch_side {L da βb : ℝ} (hda0 : 0 ≤ da) (hβ0 : 0 ≤ βb) (hne : da ≠ βb)
    {GA GB : ℝ → Prop} (hA : EndInfo L da βb GA) (hB : EndInfo L βb da GB)
    {u x : ℝ} (hu0 : 0 < u) (huL : u < L) (hx0 : 0 < x) (hxL : x < L) (hua : u ≠ da)
    (hub : u ≠ βb) (hxa : x ≠ da) (hxb : x ≠ βb) (hAu : GA u) (hAx : GA x) (hBu : GB u)
    (hBx : GB x) : sideInArc da βb u ↔ sideInArc da βb x := by
  by_cases ha : 0 < da ∧ da < L
  · obtain ⟨α', sA, hα0, hα', hGA⟩ := hA ha.1 ha.2
    exact witness_side ha.1 ha.2 hβ0 hne hα0 hα' hB hu0 huL hx0 hxL hua hub hxa hxb
      ((hGA u).1 hAu) ((hGA x).1 hAx) hBu hBx
  · by_cases hb : 0 < βb ∧ βb < L
    · obtain ⟨β', sB, hβ0', hβ', hGB⟩ := hB hb.1 hb.2
      have h := witness_side hb.1 hb.2 hda0 (Ne.symm hne) hβ0' hβ' hA hu0 huL hx0 hxL hub hua
        hxb hxa ((hGB u).1 hBu) ((hGB x).1 hBx) hAu hAx
      rw [Chazelle.Chain.sideInArc_swap (Ne.symm hne) hub hua,
        Chazelle.Chain.sideInArc_swap (Ne.symm hne) hxb hxa] at h
      exact not_iff_not.1 h
    · exact side_const (out_of hda0 ha) (out_of hβ0 hb) hu0 huL hx0 hxL

end

end Restore

end Chazelle.Core
