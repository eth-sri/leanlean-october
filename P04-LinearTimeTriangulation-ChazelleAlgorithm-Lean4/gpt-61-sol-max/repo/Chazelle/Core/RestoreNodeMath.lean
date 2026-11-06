module

public meta import Chazelle.Arithmetic

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



/-- **The side of the node chord is the same for all offsets left by the tests.** -/
theorem stretch_side {L da βb : ℝ} (hda0 : 0 ≤ da) (hβ0 : 0 ≤ βb) (hne : da ≠ βb)
    {GA GB : ℝ → Prop} (hA : EndInfo L da βb GA) (hB : EndInfo L βb da GB)
    {u x : ℝ} (hu0 : 0 < u) (huL : u < L) (hx0 : 0 < x) (hxL : x < L) (hua : u ≠ da)
    (hub : u ≠ βb) (hxa : x ≠ da) (hxb : x ≠ βb) (hAu : GA u) (hAx : GA x) (hBu : GB u)
    (hBx : GB x) : sideInArc da βb u ↔ sideInArc da βb x := by
  ram_grind

end

end Restore

end Chazelle.Core
