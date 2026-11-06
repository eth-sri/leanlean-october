module

public import Chazelle.Core.SweepMachine13
public import Chazelle.MiscTactics

/-!
# The sweep (WP-D), part 30: the abstract machine, the start of the `C₁` part

* `start_pt`: the first position of the left stretch is the shared vertex.
* `start_chord`: a chord of `F₂⁺` attached there is a shared chord (the RAM precomputes them).
* `afterOK_of_noncut_vertex`: at a vertex key without chords the label passes from the region
  before the key to the region after it (the start without shared chords, `valid_start`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section Machine

variable (J : Merge.Junction)

/-- **The first position of the left stretch is the shared vertex.** -/
theorem start_pt (hP : J.P.Simple) :
    sidePt (chainModel J.whole).W
      ((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + 0) % (chainModel J.whole).W.n) 0 = J.shared := by
  have hC := corr_left0 J hP (S₁ := ∅) (empty_subset _) finite_empty
  have hd : 0 < lL1 J + lL2 J := by
    rw [lL1_add_lL2]; unfold llen; have := J.one_le_m₁; splao
  rw [hC.sidePt_eq hd 0, Chazelle.Chain.sidePt_zero]
  unfold dq
  rw [ite_eq_left (by
    unfold lL1; have := J.one_le_m₁; have := tpos_lt J.left J.m₁
    have hm : J.left.m = J.m₁ := rfl
    splao), add_zero]
  have := walk_tour J.left J.m₁ 0 (by have := tpos_lt J.left J.m₁; omega)
  rw [add_zero] at this
  rw [this]
  exact tourV_left_zero J

end Machine

end Sweep

end

end Chazelle.Core
