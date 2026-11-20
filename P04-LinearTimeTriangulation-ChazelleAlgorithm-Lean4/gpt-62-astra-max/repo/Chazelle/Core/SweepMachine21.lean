module

public import Chazelle.Core.SweepMachine20

/-!
# The sweep (WP-D), part 37: the abstract machine, the answer of a query (interface for the RAM)

A query `q` of side `0` is a walk position of the model of `C₁` with a direction code; its point
`z` and direction `σ = dirOf q.2.2`.  The RAM answers it with a flag and a record `(h, lp, rp)`.
These theorems give `SeesInWhole J Q 0 q r` from the outputs of the RAM, stated as explicit
hypotheses:

* `seesInWhole_notFree`: flag `≠ 1` when the direction is not free for `C`;
* `seesInWhole_free`: flag `1`, the first hit parameter `T` of `C`, and the positions `pz`, `pw` of
  the walk of `C` (outputs of `wholePos`, with height code `h + 1`) of the query point and of the
  hit, at which the chord is attached; `lp`/`rp` the left and right ones;
* how `FreeAt` and `T` are obtained, one theorem per row of §9.5:
  - `hit_of_label` (general query: the arcs of the label `λ` in the model of `C₂`, any set `A₁` of
    the model of `C₁` giving its first hit, and the RAM minimum `T` over their union),
  - `hit_of_genuine` (two genuine first hits, e.g. the far end of a chord along the ray),
  - `hit_above` (above the top of `C₂`: the model of `C₁` only),
  - `hit_two_positions` (box-gap and box-block queries: positions in both models, `boxTwin`);
* `seesInWhole_of_label`, `seesInWhole_of_genuine`, `seesInWhole_above`,
  `seesInWhole_two_positions`: the four compositions.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section Machine

variable (J : Merge.Junction)

/-- The direction of a direction code. -/
theorem dirOf_cases (v : ℕ) : dirOf v = 1 ∨ dirOf v = -1 := by
  unfold dirOf; split_ifs <;> simp

/-! ## The first hit of `C`, one theorem per kind of query -/

/-! ## The compositions -/

/-- The data of an answer record at the first hit parameter `T`: positions of the walk of `C` of the
query point and of the hit point (height code `h + 1`), at which the chord is attached. -/
def RecordData (Q : Polygon) (z : Point) (σ T : ℝ) (h pz pw lp rp : ℕ) : Prop :=
  (Q.vtx h).2 = z.2 ∧ (chainModel J.whole).pos Q ⟨pz, h + 1⟩ = z ∧
    (chainModel J.whole).pos Q ⟨pw, h + 1⟩ = rayPt z σ T ∧
    SideAttach (chainModel J.whole).W (Chazelle.segment z (rayPt z σ T)) pz
      ((chainModel J.whole).param Q ⟨pz, h + 1⟩) ∧
    SideAttach (chainModel J.whole).W (Chazelle.segment z (rayPt z σ T)) pw
      ((chainModel J.whole).param Q ⟨pw, h + 1⟩) ∧
    (σ = 1 → lp = pz ∧ rp = pw) ∧ (σ = -1 → lp = pw ∧ rp = pz)

end Machine

end Sweep

end

end Chazelle.Core
