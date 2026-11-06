module

public import Chazelle.Core.DownPhaseStepLocal
public import Chazelle.Core.DownPhaseExtractMain
public import Chazelle.Core.SpecPhases

/-!
# Down step, part 2: one level of the down phase, as a math theorem

For a nonempty interior chord family `S` of a simple polygon `Q` with degree `≤ d₀`, and, for every
region `R` of `S`, a chord gap `g R` and a chord family `F R` of the chain model of the host chain
`C_R = hostChain Q S R (g R)` with degree `≤ D` and `γ`-semigranular (what the merge chain of the
region produces), the family after the step,
`stepFam Q S F = S ∪ ⋃ R, kept R (F R)` (the chain chords meeting their region), satisfies
(**`downStep`**):

* (X1) it is a chord family of the interior model;
* (X3) its degree is at most `D + d₀`;
* (X2) it is `γ`-semigranular;
* (X4) its new chords are chords of the `F R`.

Proof: every region `V` of the new family lies in a region `R` of `S`; by independence across
regions (`DownPhaseStepLocal`) its exits and weight are those in `S ∪ kept R (F R)`, which are
bounded by the per-region extraction theorems (`Extract.deg_kept`, `Extract.weight_kept`).

`downStep_level`: the level instance (`d₀ = 4`, `D = D_H`, `γ₁ = 2 γ'_μ + 15`) and
`gamma1_le`: `γ₁ ≤ 2^(⌈βμ⌉ + 12)`.  Design: `docs/design-downphase-nf.md` §4.
-/

namespace Chazelle.Core

namespace DownStep

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (ChordSystem freeIn regionsIn TouchesIn)
open DownHost

/-- **The family after one down step.** -/
def stepFam (Q : Polygon) (S : Set (Set Point)) (F : Set Point → Set (Set Point)) :
    Set (Set Point) :=
  S ∪ ⋃ R ∈ (interiorModel Q).regions S, Extract.kept R (F R)

/-! ## The level instance -/

/-- The granularity after the merge chain of a region at merge grade `μ`: leaves `γ'_μ`, box
transport `2 γ'_μ`, at most `15` merges with `fuseLoss = 1`. -/
noncomputable def gamma1 (μ : ℕ) : ℕ := 2 * gradeGran μ + 15

/-- **The schedule**: `γ₁ ≤ 2^(⌈βμ⌉ + 12)`, the semigranularity bound (I2) of index `μ`. -/
theorem gamma1_le (μ : ℕ) : gamma1 μ ≤ 2 ^ (Cost.ceilBeta μ + 12) := by
  have h := gradeGran_le_real μ
  have hN : gradeGran μ ≤ 1201 * 2 ^ Cost.ceilBeta μ := by exact_mod_cast h
  grind [gamma1, pow_add]

end

end DownStep

end Chazelle.Core
