module

public import QPBT.Combining.ExtendedLineGame.EvaluatedLineComparison

/-! Failed completed line evaluations can be charged to mixed line/point rejection. -/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

local notation "D" => P.extendedDirectLd
local notation "Sample" => DirectLdSpace D

/-- The marginal event weight for a given side of the extended strategy. -/
abbrev sideEventWeight (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (q : DirectLdQuestion D) (e : DirectLdAnswer D → Prop) [DecidablePred e] : ℝ :=
  match side with
  | .alice => aliceEventWeight (strategy lines) q e
  | .bob => bobEventWeight (strategy lines) q e

section

variable (lines : ExtendedLinesWitness setting points deltaL)
    (kind : LineKind)

/-- The average marginal mass of the `none` answer on the line questions. -/
def lineNoneMass (side : PlayerSide) : ℝ :=
  avgOver (uniformDistribution Sample) fun s =>
    sideEventWeight lines side (sampleQuestion (lineTag kind) s)
      (fun a => lineGameRead kind s a = none)

private theorem pointGameRead_ne_none {a : DirectLdAnswer D}
    (ha : validDirectLdAnswer .point a = true) : pointGameRead a ≠ none := by
  cases a <;> simp_all [pointGameRead, validDirectLdAnswer]

/-- Alice's failed line read causes rejection against a valid point read. -/
theorem alice_line_none_mass_le_rejection :
    lineNoneMass lines kind .alice ≤ branchRejection lines (lineTag kind) .point := by
  rw [branchRejection, directLdBranchRejectionProbability_eq_avgOver, lineNoneMass]
  refine avgOver_mono _ _ _ fun s => ?_
  dsimp only [sideEventWeight, Prod.fst, Prod.snd]
  rw [← outcome_event_weight_left_eq _ _ (sampleQuestion .point s),
    line_point_rejectedMass_eq_read_mismatch lines kind s]
  exact outcomeEventWeight_mono_valid lines _ _ _ _ fun _ _ _ hb hn he =>
    pointGameRead_ne_none hb (he.symm.trans hn)

/-- Bob's failed line read causes rejection against a valid point read. -/
theorem bob_line_none_mass_le_rejection :
    lineNoneMass lines kind .bob ≤ branchRejection lines .point (lineTag kind) := by
  rw [branchRejection, directLdBranchRejectionProbability_eq_avgOver, lineNoneMass]
  refine avgOver_mono _ _ _ fun s => ?_
  dsimp only [sideEventWeight, Prod.fst, Prod.snd]
  rw [← outcome_event_weight_right_eq _ (sampleQuestion .point s),
    point_line_rejectedMass_eq_read_mismatch lines kind s]
  exact outcomeEventWeight_mono_valid lines _ _ _ _ fun _ _ ha _ hn he =>
    pointGameRead_ne_none ha (he.trans hn)

end

end ExtendedLineGame

end

end MIPStarRE.QPBT
