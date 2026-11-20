module

public import QPBT.Combining.ExtendedLineGame.EvaluatedLineComparison

/-!
# Failed completed line-evaluation mass

This module bounds the marginal Born mass of the `none` outcome of each
completed line read by the corresponding mixed line/point rejection branch.
Wrong-format point answers also read as `none`, so the proof first removes
those answer pairs using their zero Born weight and only then applies event
inclusion.

These statements concern completed `Option`-valued readouts. They do not
identify successful parameter evaluation or prove a coefficient-collision
bound.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#332.
-/

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

variable (lines : ExtendedLinesWitness setting points deltaL) (k : LineKind)

/-- A failed completed line read is charged to the line/point branch: on a
valid point answer the point read cannot be `none`. -/
theorem line_none_le_rejection :
    avgOver (uniformDistribution _) (fun s => aliceEventWeight (strategy lines)
      (branchQ (lineTag k) s) (fun a => lineRead k s a = none)) ≤ rejection lines (lineTag k) .point := by
  classical
  apply avgOver_mono
  intro s
  change _ ≤ directRejectedMass _ (strategy lines) (branchQ (lineTag k) s) (branchQ .point s)
  rw [← outcome_event_weight_left_eq (strategy lines) _ (branchQ .point s),
    rejectedMass_of_readout lines _ _ _ _ (linePointLaw k s)]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases h : validDirectLdAnswer .point b = true
  · have hb : pointGameRead b ≠ none := by cases b <;> simp_all [validDirectLdAnswer, pointGameRead]
    have hw := outcomeWeight_nonneg (strategy lines) (branchQ (lineTag k) s) (branchQ .point s) a b
    split_ifs <;> grind
  · simp [outcomeWeight_eq_zero_of_invalid lines (branchQ (lineTag k) s) (branchQ .point s) a b (Or.inr (Bool.eq_false_of_not_eq_true h))]

end ExtendedLineGame
end
end MIPStarRE.QPBT
