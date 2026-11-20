module

public import QPBT.Combining.ExtendedLineGame.StateTransport

/-!
# Pair-state consistency transport

This module transports consistency defects on the two-player expanded state to
the corresponding opposite placements on the six-register expanded state.

## References

These formalization-only identities support the application of `lem:pasting`
in `lem:qld-xz-lines`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963` and
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open scoped MatrixOrder ComplexOrder

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) {Sample Outcome : Type*}
  [Fintype Sample] [DecidableEq Sample] [Fintype Outcome] [DecidableEq Outcome]
  (law : Distribution Sample) (first : Sample → Measurement Outcome (S.ExpandedLocalSpace .alice))
  (second : Sample → Measurement Outcome (S.ExpandedLocalSpace .bob))

/-- A consistency defect on the two-player expanded state equals the defect
of the same measurements placed on `AA'` and `BA''` in the six-register state. -/
theorem consistencyDefect_pairState_eq_AA'_BA'' :
    bipartiteDefect law
        first
        second
        (ExtendedLineGame.pairState S) =
      consistencyDefect law
        (fun sample answer => S.place .AA' ((first sample).effect answer))
        (fun sample answer => S.place .BA'' ((second sample).effect answer))
        S.psiHat := by
  classical
  simp [bipartiteDefect]
  apply avgOver_congr
  intro sample
  congr 1 with firstAnswer
  congr 1 with secondAnswer
  by_cases hanswer : firstAnswer = secondAnswer
  · simp [hanswer]
  · simp_all
    simp [heteroKron_mul]
    exact ExtendedLineGame.stateQForm_pairState_eq_AA'_BA'' S _ _
      (measurement_effect_hermitian (first sample) firstAnswer)
      (measurement_effect_hermitian (second sample) secondAnswer)

/-- A consistency defect on the two-player expanded state equals the defect
of the same measurements placed on `AB''` and `BB'` in the six-register state. -/
theorem consistencyDefect_pairState_eq_AB''_BB' :
    bipartiteDefect law
        first
        second
        (ExtendedLineGame.pairState S) =
      consistencyDefect law
        (fun sample answer => S.place .AB'' ((first sample).effect answer))
        (fun sample answer => S.place .BB' ((second sample).effect answer))
        S.psiHat := by
  classical
  simp [bipartiteDefect]
  apply avgOver_congr
  intro sample
  congr 1 with firstAnswer
  congr 1 with secondAnswer
  by_cases hanswer : firstAnswer = secondAnswer
  · simp [hanswer]
  · simp_all
    simp [heteroKron_mul]
    exact ExtendedLineGame.stateQForm_pairState_eq_AB''_BB'
      (measurement_effect_hermitian (first sample) firstAnswer)
      (measurement_effect_hermitian (second sample) secondAnswer)

end ProjectiveSetting

end

end MIPStarRE.QPBT
