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

section

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    {X α : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]

open DistanceCalculus

private theorem bipartiteDefect_eq_placedDefect {p q : Placement}
    (ψ : EuclideanSpace ℂ (S.ExpandedLocalSpace p.side × S.ExpandedLocalSpace q.side))
    (hform : ∀ A B, stateQForm ψ (heteroKron A B) =
      S.placedCorrelation p q A B)
    (μ : Distribution X) (A : X → Measurement α (S.ExpandedLocalSpace p.side))
    (B : X → Measurement α (S.ExpandedLocalSpace q.side)) :
    bipartiteDefect μ A B ψ = S.placedDefect p q μ A B := by
  simp only [bipartiteDefect, placedDefect, measurementDefect, consistencyDefect,
    placed_product_stateQForm_eq, placedMeasurement_effect, hform]

variable (μ : Distribution X) (A : X → Measurement α (S.ExpandedLocalSpace .alice))
    (B : X → Measurement α (S.ExpandedLocalSpace .bob))

/-- The pair-state defect transported to the first opposite register pair. -/
theorem consistencyDefect_pairState_eq_AA'_BA'' :
    bipartiteDefect μ A B (ExtendedLineGame.pairState S) = S.placedDefect .AA' .BA'' μ A B :=
  S.bipartiteDefect_eq_placedDefect (p := .AA') (q := .BA'') _
    (ExtendedLineGame.stateQForm_pairState_eq_AA'_BA'' S) μ A B

/-- The same defect transported to the second pair, with Bob first. -/
theorem consistencyDefect_pairState_eq_BB'_AB'' :
    bipartiteDefect μ A B (ExtendedLineGame.pairState S) = S.placedDefect .BB' .AB'' μ B A :=
  (S.bipartiteDefect_eq_placedDefect (p := .AB'') (q := .BB') _
    (ExtendedLineGame.stateQForm_pairState_eq_AB''_BB' S) μ A B).trans
      (S.placedDefect_symm .AB'' .BB' μ A B)

end

end ProjectiveSetting

end

end MIPStarRE.QPBT
