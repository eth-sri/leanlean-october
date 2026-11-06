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

namespace ExtendedLineGame

variable {P : AdmissibleParams} {ε : ℝ}

/-- Transport arbitrary POVM consistency on the two-player expanded state to
both heterogeneous expanded placements. -/
theorem placed_consistency_pairState
    (S : ProjectiveSetting P ε) {X α : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (μ : Distribution X) (A : X → Measurement α (S.ExpandedLocalSpace .alice))
    (B : X → Measurement α (S.ExpandedLocalSpace .bob)) :
    (consistencyDefect μ (fun x a => S.place .AA' ((A x).effect a))
      (fun x a => S.place .BA'' ((B x).effect a)) S.psiHat =
      consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) (pairState S)) ∧
    (consistencyDefect μ (fun x a => S.place .BB' ((B x).effect a))
      (fun x a => S.place .AB'' ((A x).effect a)) S.psiHat =
      consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) (pairState S)) := by
  have hA (x : X) (a : α) := (Matrix.nonneg_iff_posSemidef.mp ((A x).pos a)).isHermitian
  have hB (x : X) (a : α) := (Matrix.nonneg_iff_posSemidef.mp ((B x).pos a)).isHermitian
  constructor <;> refine avgOver_congr _ _ _ fun x => ?_
  on_goal 2 => rw [Finset.sum_comm]
  all_goals refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  all_goals by_cases hab : a = b
  all_goals try (subst hab; simp)
  all_goals simp only [hab, Ne.symm hab, ite_false,
    DistanceCalculus.consistency_term_eq_stateQForm,
    DistanceCalculus.placed_product_stateQForm_eq]
  · exact (stateQForm_pairState_eq_AA'_BA'' S _ _ (hA x a) (hB x b)).symm
  · rw [S.place_comm .BB' .AB'' trivial]
    exact (stateQForm_pairState_eq_AB''_BB' S _ _ (hA x a) (hB x b)).symm

end ExtendedLineGame

end

end MIPStarRE.QPBT
