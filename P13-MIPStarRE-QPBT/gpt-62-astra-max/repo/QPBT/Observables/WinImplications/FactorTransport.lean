module

public import QPBT.Observables.WinImplications.Interchange

/-!
# Transport of the winning implications to the interchanged tensor factor

This module carries the state-dependent functionals of the winning
implications across the interchange of the two tensor factors.  The
factor-interchanged conclusions of `lem:qld-win-implications` are stated with
the second player on the left factor and the reindexed state
`ProjectiveSetting.swappedState`; the lemmas here identify those quantities
with the ones proved on `S.toStrategy.psi`, so that the second pass of
`lem:qld-win-implications-obs` can reuse the first pass verbatim on the
interchanged side.

## References

The declarations support the trailing clause of `lem:qld-win-implications` and
the second assertion of `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:701-703`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:227,309-362`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reindexing the identity and the strategy state -/

/-! ## Transport of the consistency defect -/

/-- Left and right placements of local operators commute.  Formalization-only
support for `def:consistency`, blueprint `ch12_qpbt_games.tex:210-223`. -/
theorem heteroKron_left_right_comm {ιA ιB : Type*} [Fintype ιA]
    [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] (A : Op ιA) (B : Op ιB) :
    heteroKron A (1 : Op ιB) * heteroKron (1 : Op ιA) B =
      heteroKron (1 : Op ιA) B * heteroKron A 1 := by
  simp [heteroKron_mul]

/-! ## Transport of the phase-signed operator distance -/

/-- Reindexing an operator commutes with scalar multiplication.
Formalization-only support for the second assertion of
`lem:qld-win-implications-obs`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem reindexOp_smul {ι κ : Type*} (e : ι ≃ κ) (c : ℂ) (M : Op κ) :
    reindexOp e (c • M) = c • reindexOp e M := rfl

/-- The phase-signed operator distance of two left-placed families is
unchanged by interchanging the tensor factors of the families and the state.
This is the transport used by the second assertion of
`lem:qld-win-implications-obs`, blueprint
`ch14_qpbt_observables.tex:761-794`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`. -/
theorem opDistSq_smul_swappedState {X ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (c : X → ℂ) (M N : X → Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    opDistSq μ (fun x => heteroKron (M x) (1 : Op ιA))
        (fun x => c x • heteroKron (N x) (1 : Op ιA))
        (reindexState (Equiv.prodComm ιA ιB) ψ) =
      opDistSq μ (fun x => heteroKron (1 : Op ιA) (M x))
        (fun x => c x • heteroKron (1 : Op ιA) (N x)) ψ := by
  apply avgOver_congr
  intro x
  refine Finset.sum_congr rfl ?_
  intro _ _
  rw [norm_applyOperatorToState_reindexState]
  simp [reindexOp_sub, reindexOp_smul, reindexOp_prodComm_heteroKron]

end WinImplications

end

end MIPStarRE.QPBT
