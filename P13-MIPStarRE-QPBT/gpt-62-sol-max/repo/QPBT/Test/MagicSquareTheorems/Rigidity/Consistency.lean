module

public import QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
public import QPBT.Test.MagicSquareTheorems.Rigidity.CellRelations

/-!
# Cross-player agreement of the Magic Square variable measurements

The rigidity theorem `thm:ms-rigidity` is false for arbitrary strategies of the
role-symmetric Magic Square game: its conclusion forces the two players'
`Variable_1` and `Variable_5` measurements to agree on the shared state, and the
game never tests that agreement.  The corrected statement adopted on issue
Dengnifer/MIPStarRE-QPBT-bak#172
(owner decision B5 on issue Dengnifer/MIPStarRE-QPBT-bak#26; the note is
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`) assumes that
agreement, quantitatively.  The *variable-measurement agreement distance* at a
variable is the summed squared state-dependent distance between Alice's and
Bob's binary variable effects on the shared state, in the `≈_δ` convention of
`def:povm-distance`, and the corrected theorem bounds it at the paper's first
and fifth variables.

That distance is not the consistency defect of `def:consistency`, which is the
off-diagonal outcome weight of a pair of measurements (`consistencyDefect`); it
is the squared state-dependent distance `opFamilyDistSq` of
`def:povm-distance`.  In the declaration name `msVariableConsistencyDefect` the
word `Consistency` records the failure of the two players' variable
measurements to be consistent with one another, which is what the distance
measures, and not the defect of `def:consistency`; the blueprint states the
distinction as `rem:ms-variable-agreement-name`.  The name itself is kept
unchanged because the rigidity assembly of issue Dengnifer/MIPStarRE-QPBT-bak#105 is stated in terms
of it.

This file defines that distance on the original, possibly non-projective,
strategy and relates it to the reflections of the projective dilation on which
the self-testing argument operates.

* For a symmetric strategy whose variable measurements are consistent in the
  exact sense of `def:consistent-measurement`, the distance vanishes, so the
  corrected theorem specializes to the symmetric consistent strategies named in
  the owner decision.
* The two players' dilated variable reflections `msVarObsA S j` and
  `msVarObsB S j` are close on the dilated state whenever that distance is
  small.
  The loss is the leakage of the dilated observables out of the ground slice,
  which `Rigidity/Transfer.lean` controls by the cell-consistency masses of a
  strategy of value `1 - ε`.  This is the cross-player input that the
  swap-isometry extraction of issue Dengnifer/MIPStarRE-QPBT-bak#105 needs in order to compare the
  two
  players' extracted qubits.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
The consistency notions are `def:consistent-measurement` and `def:povm-distance`,
paper `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:144-174` and
`258-271`.  The variable indices are zero-based, so the paper's first and fifth
variables are the cells `0` and `4`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open MIPStarRE.QPBT.MagicSquareRigidity

noncomputable section

/-! ## The agreement distance of a variable measurement -/

/-! ## Exact consistency -/

/-- Formalization-only: the action on a state is additive over finite sums of
operators.  This is the `Finset` form of
`MagicSquareRigidity.applyOperatorToState_sum`, which sums over a `Fintype`;
the general form is the one `Measurement.postprocess_effect` needs, a
postprocessed effect being a sum over a fibre.  The two are kept apart because
the rigidity assembly of issue Dengnifer/MIPStarRE-QPBT-bak#105 already refers to this name; their
consolidation is issue Dengnifer/MIPStarRE-QPBT-bak#204. -/
theorem applyOperatorToState_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset β) (M : β → Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (∑ b ∈ s, M b) ψ = ∑ b ∈ s, applyOperatorToState (M b) ψ := by
  unfold applyOperatorToState
  simp only [map_sum, LinearMap.sum_apply]

end

/-! ## Transfer to the dilated reflections -/

namespace MagicSquareRigidity

noncomputable section

end

end MagicSquareRigidity

end MIPStarRE.QPBT
