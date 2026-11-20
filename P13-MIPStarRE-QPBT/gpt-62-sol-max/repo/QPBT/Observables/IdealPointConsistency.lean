module

public import QPBT.Observables.ExpandedDefs
public import QPBT.Games.EPR

/-!
# Perfect consistency of ideal point measurements

The ideal point projectors on the two halves of one EPR state have zero joint
weight for distinct outcomes. This follows from the reality and orthogonality
of the characteristic-two Pauli basis projectors, with no strategy hypothesis.

The transpose identities are supplied by `pauliProj_transpose` in
`Algebra.Pauli` and `ProjectiveSetting.tauPointProj_transpose` in
`Observables.ExpandedDefs`. Orthogonality of the Pauli eigenspace projectors and
of the point fibers is likewise reused from `pauliProj_mul_pauliProj` and
`ProjectiveSetting.tauPointProj_mul_tauPointProj` in those two modules. The
latter module also supplies the actual measurement
`ProjectiveSetting.tauPointMeas`, whose effects are `tauPointProj`.

## References

- `references/qpbt-paper/04_preliminaries.tex:1101-1161`: Pauli eigenbases.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
  `eq:def-psihat`, `eq:qld-point-obs-def`, and the proof of `lem:qld-comm-cons`
  at line 489: perfect consistency of the ancillary point projectors.

These are auxiliary identities for the expanded-state construction, not the
approximate consistency theorem for the original strategy.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

open MIPStarRE.LDT hiding Measurement
open DistanceCalculus

variable {P : AdmissibleParams}

section

variable (W : PauliKind)
    (u : PauliPoint P) {a b : PauliScalar P} (hab : a ≠ b)
include W u a b hab

/-- Two distinct ideal point outcomes annihilate the actual EPR vector.
Move the second effect to the first half and use orthogonality of point fibers. -/
theorem tauPointProj_epr_mulVec_eq_zero_of_ne :
    (heteroKron (tauPointProj W u a) (tauPointProj W u b)).mulVec
      (eprState (PauliRegister P)) = 0 := by
  exact heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero _ _ (tauPointProj_transpose W u b)
    (by rw [tauPointProj_mul_tauPointProj, if_neg hab])

/-- Every off-diagonal joint weight of the ideal point measurement on one EPR
pair is zero. The Pauli basis and the point are arbitrary. -/
theorem tauPointProj_epr_joint_eq_zero_of_ne :
    stateQForm (eprState (PauliRegister P))
      (heteroKron (tauPointProj W u a) (tauPointProj W u b)) = 0 := by
  unfold stateQForm applyOperatorToState
  change (inner ℂ (eprState (PauliRegister P))
    ((EuclideanSpace.equiv _ ℂ).symm
      ((heteroKron (tauPointProj W u a) (tauPointProj W u b)).mulVec
        (eprState (PauliRegister P))))).re = 0
  rw [tauPointProj_epr_mulVec_eq_zero_of_ne W u hab, map_zero, inner_zero_right]
  rfl

end

end ProjectiveSetting

end

end MIPStarRE.QPBT
