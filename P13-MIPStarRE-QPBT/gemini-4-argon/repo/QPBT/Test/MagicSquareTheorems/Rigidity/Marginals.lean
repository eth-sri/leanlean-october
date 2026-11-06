module

public import QPBT.Test.MagicSquareTheorems.Rigidity.Assembly

/-!
# Transporting the first logical pair through the two-qubit controlled swap

The bit-measurement conclusions of `thm:ms-rigidity` compare each player's
variable-0 and variable-4 measurements, conjugated by the two-qubit
controlled-swap embedding, with the marginals of the two-qubit Pauli basis over
the first register coordinate.  `Rigidity/TwoQubitIntertwine.lean` identifies
those marginals with the spectral effects of the two-qubit Pauli observables.
This file carries the one-qubit intertwining relations of `Rigidity/Swap.lean`
through the *second* controlled swap, which is the remaining step.

The transport is expressed at the level of the matrix of the embedding.  The
phase observable is transported exactly, because the residual factors of the
first swap absorb their controlling observable with the sign of the register
label and the residual factors of the second swap are untouched.  For the shift
observable the transport defect `D` satisfies the exact identity
`Dᴴ D = (1/2) · GᴴG`, where `G` is the anticommutator of the first pair: the
residual factors of the second swap form a complete family and therefore drop
out of `Dᴴ D`, leaving the one-qubit computation of `Rigidity/Swap.lean`.  The
spectral effects of the two observables inherit these estimates with a further
factor `1/4`, and tensoring with the other player's embedding preserves them
because that embedding is an isometry.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the cited robust self-test is Coladangelo--Stark, arXiv:1709.09267v2,
Theorem 6.9, `references/cs-paper/self-testing.tex:660-730`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Matrix products with a register operator placed on the left -/

/-! ## Block decomposition of a Gram matrix -/

/-! ## The matrix of the two-qubit controlled swap -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The shift transport defect -/

/-! ## The spectral effects of the transported observables -/

/-! ## Transport on the joint state -/

variable {ιA ιB κA κB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]

/-! ## Magic Square specialization -/

/-- The spectral effects of a left-placed reflection are the placed spectral
effects. -/
theorem reflectionEffect_heteroKron_left (Z : Op ιA) (b : ZMod 2) :
    heteroKron (reflectionEffect Z b) (1 : Op ιB) =
      reflectionEffect (heteroKron Z (1 : Op ιB)) b := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [reflectionEffect, if_pos]
    rw [heteroKron_smul_left, heteroKron_add_left, heteroKron_one_one]
  · simp only [reflectionEffect, if_neg one_ne_zero]
    rw [heteroKron_smul_left, heteroKron_sub_left, heteroKron_one_one]

end

end MIPStarRE.QPBT.MagicSquareRigidity
