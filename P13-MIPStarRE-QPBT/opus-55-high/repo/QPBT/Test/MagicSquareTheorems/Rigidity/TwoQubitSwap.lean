module

public import QPBT.Test.MagicSquareTheorems.Rigidity.Swap

/-!
# The two-qubit controlled-swap isometry

The conclusion of `thm:ms-rigidity` places each player's extracted register on
two qubits, indexed by `Fin 2 → ZMod 2`: the first carries the logical pair at
the cells `0` and `4`, the second the logical pair at the cells `1` and `3`.
`Rigidity/Swap.lean` builds the controlled-swap embedding attached to a single
anticommuting pair.  This file composes two of them.

For two pairs of binary observables `(X₁, Z₁)` and `(X₂, Z₂)` on one local
space, the map defined here sends a vector `ψ` to the family

    (e, i) ↦ (X₂^{e(1)} P^{Z₂}_{e(1)} X₁^{e(0)} P^{Z₁}_{e(0)} ψ) (i),

where `P^{Z}_b` is the spectral effect `reflectionEffect Z b`.  It is the
composition of the controlled swap of the first pair with the controlled swap
of the second pair applied to the residual copy of the local space, so it is an
*exact* isometry with no commutation assumption on the two pairs; approximate
commutation of the two pairs enters only when the second pair's observables are
transported through the first swap, which is not part of this file.

The first pair is applied innermost and is indexed by the register coordinate
`0`, matching `idealMagicBitProj`, whose marginal is taken over the coordinate
`0` of the label.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the cited robust self-test is Coladangelo--Stark, arXiv:1709.09267v2,
Theorem 6.9, `references/cs-paper/self-testing.tex:660-730`.  The one-qubit
construction is `binarySwapIsometry` in `Rigidity/Swap.lean`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Sums over a two-qubit label -/




/-! ## The two-qubit controlled-swap map -/






/-! ## Magic Square specialization -/

end

end MIPStarRE.QPBT.MagicSquareRigidity
