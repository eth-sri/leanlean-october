module

public import QPBT.Algebra.Pauli
public import QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-!
# The ideal target of the Magic Square rigidity theorem

The conclusion of `thm:ms-rigidity` compares the two players' bit measurements
with the Pauli basis projectors on a two-qubit register and their shared state
with two EPR pairs tensored with an auxiliary bipartite state.  This file
records the two elementary properties of that target which the estimates of the
rigidity assembly use: the Pauli basis projectors of one kind form a complete
projective measurement, so that any marginal of them is a positive contraction,
and the ideal state is a unit vector whenever the auxiliary state is.

The completeness of the Pauli basis follows from the Fourier expansion
`tauObservable_eq_sum_pauliProj` evaluated at the zero label, where the
generalized Pauli observable is the identity.  Positivity is the rank-one
factorization `pauliProj W e = v vᴴ` for the normalized Pauli eigenvector `v`.

## References

`def:generalized-pauli` and blueprint
`lem:pauli-observable-expansion`, paper
`references/qpbt-paper/04_preliminaries.tex:908-1161`; the target of the
rigidity theorem is blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]
/-! ## Marginals of the Pauli basis -/











/-! ## The ideal state is normalized -/

/-- The ideal state of `thm:ms-rigidity`, a maximally entangled state on the
extracted registers tensored with an auxiliary bipartite state and shuffled into
local player order, has the norm of the auxiliary state.  In particular it is a
unit vector whenever the auxiliary state is.  The norm identities for the
coordinate operations are `reindexState_norm_eq` and `vecTensor_norm_eq` in
`MIPStarRE/QPBT/State.lean`.  Blueprint `thm:ms-rigidity`. -/
theorem norm_reindexState_prodShuffle_vecTensor_eprState {V ιA'' ιB'' : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype ιA''] [DecidableEq ιA'']
    [Fintype ιB''] [DecidableEq ιB''] (aux : MIPStarRE.QPBT.StateVector (ιA'' × ιB'')) :
    ‖reindexState prodShuffle (vecTensor (eprState V) aux)‖ = ‖aux‖ := by
  rw [reindexState_norm_eq, vecTensor_norm_eq, eprState_norm, one_mul]

end

end MIPStarRE.QPBT
