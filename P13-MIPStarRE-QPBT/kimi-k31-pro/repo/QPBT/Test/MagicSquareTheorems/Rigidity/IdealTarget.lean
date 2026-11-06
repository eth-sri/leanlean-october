module

public import QPBT.Algebra.Pauli
public import QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

noncomputable section

theorem norm_reindexState_prodShuffle_vecTensor_eprState {V ιA'' ιB'' : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype ιA''] [DecidableEq ιA'']
    [Fintype ιB''] [DecidableEq ιB''] (aux : EuclideanSpace ℂ (ιA'' × ιB'')) :
    ‖reindexState prodShuffle (vecTensor (eprState V) aux)‖ = ‖aux‖ := by
  rw [reindexState_norm_eq, vecTensor_norm_eq, eprState_norm, one_mul]

end

end MIPStarRE.QPBT
