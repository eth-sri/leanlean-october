module

public import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexSeparationAsymptotics
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexSeparatedTensorDecomposition

public section

@[expose] section

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

instance auxiliarySeparation_modulus_neZero (K : ℕ) :
    NeZero (4 * Separation.gridWidth K) :=
  ⟨Nat.mul_ne_zero (by decide)
    (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2)
      (Separation.gridWidth_ge_two K)))⟩

section AuxiliarySeparation

variable {X Y Z S : Type*} [Fintype S] [DecidableEq S]

end AuxiliarySeparation

end MatrixMultiplication.Foundation

end OAI
