module

public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexGroupTensor
public import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexModularSeparation

public section

@[expose] section

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

section Separation

variable {X Y Z S U G : Type*}
variable [AddCommGroup G] [Fintype G] [DecidableEq G]
variable [DecidableEq S] [DecidableEq U]

def separatedTensor (lx : X → S) (T : Tensor ℂ X Y Z) :
    Tensor ℂ (X × U) (Y × U) (Z × S) :=
  fun x y z => if lx x.1 = z.2 ∧ x.2 = y.2 then T x.1 y.1 z.1 else 0

end Separation

section FiniteGrid

variable {X Y Z S : Type*} [Fintype S] [DecidableEq S]

end FiniteGrid
end MatrixMultiplication.Foundation

end OAI
