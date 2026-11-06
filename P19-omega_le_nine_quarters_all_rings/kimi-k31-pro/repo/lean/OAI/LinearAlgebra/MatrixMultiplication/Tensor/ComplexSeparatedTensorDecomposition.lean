module

public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexDotPairing

public section

@[expose] section

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section DependentSum

variable {K S : Type*} [CommSemiring K] [DecidableEq S]
variable {X Y Z : S → Type*}

def dependentDirectSum (T : ∀ s, Tensor K (X s) (Y s) (Z s)) :
    Tensor K (Σ s, X s) (Σ s, Y s) (Σ s, Z s) :=
  fun x y z =>
    if hxy : y.1 = x.1 then
      if hxz : z.1 = x.1 then T x.1 x.2 (hxy ▸ y.2) (hxz ▸ z.2)
      else 0
    else 0

@[simp] theorem dependentDirectSum_matching
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (s : S) (x : X s) (y : Y s) (z : Z s) :
    dependentDirectSum T ⟨s, x⟩ ⟨s, y⟩ ⟨s, z⟩ = T s x y z := by
  simp [dependentDirectSum]

end DependentSum
end Tensor

end MatrixMultiplication.Foundation

end OAI
