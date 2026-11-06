module

public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexDotPairing
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization

public section

@[expose] section

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K : Type*} [CommSemiring K]

def pairingTriple (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K ((B × A) × Unit) ((B × Unit) × C) ((Unit × A) × C) :=
  product (product (dotPairing B) (cyclic (dotPairing A)))
    (cyclic (cyclic (dotPairing C)))

def pairingTripleMatrixX (A B : Type*) : (A × B) ≃ ((B × A) × Unit) where
  toFun x := ((x.2, x.1), ())
  invFun x := (x.1.2, x.1.1)
  left_inv x := rfl
  right_inv := by rintro ⟨⟨b, a⟩, ⟨⟩⟩; rfl

def pairingTripleMatrixY (B C : Type*) : (B × C) ≃ ((B × Unit) × C) where
  toFun y := ((y.1, ()), y.2)
  invFun y := (y.1.1, y.2)
  left_inv y := rfl
  right_inv := by rintro ⟨⟨b, ⟨⟩⟩, c⟩; rfl

def pairingTripleMatrixZ (C A : Type*) : (C × A) ≃ ((Unit × A) × C) where
  toFun z := (((), z.2), z.1)
  invFun z := (z.2, z.1.2)
  left_inv z := rfl
  right_inv := by rintro ⟨⟨⟨⟩, a⟩, c⟩; rfl

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem pairingTriple_matrixCoefficients :
    pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
      (pairingTripleMatrixZ C A) (pairingTriple (K := K) A B C) =
      matrixCoefficients A B C := by
  funext x y z
  change ((if x.2 = y.1 then (1 : K) else 0) *
    (if z.2 = x.1 then 1 else 0)) * (if y.2 = z.1 then 1 else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  have hguard : ((x.2 = y.1 ∧ z.2 = x.1) ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
  simp only [ite_zero_mul_ite_zero, one_mul, hguard]

end Tensor
end MatrixMultiplication.Foundation

end OAI
