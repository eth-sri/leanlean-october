module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Semiring
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.BinaryCharacter
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.DirectSumClass

public section
@[expose] section
namespace OAI.MatrixMultiplication.AuxiliarySeparation.Character

noncomputable section
open MatrixMultiplication.Foundation
open scoped BigOperators
open TensorSemiring

variable {K : Type*} [CommSemiring K] [Nontrivial K]

/-- A monotone semiring homomorphism on tensor classes gives a character. -/
def ofTensorClassHom (φ : (TensorClass K) →+* ℝ) (hφ : Monotone φ) : (Character K) where
  value := fun T => φ (classOf T)
  nonneg := by
    intro X Y Z hX hY hZ T
    simpa only [φ.map_zero] using hφ (TensorSemiring.zero_le (classOf T))
  map_zero := by
    intro X Y Z hX hY hZ
    rw [classOf_zero]
    exact φ.map_zero
  map_one := φ.map_one
  map_directSum := by
    intro ι X Y Z hι dι hX hY hZ T
    rw [classOf_directSum, map_sum]
  map_product := by
    intro X Y Z U V W hX hY hZ hU hV hW T S
    rw [classOf_product, map_mul]
  monotone := by
    intro X Y Z X' Y' Z' hX hY hZ hX' hY' hZ' T A B C
    exact hφ ((classOf_le_iff _ _).mpr ⟨A, B, C, rfl⟩)

end
end OAI.MatrixMultiplication.AuxiliarySeparation.Character
