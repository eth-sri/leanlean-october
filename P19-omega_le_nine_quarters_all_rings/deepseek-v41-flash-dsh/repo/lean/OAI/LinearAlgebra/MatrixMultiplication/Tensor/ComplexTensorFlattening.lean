module

public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

@[expose] section

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/


open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z : Type*} [CommSemiring K] [Nontrivial K]

theorem RankAtMost.card_le_of_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (hT : RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) K := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι K := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι K) := by
    funext i j
    change (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = if i = j then 1 else 0
    calc
      (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = T (x i) (y i) (z j) :=
        (congrFun (congrFun (congrFun heq (x i)) (y i)) (z j)).symm
      _ = _ := hidentity i j
  have hinj : Function.Injective R.mulVecLin := by
    intro v w hvw
    have heq := congrArg L.mulVecLin hvw
    simpa only [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul,
      hmul, Matrix.mulVecLin_one, LinearMap.id_apply] using heq
  simpa using card_le_of_injective K R.mulVecLin hinj

end Tensor
end MatrixMultiplication.Foundation


end OAI
