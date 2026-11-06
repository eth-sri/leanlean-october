module

public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

public section

@[expose] section

namespace OAI

noncomputable section

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {F X Y Z X' Y' Z' : Type*} [CommRing F]
variable [Fintype X] [Fintype Y] [Fintype Z]

structure PolynomialRestrictionDegeneration
    (T : Tensor F X Y Z) (U : Tensor F X' Y' Z') (k Lx Ly Lz : ℕ) where
  leftMap : X' → X → Polynomial F
  middleMap : Y' → Y → Polynomial F
  rightMap : Z' → Z → Polynomial F
  left_degree : ∀ x' x, (leftMap x' x).degree ≤ Lx
  middle_degree : ∀ y' y, (middleMap y' y).degree ≤ Ly
  right_degree : ∀ z' z, (rightMap z' z).degree ≤ Lz
  vanishes : ∀ x' y' z' j, j < k →
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff j = 0
  leading : ∀ x' y' z',
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff k = U x' y' z'

namespace PolynomialRestrictionDegeneration

variable {T : Tensor F X Y Z} {U : Tensor F X' Y' Z'} {k Lx Ly Lz : ℕ}

def basePolynomial (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap (fun x y z => Polynomial.C (T x y z))

end PolynomialRestrictionDegeneration
end Tensor
end MatrixMultiplication.Foundation
end
end OAI
