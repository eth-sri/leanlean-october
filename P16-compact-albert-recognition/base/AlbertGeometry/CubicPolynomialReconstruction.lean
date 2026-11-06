/-
The reverse polynomial producer uses every
ordered triple of actual Euclidean coordinate basis vectors. Homogeneity and
evaluation equality are proved from finite sums and actual linearity. No
coefficient/evaluation conclusion or representation roundtrip is assumed.
-/
module

public import AlbertGeometry.CubicPolynomialRepresentation
public import AlbertGeometry.CubicPolarizationUniqueness

@[expose] public section

namespace AlbertGeometry.CubicPolynomialReconstruction
noncomputable section
open scoped BigOperators
open AlbertGeometry.Cubic AlbertGeometry.CubicPolynomialRepresentation

/-- The existing actual Euclidean coordinate basis vector. -/
def coordinateVector (i : Fin 27) : Coordinates := EuclideanSpace.basisFun (Fin 27) ℝ i

theorem coordinate_sum (x : Coordinates) :
    ∑ i : Fin 27, x i • coordinateVector i = x := by
  simpa only [coordinateVector, EuclideanSpace.basisFun_repr] using
    (EuclideanSpace.basisFun (Fin 27) ℝ).sum_repr x

end
end AlbertGeometry.CubicPolynomialReconstruction
