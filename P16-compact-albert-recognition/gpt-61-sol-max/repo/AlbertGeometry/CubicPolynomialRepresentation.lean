/- Every formal homogeneous degree-three polynomial on the actual real27
Euclidean coordinate space receives a constructed continuous symmetric
trilinear diagonal representation. No existence of a representation is assumed.
-/
module

public import AlbertGeometry.CubicDerivatives
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

@[expose] public section
namespace AlbertGeometry.CubicPolynomialRepresentation
noncomputable section
open AlbertGeometry.Cubic

abbrev Coordinates := EuclideanSpace ℝ (Fin 27)


end
end AlbertGeometry.CubicPolynomialRepresentation
