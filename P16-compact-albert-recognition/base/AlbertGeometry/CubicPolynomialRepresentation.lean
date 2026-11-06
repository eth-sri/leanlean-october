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
open scoped BigOperators
open AlbertGeometry.Cubic

abbrev Coordinates := EuclideanSpace ℝ (Fin 27)

/-- A genuine continuous coordinate product in three separately linear inputs. -/
def coordinateProduct (i j k : Fin 27) : TrilinearForm Coordinates :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 3) ℝ).compContinuousLinearMap
    ![EuclideanSpace.proj i, EuclideanSpace.proj j, EuclideanSpace.proj k]

theorem coordinateProduct_apply (i j k : Fin 27) (m : Fin 3 → Coordinates) :
    coordinateProduct i j k m = m 0 i * m 1 j * m 2 k := by
  simp [coordinateProduct, Fin.prod_univ_three, mul_assoc]

/-- The six slot permutations are averaged with literal coefficient1/6.
Repeated coordinate indices remain six terms; no orbit-size division is used. -/
def symmetricCoordinateForm (i j k : Fin 27) : TrilinearForm Coordinates :=
  (1 / 6 : ℝ) • (coordinateProduct i j k + coordinateProduct i k j +
    coordinateProduct j i k + coordinateProduct j k i +
    coordinateProduct k i j + coordinateProduct k j i)

theorem symmetricCoordinateForm_apply (i j k : Fin 27) (x y z : Coordinates) :
    symmetricCoordinateForm i j k ![x,y,z] = (1 / 6 : ℝ) *
      (x i * y j * z k + x i * y k * z j +
       x j * y i * z k + x j * y k * z i +
       x k * y i * z j + x k * y j * z i) := by
  simp [symmetricCoordinateForm, coordinateProduct_apply, smul_eq_mul]
  ring

theorem symmetricCoordinateForm_swap12 (i j k : Fin 27) (x y z : Coordinates) :
    symmetricCoordinateForm i j k ![x,y,z] =
      symmetricCoordinateForm i j k ![y,x,z] := by
  rw [symmetricCoordinateForm_apply, symmetricCoordinateForm_apply]
  ring

theorem symmetricCoordinateForm_swap23 (i j k : Fin 27) (x y z : Coordinates) :
    symmetricCoordinateForm i j k ![x,y,z] =
      symmetricCoordinateForm i j k ![x,z,y] := by
  rw [symmetricCoordinateForm_apply, symmetricCoordinateForm_apply]
  ring

theorem symmetricCoordinateForm_diagonal (i j k : Fin 27) (x : Coordinates) :
    symmetricCoordinateForm i j k (fun _ : Fin 3 => x) = x i * x j * x k := by
  have hv : (fun _ : Fin 3 => x) = ![x,x,x] := by
    ext t
    fin_cases t <;> rfl
  rw [hv, symmetricCoordinateForm_apply]
  ring

end
end AlbertGeometry.CubicPolynomialRepresentation
