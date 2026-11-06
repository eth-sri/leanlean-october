/-
Every derivative is the actual Frechet
or scalar derivative of the coordinate Newton function. Affine-line identities
from native algebra are differentiated using real derivative rules and
uniqueness; they are not derivative fields or named coefficient definitions.
No normed native Albert instance or unknown/native equivalence is introduced.
-/
module
public import AlbertGeometry.BasedNormDerivativeTransport
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop

public import AlbertGeometry.NativeEuclideanNormBinding
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section
namespace AlbertGeometry.NativeCoordinateDerivatives
noncomputable section
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open Glennie AlbertGeometry.Cubic AlbertGeometry.CubicPolynomialRepresentation
open AlbertGeometry.NativeEuclideanNormBinding AlbertGeometry.BasedNormDerivativeTransport

theorem native_normTrace (x : Coordinates) :
    normTrace nativeEuclideanRepresentation nativeCoordinateUnit x = trace (delta x) := by
  rw [normTrace, fderiv_diagonalCubic_apply_symmetric]
  change 3 * rawNewtonPolarization (delta nativeCoordinateUnit)
    (delta nativeCoordinateUnit) (delta x) = _
  simp only [delta_nativeCoordinateUnit, rawNewtonPolarization, trace_unit,
    jordan_unit_left, inner_unit_left, inner_unit_right]
  ring

theorem native_rawTraceForm (x y : Coordinates) :
    rawTraceForm nativeEuclideanRepresentation nativeCoordinateUnit x y =
      inner (delta x) (delta y) := by
  rw [rawTraceForm_apply, native_normTrace, native_normTrace, cubicHessian_apply]
  change trace (delta x) * trace (delta y) -
    6 * rawNewtonPolarization (delta nativeCoordinateUnit) (delta x) (delta y) = _
  simp only [delta_nativeCoordinateUnit, rawNewtonPolarization, trace_unit,
    ← inner_jordan_associative, jordan_unit_left, inner_unit_left ]
  ring

end
end AlbertGeometry.NativeCoordinateDerivatives
