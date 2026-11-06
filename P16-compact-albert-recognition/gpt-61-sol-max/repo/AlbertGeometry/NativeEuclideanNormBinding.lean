/-
Native polynomial representation. All normed/continuous objects
live on actual Euclidean27 coordinates; delta into native Albert is algebraic.
The continuous symmetric form is a genuine finite coordinate tensor sum and
its diagonal equality with literal native Newton is proved by bilinearity.
No native norm instance, native CLEquiv, assumed representation, trace law,
primitive predicate or recognition conclusion is introduced.
-/
module
public import Glennie.Compactness

public import Glennie.LinearSimp
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

public import Glennie.Theorems.CubicNorm
public import AlbertGeometry.CubicPolynomialRepresentation
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
namespace AlbertGeometry.NativeEuclideanNormBinding
noncomputable section
open Glennie
open AlbertGeometry.Cubic AlbertGeometry.CubicPolynomialRepresentation

open scoped BigOperators ContDiff

/-- A coordinate carrier chosen using the native dimension. -/
def delta : Coordinates ≃ₗ[ℝ] Albert :=
  LinearEquiv.ofFinrankEq _ _ (by simp [Coordinates, albert_finrank])

/-- Literal trilinear Newton polarization before supplying continuity. -/
def rawNewtonPolarization (x y z : Albert) : ℝ :=
  (Glennie.trace x * Glennie.trace y * Glennie.trace z -
    Glennie.trace x * Glennie.inner y z -
    Glennie.trace y * Glennie.inner x z -
    Glennie.trace z * Glennie.inner x y +
    2 * Glennie.inner x (jordan y z)) / 6

attribute [local fun_prop] continuous_jordan continuous_native_inner

def nativeEuclideanForm : TrilinearForm Coordinates where
  toMultilinearMap := MultilinearMap.mk'
    (fun m => rawNewtonPolarization (delta (m 0)) (delta (m 1)) (delta (m 2)))
    (by intro m i x y; fin_cases i <;> simp [rawNewtonPolarization, albert_linear] <;> ring)
    (by intro m i r x; fin_cases i <;>
        simp [rawNewtonPolarization, albert_linear, map_smul, smul_eq_mul] <;> ring)
  cont := by
    have hd : Continuous delta := delta.continuous_of_finiteDimensional
    simp only [rawNewtonPolarization, ← inner_unit_right]
    fun_prop

                                                         
                                                                                             

def nativeEuclideanRepresentation : SymmetricTrilinearForm Coordinates where
  form := nativeEuclideanForm
  swap12 x y z := by
    change rawNewtonPolarization (delta x) (delta y) (delta z) =
      rawNewtonPolarization (delta y) (delta x) (delta z)
    simp only [rawNewtonPolarization, ← inner_jordan_associative,
      jordan_comm (delta x) (delta y), inner_comm (delta y) (delta x)]
    ring
  swap23 x y z := by
    change rawNewtonPolarization (delta x) (delta y) (delta z) =
      rawNewtonPolarization (delta x) (delta z) (delta y)
    simp only [rawNewtonPolarization, jordan_comm (delta y) (delta z), inner_comm (delta y) (delta z)]
    ring

theorem diagonal_nativeEuclideanRepresentation (x : Coordinates) :
    diagonalCubic nativeEuclideanRepresentation.form x = newtonCubicNorm (delta x) := by
  change rawNewtonPolarization (delta x) (delta x) (delta x) = newtonCubicNorm (delta x)
  unfold rawNewtonPolarization newtonCubicNorm Glennie.inner
  ring

def nativeCoordinateUnit : Coordinates := delta.symm (1 : Albert)

@[simp] theorem delta_nativeCoordinateUnit : delta nativeCoordinateUnit = (1 : Albert) :=
  delta.apply_symm_apply 1


theorem nativeNormalization :
    diagonalCubic nativeEuclideanRepresentation.form nativeCoordinateUnit = 1 := by
  rw [diagonal_nativeEuclideanRepresentation, delta_nativeCoordinateUnit]
  norm_num [newtonCubicNorm]

end
end AlbertGeometry.NativeEuclideanNormBinding
