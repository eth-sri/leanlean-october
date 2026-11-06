module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import GS.ComplexAlgebra
public import GS.Core
public import GS.Frobenius
public import GS.Unitary.Frobenius
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.Projection
public import GS.Unitary.Support
public import GS.UnitaryManifold.CayleyAlgebra
public import GS.UnitaryManifold.CayleyModel


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The real dimension of the full unitary Cayley model

An explicit real-linear coordinate equivalence identifies skew-Hermitian
q-by-q matrices with arbitrary real q-by-q matrices. Above the diagonal we
store real parts; on and below the diagonal we store imaginary parts. In
particular the imaginary diagonal contributes q independent real dimensions.
-/
noncomputable section
open GS Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {q : ℕ}

/-- Independent real coordinates for a skew-Hermitian matrix. -/
def realMatrixToSkew (R : Mat q) : CMat q := fun i j =>
  ⟨if i < j then R i j else if j < i then -R j i else 0,
    if i < j then R j i else R i j⟩

/-- Read real parts above the diagonal and imaginary parts elsewhere. -/
def skewToRealMatrix (A : CMat q) : Mat q := fun i j =>
  if i < j then (A i j).re else (A i j).im

theorem realMatrixToSkew_skewHermitian (R : Mat q) :
    IsSkewHermitian (realMatrixToSkew R) := by
  apply Matrix.ext
  intro i j
  apply Complex.ext
  all_goals
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [realMatrixToSkew, Matrix.conjTranspose_apply, hij, not_lt_of_ge hij.le,
        Complex.star_def, Complex.conj_re, Complex.conj_im]
    · subst j
      simp [realMatrixToSkew, Matrix.conjTranspose_apply,
        Complex.star_def, Complex.conj_re, Complex.conj_im]
    · simp [realMatrixToSkew, Matrix.conjTranspose_apply, hij, not_lt_of_ge hij.le,
        Complex.star_def, Complex.conj_re, Complex.conj_im]

@[simp] theorem skewToRealMatrix_realMatrixToSkew (R : Mat q) :
    skewToRealMatrix (realMatrixToSkew R) = R := by
  ext i j
  by_cases hij : i < j <;> simp [skewToRealMatrix, realMatrixToSkew, hij]

@[simp] theorem realMatrixToSkew_skewToRealMatrix (A : CMat q)
    (hA : IsSkewHermitian A) : realMatrixToSkew (skewToRealMatrix A) = A := by
  apply Matrix.ext
  intro i j
  have ha : star (A j i) = -(A i j) := congrArg (fun M : CMat q => M i j) hA
  have hr := congrArg Complex.re ha
  have hi := congrArg Complex.im ha
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hr
  simp only [Complex.star_def, Complex.conj_im, Complex.neg_im] at hi
  rcases lt_trichotomy i j with hij | hij | hij
  · apply Complex.ext
    · simp [realMatrixToSkew, skewToRealMatrix, hij]
    · simp only [realMatrixToSkew, hij, if_pos, skewToRealMatrix,
        not_lt_of_ge hij.le, if_false]
      linarith
  · subst j
    apply Complex.ext
    · simp only [realMatrixToSkew, lt_self_iff_false, if_false]
      linarith
    · simp [realMatrixToSkew, skewToRealMatrix]
  · apply Complex.ext
    · simp only [realMatrixToSkew, hij, not_lt_of_ge hij.le, if_false, if_true,
        skewToRealMatrix]
      linarith
    · simp [realMatrixToSkew, skewToRealMatrix, not_lt_of_ge hij.le]

/-- The full supported skew-Hermitian model is a real vector space of q² coordinates. -/
def fullSkewCoordinateEquiv (q : ℕ) : Mat q ≃ₗ[ℝ] Model (fun _ : Fin q => 0) where
  toFun R := ⟨realMatrixToSkew R,
    by intro i j hij; exact (hij rfl).elim,
    realMatrixToSkew_skewHermitian R⟩
  invFun A := skewToRealMatrix A.val
  left_inv := skewToRealMatrix_realMatrixToSkew
  right_inv A := Subtype.ext (realMatrixToSkew_skewToRealMatrix A.val A.property.2)
  map_add' R S := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    apply Complex.ext
    all_goals
      by_cases hij : i < j <;> by_cases hji : j < i <;>
        simp [realMatrixToSkew, hij, hji] <;> ring
  map_smul' r R := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    apply Complex.ext
    all_goals
      by_cases hij : i < j <;> by_cases hji : j < i <;>
        simp [realMatrixToSkew, hij, hji, Complex.real_smul]

theorem finrank_fullModel (q : ℕ) :
    Module.finrank ℝ (Model (fun _ : Fin q => 0)) = q * q := by
  rw [← (fullSkewCoordinateEquiv q).finrank_eq]
  simp [Mat, Module.finrank_matrix]

end GS.UnitaryManifold
