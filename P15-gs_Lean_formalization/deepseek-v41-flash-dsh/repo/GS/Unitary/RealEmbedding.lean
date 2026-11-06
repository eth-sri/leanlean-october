module
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
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
public import GS.Unitary.CholeskySupport
public import GS.Unitary.Factorization
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.OrdinaryQR
public import GS.Unitary.Permutations
public import GS.Unitary.StructuredQR
public import GS.Unitary.Support


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! # Entrywise extension from real orthogonal to complex unitary matrices -/

noncomputable section
open Matrix
namespace GS.UnitaryGeometry

/-- Entrywise scalar extension of real matrices. -/
def ofRealMatrix {n : ℕ} (A : Mat n) : CMat n := A.map Complex.ofRealHom

@[simp] theorem ofRealMatrix_apply {n : ℕ} (A : Mat n) (i j : Fin n) :
    ofRealMatrix A i j = (A i j : ℂ) := rfl

@[simp] theorem ofRealMatrix_mul {n : ℕ} (A B : Mat n) :
    ofRealMatrix (A * B) = ofRealMatrix A * ofRealMatrix B := Matrix.map_mul

@[simp] theorem ofRealMatrix_one {n : ℕ} :
    ofRealMatrix (1 : Mat n) = 1 := by
  exact map_one (Complex.ofRealHom.mapMatrix : Mat n →+* CMat n)

@[simp] theorem ofRealMatrix_transpose {n : ℕ} (A : Mat n) :
    ofRealMatrix Aᵀ = (ofRealMatrix A)ᴴ := by
  ext i j
  simp [ofRealMatrix, Matrix.conjTranspose_apply, Matrix.transpose_apply]

theorem ofRealMatrix_unitary {n : ℕ} {A : Mat n} (h : Orthogonal A) :
    Unitary (ofRealMatrix A) := by
  constructor
  · simpa only [ofRealMatrix_mul, ofRealMatrix_transpose, ofRealMatrix_one] using
      congrArg ofRealMatrix h.1
  · simpa only [ofRealMatrix_mul, ofRealMatrix_transpose, ofRealMatrix_one] using
      congrArg ofRealMatrix h.2

theorem ofRealMatrix_blockDiagonal {n b : ℕ} {A : Mat n}
    (h : BlockDiagonal b A) : CBlockDiagonal b (ofRealMatrix A) := by
  intro i j hij
  simp [h i j hij]

end GS.UnitaryGeometry
