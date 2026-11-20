module

public import GS.Unitary.Factorization

public import GS.Core

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! # Entrywise extension from real orthogonal to complex unitary matrices -/

noncomputable section
open Matrix
namespace GS.UnitaryGeometry

/-- Entrywise scalar extension of real matrices. -/
def ofRealMatrix {n : ℕ} (A : Mat n) : CMat n := A.map Complex.ofRealHom

@[simp] theorem ofRealMatrix_mul {n : ℕ} (A B : Mat n) :
    ofRealMatrix (A * B) = ofRealMatrix A * ofRealMatrix B := Matrix.map_mul

@[simp] theorem ofRealMatrix_one {n : ℕ} :
    ofRealMatrix (1 : Mat n) = 1 := by
  exact map_one (Complex.ofRealHom.mapMatrix : Mat n →+* CMat n)

@[simp] theorem ofRealMatrix_transpose {n : ℕ} (A : Mat n) :
    ofRealMatrix Aᵀ = (ofRealMatrix A)ᴴ := by
  ext <;> simp [ofRealMatrix]

theorem ofRealMatrix_unitary {n : ℕ} {A : Mat n} (h : Orthogonal A) :
    Unitary (ofRealMatrix A) := by
  have h' : (ofRealMatrix A)ᴴ * ofRealMatrix A = 1 := by simpa using congrArg ofRealMatrix h.1
  exact ⟨h', mul_eq_one_comm.mp h'⟩

theorem ofRealMatrix_blockDiagonal {n b : ℕ} {A : Mat n}
    (h : BlockDiagonal b A) : CBlockDiagonal b (ofRealMatrix A) := by
  intro i j hij
  exact Complex.ext (h i j hij) rfl

end GS.UnitaryGeometry
