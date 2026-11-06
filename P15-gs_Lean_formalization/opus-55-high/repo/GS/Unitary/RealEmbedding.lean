module

public import GS.Unitary.Factorization
public import GS.Core

@[expose] public section


/-! # Entrywise extension from real orthogonal to complex unitary matrices -/

noncomputable section
open Matrix
namespace GS.UnitaryGeometry

section
variable {n : ℕ}
/-- Entrywise scalar extension of real matrices. -/
def ofRealMatrix (A : Mat n) : CMat n := A.map Complex.ofRealHom

@[simp] theorem ofRealMatrix_apply (A : Mat n) (i j : Fin n) :
    ofRealMatrix A i j = (A i j : ℂ) := rfl

@[simp] theorem ofRealMatrix_mul (A B : Mat n) :
    ofRealMatrix (A * B) = ofRealMatrix A * ofRealMatrix B := Matrix.map_mul

@[simp] theorem ofRealMatrix_one :
    ofRealMatrix (1 : Mat n) = 1 :=
  map_one (Complex.ofRealHom.mapMatrix : Mat n →+* CMat n)

@[simp] theorem ofRealMatrix_transpose (A : Mat n) :
    ofRealMatrix Aᵀ = (ofRealMatrix A)ᴴ := by
  ext i j
  simp

theorem ofRealMatrix_unitary {A : Mat n} (h : Orthogonal A) :
    Unitary (ofRealMatrix A) := by
  constructor
  · simpa only [ofRealMatrix_mul, ofRealMatrix_transpose, ofRealMatrix_one] using
      congrArg ofRealMatrix h.1
  · simpa only [ofRealMatrix_mul, ofRealMatrix_transpose, ofRealMatrix_one] using
      congrArg ofRealMatrix h.2

end

theorem ofRealMatrix_blockDiagonal {n b : ℕ} {A : Mat n}
    (h : BlockDiagonal b A) : CBlockDiagonal b (ofRealMatrix A) := by
  intro i j hij
  aesop


end GS.UnitaryGeometry
