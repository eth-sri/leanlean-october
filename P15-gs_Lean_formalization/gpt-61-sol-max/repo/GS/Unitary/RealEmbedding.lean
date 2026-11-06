
import GS.Unitary.Factorization
import GS.Core




/-! # Entrywise extension from real orthogonal to complex unitary matrices -/

open Matrix
namespace GS.UnitaryGeometry

variable (A B : Mat n)

/-- Entrywise scalar extension of real matrices. -/
def ofRealMatrix  : CMat n := A.map Complex.ofRealHom

@[simp] theorem ofRealMatrix_mul  :
    ofRealMatrix (A * B) = ofRealMatrix A * ofRealMatrix B := Matrix.map_mul

@[simp] theorem ofRealMatrix_one :
    ofRealMatrix (1 : Mat n) = 1 := map_one (Complex.ofRealHom.mapMatrix : Mat n →+* CMat n)

@[simp] theorem ofRealMatrix_transpose  :
    ofRealMatrix Aᵀ = (ofRealMatrix A)ᴴ := by
  aesop (add norm [ofRealMatrix])

theorem ofRealMatrix_unitary {A : Mat n} (h : Orthogonal A) :
    Unitary (ofRealMatrix A) := by
  constructor
  · simpa only [ofRealMatrix_mul, ofRealMatrix_transpose, ofRealMatrix_one] using
      congrArg ofRealMatrix h.1
  · simpa only [ofRealMatrix_mul, ofRealMatrix_transpose, ofRealMatrix_one] using
      congrArg ofRealMatrix h.2

theorem ofRealMatrix_blockDiagonal {n b : ℕ} {A : Mat n}
    (h : BlockDiagonal b A) : CBlockDiagonal b (ofRealMatrix A) := by
  intro i j hij
  exact congrArg Complex.ofReal (h i j hij)



end GS.UnitaryGeometry
