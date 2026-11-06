module

public import GS.Unitary.FourFactor

@[expose] public section


/-!
# Exact complex four-factor counterexample

The certified real matrix is embedded entrywise into the complex matrices.
Its determinant-modulus table is unchanged, so the universal unitary
obstruction rules out complex factors as well as real factors.
-/

noncomputable section
namespace GS.UnitaryFour
open GS.UnitaryGeometry

@[simp] theorem normDetBlock_ofRealMatrix (A : Mat 6) :
    normDetBlock (ofRealMatrix A) = GS.M4.absDetBlock A := by
  funext i j
  simp only [normDetBlock, detBlock, ofRealMatrix_apply, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rfl

/-- The explicit algebraic matrix, now considered over ℂ. -/
def Q : CMat 6 := ofRealMatrix GS.M4.Q

theorem Q_not_mem_A4Unitary : ¬ CInA4Unitary 2 2 2 2 P P P Q := fun h => by
  have := necessaryCondition Q h
  have : GS.M4.root6^2 = 6 := by norm_num [GS.M4.root6, mul_pow]
  simp [determinantObstruction, Q, GS.M4.absDetTable_Q, GS.M4.absDetTable, GS.M4.root6] at *
  nlinarith

/-- Unconditional insufficiency of four unitary block factors in the fixed GS family. -/
theorem counterexample : CInA4 2 2 2 2 P P P Q ∧ Unitary Q ∧
    ¬ CInA4Unitary 2 2 2 2 P P P Q :=
  have ⟨_,_,_,_,hb₁,hb₂,hb₃,hb₄,he⟩ := GS.M4.Q_mem_A4
  ⟨⟨_,_,_,_,ofRealMatrix_blockDiagonal hb₁,ofRealMatrix_blockDiagonal hb₂,ofRealMatrix_blockDiagonal hb₃,
    ofRealMatrix_blockDiagonal hb₄,
    by simpa only [Q, P, GS.product4, GS.UnitaryGeometry.product4, ofRealMatrix_mul] using congrArg ofRealMatrix he⟩, ofRealMatrix_unitary GS.M4.Q_orthogonal, Q_not_mem_A4Unitary⟩

end GS.UnitaryFour
