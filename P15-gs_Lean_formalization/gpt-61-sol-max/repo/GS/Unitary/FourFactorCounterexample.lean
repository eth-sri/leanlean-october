
import GS.Unitary.FourFactor



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
  simp only [normDetBlock, GS.M4.absDetBlock, GS.M4.detBlock, Matrix.det_fin_two, Matrix.submatrix_apply, ofRealMatrix, Matrix.map_apply, Complex.ofRealHom_eq_coe, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- The explicit algebraic matrix, now considered over ℂ. -/
def Q := ofRealMatrix GS.M4.Q

theorem Q_unitary : Unitary Q := ofRealMatrix_unitary GS.M4.Q_orthogonal

theorem Q_mem_A4 : CInA4 2 2 2 2 P P P Q := by
  obtain ⟨B₁,B₂,B₃,B₄,hb₁,hb₂,hb₃,hb₄,he⟩ := GS.M4.Q_mem_A4
  refine ⟨ofRealMatrix B₁,ofRealMatrix B₂,ofRealMatrix B₃,ofRealMatrix B₄,
    ofRealMatrix_blockDiagonal hb₁,ofRealMatrix_blockDiagonal hb₂,
    ofRealMatrix_blockDiagonal hb₃,ofRealMatrix_blockDiagonal hb₄,?_⟩
  simpa only [Q,P,GS.product4,GS.UnitaryGeometry.product4,ofRealMatrix_mul] using
    congrArg ofRealMatrix he

theorem Q_not_mem_A4Unitary : ¬ CInA4Unitary 2 2 2 2 P P P Q := by
  intro h
  have hden : normDetBlock Q 2 1 * normDetBlock Q 1 0 * normDetBlock Q 1 1 ≠ 0 := by
    simpa only [Q, normDetBlock_ofRealMatrix] using GS.M4.obstruction_denominator_nonzero
  have hn := necessaryCondition Q h hden
  have hr  := by
    simpa only [determinantObstruction, Q, normDetBlock_ofRealMatrix,
      GS.M4.determinantObstruction] using hn
  exact GS.M4.Q_violates_determinantObstruction hr



end GS.UnitaryFour

namespace GS.M4
open GS.UnitaryGeometry

/-- Orthogonal factors would give unitary factors after extension of scalars. -/
theorem Q_not_mem_A4Orth : ¬ InA4Orth 2 2 2 2 P P P Q := by
  rintro ⟨B₁,B₂,B₃,B₄,h₁,h₂,h₃,h₄,o₁,o₂,o₃,o₄,he⟩
  apply GS.UnitaryFour.Q_not_mem_A4Unitary
  refine ⟨ofRealMatrix B₁,ofRealMatrix B₂,ofRealMatrix B₃,ofRealMatrix B₄,
    ofRealMatrix_blockDiagonal h₁,ofRealMatrix_blockDiagonal h₂,
    ofRealMatrix_blockDiagonal h₃,ofRealMatrix_blockDiagonal h₄,
    ofRealMatrix_unitary o₁,ofRealMatrix_unitary o₂,
    ofRealMatrix_unitary o₃,ofRealMatrix_unitary o₄,?_⟩
  simpa only [GS.UnitaryFour.Q,GS.UnitaryFour.P,GS.product4,
    GS.UnitaryGeometry.product4,ofRealMatrix_mul] using congrArg ofRealMatrix he


end GS.M4
