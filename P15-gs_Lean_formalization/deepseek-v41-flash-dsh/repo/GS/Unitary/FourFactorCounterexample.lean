module
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.Real.Sqrt
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
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.M4Certificate
public import GS.M4Necessary
public import GS.M4Obstruction
public import GS.Projection
public import GS.Unitary.CholeskySupport
public import GS.Unitary.Factorization
public import GS.Unitary.FourFactor
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.OrdinaryQR
public import GS.Unitary.Permutations
public import GS.Unitary.RealEmbedding
public import GS.Unitary.StructuredQR
public import GS.Unitary.Support


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact complex four-factor counterexample

The certified real matrix is embedded entrywise into the complex matrices.
Its determinant-modulus table is unchanged, so the universal unitary
obstruction rules out complex factors as well as real factors.
-/

noncomputable section
open Matrix
namespace GS.UnitaryFour
open GS.UnitaryGeometry

theorem ofRealMatrix_inA4 {n : ℕ} {b₁ b₂ b₃ b₄ : ℕ} {P₁ P₂ P₃ A : Mat n}
    (h : InA4 b₁ b₂ b₃ b₄ P₁ P₂ P₃ A) :
    CInA4 b₁ b₂ b₃ b₄ (ofRealMatrix P₁) (ofRealMatrix P₂)
      (ofRealMatrix P₃) (ofRealMatrix A) := by
  rcases h with ⟨B₁,B₂,B₃,B₄,hb₁,hb₂,hb₃,hb₄,he⟩
  refine ⟨ofRealMatrix B₁,ofRealMatrix B₂,ofRealMatrix B₃,ofRealMatrix B₄,
    ofRealMatrix_blockDiagonal hb₁,ofRealMatrix_blockDiagonal hb₂,
    ofRealMatrix_blockDiagonal hb₃,ofRealMatrix_blockDiagonal hb₄,?_⟩
  simpa only [GS.product4, GS.UnitaryGeometry.product4, ofRealMatrix_mul] using
    congrArg ofRealMatrix he

@[simp] theorem normDetBlock_ofRealMatrix (A : Mat 6) :
    normDetBlock (ofRealMatrix A) = GS.M4.absDetBlock A := by
  funext i j
  simp only [normDetBlock, detBlock, ofRealMatrix_apply, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rfl

/-- The explicit algebraic matrix, now considered over ℂ. -/
def Q : CMat 6 := ofRealMatrix GS.M4.Q

theorem Q_unitary : Unitary Q := ofRealMatrix_unitary GS.M4.Q_orthogonal

theorem Q_mem_A4 : CInA4 2 2 2 2 P P P Q :=
  ofRealMatrix_inA4 GS.M4.Q_mem_A4

theorem Q_not_mem_A4Unitary : ¬ CInA4Unitary 2 2 2 2 P P P Q := by
  intro h
  have hden : normDetBlock Q 2 1 * normDetBlock Q 1 0 * normDetBlock Q 1 1 ≠ 0 := by
    simpa only [Q, normDetBlock_ofRealMatrix] using GS.M4.obstruction_denominator_nonzero
  have hn := necessaryCondition Q h hden
  have hr : GS.M4.determinantObstruction GS.M4.Q := by
    simpa only [determinantObstruction, Q, normDetBlock_ofRealMatrix,
      GS.M4.determinantObstruction] using hn
  exact GS.M4.Q_violates_determinantObstruction hr

/-- Unconditional insufficiency of four unitary block factors in the fixed GS family. -/
theorem counterexample : CInA4 2 2 2 2 P P P Q ∧ Unitary Q ∧
    ¬ CInA4Unitary 2 2 2 2 P P P Q :=
  ⟨Q_mem_A4, Q_unitary, Q_not_mem_A4Unitary⟩

end GS.UnitaryFour
