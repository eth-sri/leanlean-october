/- Complete complex-unit alternative for the small mixed residual.
All nine complex input units and all nine complex output entries are retained.
No residual Hermiticity, assumed coefficient identity, genericity or factor
conclusion is a field/premise. -/
module
public import Glennie.Theorems.SectorContraction
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Module

@[expose] public section
namespace Glennie
noncomputable section
namespace MixedComplexUnits
set_option maxHeartbeats 2000000

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

def diagonalInput (a b c : ℂ) : Mat := Matrix.diagonal ![a,b,c]
def symmProduct (D H : Mat) : Mat := (1/2:ℂ) • (D*H+H*D)
def adjugateCommutator (D H : Mat) : Mat :=
  H.adjugate*D.adjugate-D.adjugate*H.adjugate
def complexCommutator (D H K : Mat) : Mat := D*H*K*H*D-H*D*K*D*H

/- Expand the diagonal adjugate through the explicit three-by-three formula
before default simp can replace it by erased-Finset cofactor products. -/
private theorem diagonalInput_adjugate (a b c : ℂ) :
    (diagonalInput a b c).adjugate = Matrix.diagonal ![b*c,a*c,a*b] := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalInput]

theorem mixed_identity (a b c : ℂ) (H K : Mat) :
    SectorArgumentAction.gamma
      (complexCommutator (diagonalInput a b c) H K)
      (symmProduct (diagonalInput a b c) H) =
      adjugateCommutator (diagonalInput a b c) H *
        symmProduct (diagonalInput a b c) H * K -
      K * symmProduct (diagonalInput a b c) H *
        adjugateCommutator (diagonalInput a b c) H := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [complexCommutator, adjugateCommutator,
    symmProduct, SectorArgumentAction.gamma, diagonalInput_adjugate]
  all_goals simp only [Matrix.adjugate_fin_three]
  all_goals simp [diagonalInput, Matrix.diagonal_apply, Matrix.mul_apply,
    Matrix.trace, Matrix.diag, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_three, smul_eq_mul]
  all_goals ring

/- Actual native diagonal binding; no sector convention is relabelled. -/
theorem diagonalInput_native (a b c : ℝ) :
    diagonalInput (a:ℂ) (b:ℂ) (c:ℂ) =
      sectorComplexMatrix (diagonalAlbert a b c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [diagonalInput, sectorComplexMatrix,
      complexHermitianMatrix, complexCoordinatesLinear, diagonalAlbert,
      complexPart]


end MixedComplexUnits
end
end Glennie
