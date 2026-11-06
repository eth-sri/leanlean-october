
import GS.UnitaryLocalModel.Dephasing
import GS.UnitaryNonmanifold.ScalarBridge



/-!
# Algebra of the canonical anchor normalization

This file proves the exact dephased block formula, including the common
unitary basis and the fixed right anchor. Its row and column phase factors
are explicit. The identification with factors extracted continuously from the
matrix itself is the separate polar-normalization step.
-/

noncomputable section
open Matrix GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel

variable (U V : Fin q → CMat 2)

variable (Q A B : CMat q)

variable (o i j : Fin q)

def rowPhaseDiagonal   : CMat 2 :=
  diagTwo (rowPhase Q A o i) (rowPhase Q B o i)

def colPhaseDiagonal   : CMat 2 :=
  diagTwo (colPhase Q A o j) (colPhase Q B o j)

@[simp] theorem colPhaseDiagonal_anchor   :
    colPhaseDiagonal Q A B o o = rowPhaseDiagonal Q A B o o := rfl

theorem rowPhaseDiagonal_unitary {Q A B : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (i : Fin q) :
    GS.Unitary (rowPhaseDiagonal Q A B o i) := by
  apply diagonal_unitary_of_norm_one
  intro k
  fin_cases k
  · exact norm_phase (div_ne_zero (ha.1 i).2 (ha.1 i).1)
  · exact norm_phase (div_ne_zero (hb.1 i).2 (hb.1 i).1)



def phaseGaugeLeft  
     : CMat 2 := U i * rowPhaseDiagonal Q A B o i * V o

def phaseGaugeRight  
     : CMat 2 :=
  (V o)ᴴ * (rowPhaseDiagonal Q A B o o)ᴴ * colPhaseDiagonal Q A B o j * V j

/-- After anchor phases are removed, every middle block uses the same basis. -/
theorem phase_normalization_block  
     (hU : GS.Unitary (U i)) (hV : GS.Unitary (V j)) :
    (phaseGaugeLeft U V Q A B o i)ᴴ * (U i * diagTwo (A i j) (B i j) * V j) *
      (phaseGaugeRight V Q A B o j)ᴴ =
      (V o)ᴴ * diagTwo (dephase Q A o i j) (dephase Q B o i j) * V o := by
  simp only [phaseGaugeLeft, phaseGaugeRight, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (U i)ᴴ (U i), hU.1, Matrix.one_mul,
    ← Matrix.mul_assoc (V j) (V j)ᴴ, hV.2]
  congr 1
  simp only [← Matrix.mul_assoc]
  congr 1
  simp [dephase, colPhaseDiagonal, rowPhaseDiagonal, GS.UnitaryNonmanifold.diagTwo]


end GS.UnitaryLocalModel
