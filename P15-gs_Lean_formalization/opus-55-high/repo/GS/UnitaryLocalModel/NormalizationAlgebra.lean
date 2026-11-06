module

public import GS.UnitaryLocalModel.Dephasing
public import GS.UnitaryNonmanifold.BlockInvariant

@[expose] public section


/-!
# Algebra of the canonical anchor normalization

This file proves the exact dephased block formula, including the common
unitary basis and the fixed right anchor. Its row and column phase factors
are explicit. The identification with factors extracted continuously from the
matrix itself is the separate polar-normalization step.
-/

noncomputable section
open Matrix GS GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel
variable {q : ℕ}

section
variable (Q A B : CMat q)
def rowPhaseDiagonal (o i : Fin q) : CMat 2 :=
  diagTwo (rowPhase Q A o i) (rowPhase Q B o i)

def colPhaseDiagonal (o j : Fin q) : CMat 2 :=
  diagTwo (colPhase Q A o j) (colPhase Q B o j)

@[simp] theorem colPhaseDiagonal_anchor (o : Fin q) :
    colPhaseDiagonal Q A B o o = rowPhaseDiagonal Q A B o o := rfl

end

section
variable {Q A B : CMat q} {o : Fin q}
theorem rowPhaseDiagonal_unitary (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (i : Fin q) :
    GS.Unitary (rowPhaseDiagonal Q A B o i) :=
  diagonal_unitary_of_norm_one _ fun k => by fin_cases k <;> simp [rowPhase, norm_phase, ha.1 i, hb.1 i]

end

def phaseGaugeLeft (U V : Fin q → CMat 2) (Q A B : CMat q)
    (o i : Fin q) : CMat 2 := U i * rowPhaseDiagonal Q A B o i * V o

def phaseGaugeRight (V : Fin q → CMat 2) (Q A B : CMat q)
    (o j : Fin q) : CMat 2 :=
  (V o)ᴴ * (rowPhaseDiagonal Q A B o o)ᴴ * colPhaseDiagonal Q A B o j * V j

theorem phaseGaugeLeft_unitary (U V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)
    (hU : ∀ i, GS.Unitary (U i)) (hV : ∀ j, GS.Unitary (V j))
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (i : Fin q) :
    GS.Unitary (phaseGaugeLeft U V Q A B o i) :=
  ((hU i).mul (rowPhaseDiagonal_unitary ha hb i)).mul (hV o)

section
variable (V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)
theorem phaseGaugeRight_unitary (hV : ∀ j, GS.Unitary (V j))
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (j : Fin q) :
    GS.Unitary (phaseGaugeRight V Q A B o j) :=
  ((((hV o).conjTranspose).mul (rowPhaseDiagonal_unitary ha hb o).conjTranspose).mul
    (diagonal_unitary_of_norm_one _ fun k => by fin_cases k <;> simp [colPhase, norm_phase, ha.2 j, hb.2 j])).mul (hV j)

end

/-- After anchor phases are removed, every middle block uses the same basis. -/
theorem phase_normalization_block (U V : Fin q → CMat 2) (Q A B : CMat q)
    (o i j : Fin q) (hU : GS.Unitary (U i)) (hV : GS.Unitary (V j)) :
    (phaseGaugeLeft U V Q A B o i)ᴴ * (U i * diagTwo (A i j) (B i j) * V j) *
      (phaseGaugeRight V Q A B o j)ᴴ =
      (V o)ᴴ * diagTwo (dephase Q A o i j) (dephase Q B o i j) * V o := by
  simp only [phaseGaugeLeft, phaseGaugeRight, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc (U i)ᴴ, ← Matrix.mul_assoc (V j), hU.1, hV.2, Matrix.one_mul]
  congr 1
  simp only [← Matrix.mul_assoc]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rowPhaseDiagonal, colPhaseDiagonal, diagTwo, dephase, Matrix.mul_apply, Fin.sum_univ_two]

end GS.UnitaryLocalModel
