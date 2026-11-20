module

public import QPBT.Games.StrategyClasses
public import QPBT.Test.MagicSquare
public import QPBT.Algebra.Pauli

/-!
# Basic Magic Square symmetry facts

This file proves symmetry of the Magic Square question distribution and
decision predicate, packages the game as a `SymmetricGame`, and defines the
observable associated with a binary measurement.

## References

The game is blueprint
`def:ms-game`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Symmetry of the Magic Square question distribution from blueprint
`def:ms-game`, paper
`08_classical_and_quantum_low_degree_tests.tex:512-610`. -/
theorem msQuestionDistribution_symm (x y : MsType) :
    msGame.μ.weight (x, y) = msGame.μ.weight (y, x) := by
  classical
  simp [msGame, graphDistribution, Sym2.eq_swap]

/-- Symmetry of the Magic Square decision predicate from blueprint
`def:ms-game`, paper
`08_classical_and_quantum_low_degree_tests.tex:512-610`. -/
theorem msWinPredicate_symm (x y : MsType) (a b : MsAnswer) :
    msWinPredicate x y a b = msWinPredicate y x b a := by
  cases x <;> cases y <;> cases a <;> cases b <;>
    simp [msWinPredicate, and_comm, eq_comm]

/-- The symmetric-game presentation of the Magic Square game. -/
noncomputable def msGameSymm : SymmetricGame where
  Question := MsType
  Answer := MsAnswer
  μ := msGame.μ
  μ_prob := msGame.μ_prob
  μ_symm := msQuestionDistribution_symm
  decide := msWinPredicate
  decide_symm := msWinPredicate_symm

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Measurement (ZMod 2) ι)
include ι M

/-- The observable associated with a binary measurement; formalization-only notation
used in blueprint `thm:ms-from-ac`, paper
`08_classical_and_quantum_low_degree_tests.tex:658-722`. -/
def obsOf : Op ι :=
  M.effect 0 - M.effect 1

/-- The signed sum of a binary measurement is its observable. -/
theorem sum_phaseSign_smul_effect_eq_obsOf : ∑ b, phaseSign b • M.effect b = obsOf M := by
  rw [sum_zmod_two]
  simp [phaseSign, obsOf, sub_eq_add_neg]

end

end

end MIPStarRE.QPBT
