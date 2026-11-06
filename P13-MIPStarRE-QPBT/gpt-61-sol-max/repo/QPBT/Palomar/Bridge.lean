module

public import QPBT.Palomar.Foundation
public import QPBT.Games.StrategyClasses
public import MIPStarRE.LDT.Basic.DistributionPMF

/-!
# Exact bridges for the compact Palomar game foundation

This module converts the compact Mathlib-only game and strategy data to and
from the library structures.  The conversions preserve every effect, state,
Born value, and the projective, consistency, commutation, and SPCC predicates.

This bridge uses the repository's legacy import form because Lean `module`
files cannot import the current non-`module` game API.  The compact foundation
itself uses the public module surface required by the Palomar extraction.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57,68-180`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.Palomar

open MIPStarRE.LDT MIPStarRE.Quantum







namespace Game

/-- Convert a library game to the compact PMF representation. -/
noncomputable def ofGame (G : MIPStarRE.QPBT.Game) :
    Game G.QuestionA G.QuestionB G.AnswerA G.AnswerB where
  μ := G.μ.toPMF G.μ_prob
  decide := G.decide









end Game

namespace SymmetricGame

/-- Convert a library symmetric game to the compact PMF representation. -/
noncomputable def ofSymmetricGame (G : MIPStarRE.QPBT.SymmetricGame) :
    SymmetricGame G.Question G.Answer where
  toGame :=
    { μ := G.μ.toPMF G.μ_prob
      decide := G.decide }
  μ_symm := by
    intro x y
    change ENNReal.ofReal (G.μ.weight (x, y)) = ENNReal.ofReal (G.μ.weight (y, x))
    rw [G.μ_symm]
  decide_symm := G.decide_symm





end SymmetricGame

namespace POVM

/-- Convert a library measurement to a compact POVM. -/
def ofMeasurement {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (M : MIPStarRE.Quantum.Measurement A I) : POVM A I where
  effect := M.effect
  pos := fun a => Matrix.nonneg_iff_posSemidef.mp (M.pos a)
  sum_eq_one := M.sum_eq_one

/-- Convert a compact POVM to a library measurement. -/
def toMeasurement {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (M : POVM A I) : MIPStarRE.Quantum.Measurement A I :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne M.effect
    (fun a => Matrix.nonneg_iff_posSemidef.mpr (M.pos a)) M.sum_eq_one









end POVM

namespace Strategy

/-- Convert a library strategy to compact carrier-parametric data. -/
def ofStrategy {G : MIPStarRE.QPBT.Game} (S : MIPStarRE.QPBT.Strategy G) :
    Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  alice := fun x => POVM.ofMeasurement (S.A x)
  bob := fun y => POVM.ofMeasurement (S.B y)

variable {G : MIPStarRE.QPBT.Game} (S : Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB)

/-- Convert compact strategy data to a strategy for a library game on the same carriers. -/
def toStrategy
     :
    MIPStarRE.QPBT.Strategy G where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  A := fun x => (S.alice x).toMeasurement
  B := fun y => (S.bob y).toMeasurement







/-- Compact-to-library-to-compact strategy conversion is exact. -/
@[simp] theorem ofStrategy_toStrategy
     :
    ofStrategy (toStrategy S) = S := by
  cases S
  rfl

/-- The compact and library Born values agree for a library strategy. -/
theorem value_ofStrategy {G : MIPStarRE.QPBT.Game}
    (S : MIPStarRE.QPBT.Strategy G) :
    (ofStrategy S).value (Game.ofGame G) = S.value := by
  unfold MIPStarRE.QPBT.Palomar.Strategy.value MIPStarRE.QPBT.Strategy.value
  rw [MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum G.μ G.μ_prob]
  rfl

/-- Projectivity is unchanged by compact-to-library conversion. -/
theorem isProjective_toStrategy_iff
     :
    (toStrategy S).IsProjective ↔ S.IsProjective :=
  Iff.rfl

end Strategy



/-- Existing and compact commutation predicates agree after `Distribution.toPMF`. -/
theorem isCommutingOn_toPMF_iff
    {X Y A B I : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    (μ : Distribution (X × Y)) (hμ : μ.IsProbability)
    (alice : X → MIPStarRE.Quantum.Measurement A I)
    (bob : Y → MIPStarRE.Quantum.Measurement B I) :
    IsCommutingOn (μ.toPMF hμ) (fun x => POVM.ofMeasurement (alice x))
        (fun y => POVM.ofMeasurement (bob y)) ↔
      MIPStarRE.QPBT.IsCommutingOn μ alice bob := by classical simp_all [MIPStarRE.QPBT.IsCommutingOn, MIPStarRE.QPBT.Palomar.IsCommutingOn, MIPStarRE.QPBT.Palomar.POVM.ofMeasurement]

namespace SymmetricStrategy

/-- Convert a library symmetric strategy to compact data. -/
def ofSymmetricStrategy {G : MIPStarRE.QPBT.SymmetricGame}
    (S : MIPStarRE.QPBT.SymmetricStrategy G) : SymmetricStrategy G.Question G.Answer where
  ι := S.ι
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  ψ_swap := S.ψ_swap
  meas := fun x => POVM.ofMeasurement (S.M x)







/-- The compact and library Born values agree for a library symmetric strategy. -/
theorem value_ofSymmetricStrategy {G : MIPStarRE.QPBT.SymmetricGame}
    (S : MIPStarRE.QPBT.SymmetricStrategy G) :
    (ofSymmetricStrategy S).toStrategy.value
        (SymmetricGame.ofSymmetricGame G).toGame = S.toStrategy.value := Strategy.value_ofStrategy S.toStrategy

/-- Library and compact SPCC predicates are exactly equivalent. -/
theorem isSPCC_ofSymmetricStrategy_iff {G : MIPStarRE.QPBT.SymmetricGame}
    (S : MIPStarRE.QPBT.SymmetricStrategy G) :
    (ofSymmetricStrategy S).IsSPCC (SymmetricGame.ofSymmetricGame G) ↔ S.IsSPCC := by
  change
    ((∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.M x)) ∧
      (∀ x, MIPStarRE.QPBT.Measurement.IsConsistentOn (S.M x) S.ψ) ∧
      IsCommutingOn (G.μ.toPMF G.μ_prob)
        (fun x => POVM.ofMeasurement (S.M x))
         fun x => POVM.ofMeasurement (S.M x) ) ↔ _
  rw [isCommutingOn_toPMF_iff]
  rfl

end SymmetricStrategy

end MIPStarRE.QPBT.Palomar
