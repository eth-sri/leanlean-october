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

/-- The canonical project distribution associated to a finite Mathlib PMF. -/
noncomputable def pmfDistribution {α : Type*} [Fintype α] (p : PMF α) :
    Distribution α where
  support := Finset.univ
  weight := fun a => (p a).toReal
  nonnegative := fun _ => ENNReal.toReal_nonneg
  outsideSupport := by simp
variable {α : Type*}


/-- The canonical distribution associated to a PMF has total mass one. -/
theorem pmfDistribution_isProbability  [Fintype α] (p : PMF α) :
    (pmfDistribution p).IsProbability := by
  simpa [Distribution.IsProbability, Distribution.totalWeight, pmfDistribution] using
    PMF.sum_toReal_eq_one p

/-- Converting a finite PMF to a project distribution and back is exact. -/
@[simp] theorem pmfDistribution_toPMF  [Fintype α] (p : PMF α) :
    (pmfDistribution p).toPMF (pmfDistribution_isProbability p) = p := by
  ext a
  rw [Distribution.toPMF_apply]
  exact ENNReal.ofReal_toReal (p.apply_ne_top a)

namespace Game

/-- Convert a library game to the compact PMF representation. -/
noncomputable def ofGame (G : MIPStarRE.QPBT.Game) :
    Game G.QuestionA G.QuestionB G.AnswerA G.AnswerB where
  μ := G.μ.toPMF G.μ_prob
  decide := G.decide

/-- Convert a compact game to the library representation with canonical full support. -/
noncomputable def toGame {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] [DecidableEq X] [DecidableEq Y]
    [DecidableEq A] [DecidableEq B] (G : Game X Y A B) : MIPStarRE.QPBT.Game where
  QuestionA := X
  QuestionB := Y
  AnswerA := A
  AnswerB := B
  μ := pmfDistribution G.μ
  μ_prob := pmfDistribution_isProbability G.μ
  decide := G.decide

/-- The canonical library conversion has exactly the original question PMF. -/
@[simp] theorem toGame_questionPMF {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] [DecidableEq X] [DecidableEq Y]
    [DecidableEq A] [DecidableEq B] (G : Game X Y A B) :
    (G.toGame.μ.toPMF G.toGame.μ_prob) = G.μ :=
  pmfDistribution_toPMF G.μ

/-- Compact-to-library-to-compact game conversion is exact. -/
@[simp] theorem ofGame_toGame {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] [DecidableEq X] [DecidableEq Y]
    [DecidableEq A] [DecidableEq B] (G : Game X Y A B) :
    ofGame G.toGame = G := by
  cases G
  simp [ofGame, toGame]
  rfl

/-- Library-to-compact-to-library conversion preserves the question PMF exactly. -/
@[simp] theorem ofGame_toGame_questionPMF (G : MIPStarRE.QPBT.Game) :
    ((ofGame G).toGame.μ.toPMF (ofGame G).toGame.μ_prob) = G.μ.toPMF G.μ_prob := by
  rw [toGame_questionPMF]
  rfl

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

/-- Convert a compact symmetric game to the library representation. -/
noncomputable def toSymmetricGame {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A]
    (G : SymmetricGame X A) : MIPStarRE.QPBT.SymmetricGame where
  Question := X
  Answer := A
  μ := pmfDistribution G.μ
  μ_prob := pmfDistribution_isProbability G.μ
  μ_symm := fun x y => congrArg ENNReal.toReal (G.μ_symm x y)
  decide := G.decide
  decide_symm := G.decide_symm

/-- Compact-to-library-to-compact symmetric-game conversion is exact. -/
@[simp] theorem ofSymmetricGame_toSymmetricGame
    {X A : Type} [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
    (G : SymmetricGame X A) : ofSymmetricGame G.toSymmetricGame = G := by
  cases G
  simp [ofSymmetricGame, toSymmetricGame]
  rfl

end SymmetricGame

namespace POVM
variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]


/-- Convert a library measurement to a compact POVM. -/
def ofMeasurement 
    (M : MIPStarRE.Quantum.Measurement A I) : POVM A I where
  effect := M.effect
  pos := fun a => Matrix.nonneg_iff_posSemidef.mp (M.pos a)
  sum_eq_one := M.sum_eq_one

/-- Convert a compact POVM to a library measurement. -/
def toMeasurement 
    (M : POVM A I) : MIPStarRE.Quantum.Measurement A I :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne M.effect
    (fun a => Matrix.nonneg_iff_posSemidef.mpr (M.pos a)) M.sum_eq_one

@[simp] theorem ofMeasurement_effect {A I : Type*} [Fintype A] [Fintype I]
    [DecidableEq I] (M : MIPStarRE.Quantum.Measurement A I) (a : A) :
    (ofMeasurement M).effect a = M.effect a := rfl

@[simp] theorem toMeasurement_effect {A I : Type*} [Fintype A] [Fintype I]
    [DecidableEq I] (M : POVM A I) (a : A) :
    M.toMeasurement.effect a = M.effect a := rfl
variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]


/-- Compact-to-library-to-compact POVM conversion is exact. -/
@[simp] theorem ofMeasurement_toMeasurement  (M : POVM A I) : ofMeasurement M.toMeasurement = M := by
  cases M
  rfl

/-- Library-to-compact-to-library measurement conversion is exact. -/
@[simp] theorem toMeasurement_ofMeasurement  (M : MIPStarRE.Quantum.Measurement A I) :
    (ofMeasurement M).toMeasurement = M := by
  apply MIPStarRE.Quantum.Measurement.ext
  intro a
  rfl

end POVM

namespace Strategy
variable {G : MIPStarRE.QPBT.Game}


/-- Convert a library strategy to compact carrier-parametric data. -/
def ofStrategy  (S : MIPStarRE.QPBT.Strategy G) :
    Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  alice := fun x => POVM.ofMeasurement (S.A x)
  bob := fun y => POVM.ofMeasurement (S.B y)

/-- Convert compact strategy data to a strategy for a library game on the same carriers. -/
def toStrategy 
    (S : Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB) :
    MIPStarRE.QPBT.Strategy G where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  A := fun x => (S.alice x).toMeasurement
  B := fun y => (S.bob y).toMeasurement

/-- Strategy conversion preserves Alice's effects pointwise. -/
@[simp] theorem toStrategy_alice_effect {G : MIPStarRE.QPBT.Game}
    (S : Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB)
    (x : G.QuestionA) (a : G.AnswerA) :
    ((toStrategy S).A x).effect a = (S.alice x).effect a := rfl

/-- Strategy conversion preserves Bob's effects pointwise. -/
@[simp] theorem toStrategy_bob_effect {G : MIPStarRE.QPBT.Game}
    (S : Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB)
    (y : G.QuestionB) (b : G.AnswerB) :
    ((toStrategy S).B y).effect b = (S.bob y).effect b := rfl
variable {G : MIPStarRE.QPBT.Game}


/-- Library-to-compact-to-library strategy conversion is exact. -/
@[simp] theorem toStrategy_ofStrategy 
    (S : MIPStarRE.QPBT.Strategy G) : toStrategy (ofStrategy S) = S := by
  cases S
  rfl

/-- Compact-to-library-to-compact strategy conversion is exact. -/
@[simp] theorem ofStrategy_toStrategy 
    (S : Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB) :
    ofStrategy (toStrategy S) = S := by
  cases S
  rfl

/-- The compact and library Born values agree for a library strategy. -/
theorem value_ofStrategy 
    (S : MIPStarRE.QPBT.Strategy G) :
    (ofStrategy S).value (Game.ofGame G) = S.value := by
  unfold MIPStarRE.QPBT.Palomar.Strategy.value MIPStarRE.QPBT.Strategy.value
  rw [MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum G.μ G.μ_prob]
  rfl

/-- Projectivity is unchanged by compact-to-library conversion. -/
theorem isProjective_toStrategy_iff {G : MIPStarRE.QPBT.Game}
    (S : Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB) :
    (toStrategy S).IsProjective ↔ S.IsProjective :=
  Iff.rfl

end Strategy

/-- A project distribution and its PMF have the same positive-probability support. -/
theorem distribution_toPMF_pos_iff  (μ : Distribution α)
    (hμ : μ.IsProbability) (a : α) : 0 < μ.toPMF hμ a ↔ 0 < μ.weight a := by
  rw [Distribution.toPMF_apply]
  exact ENNReal.ofReal_pos

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
      MIPStarRE.QPBT.IsCommutingOn μ alice bob := by
  constructor
  · intro h x y hxy a b
    exact h x y ((distribution_toPMF_pos_iff μ hμ (x, y)).mpr hxy) a b
  · intro h x y hxy a b
    exact h x y ((distribution_toPMF_pos_iff μ hμ (x, y)).mp hxy) a b

namespace SymmetricStrategy
variable {G : MIPStarRE.QPBT.SymmetricGame}


/-- Convert a library symmetric strategy to compact data. -/
def ofSymmetricStrategy 
    (S : MIPStarRE.QPBT.SymmetricStrategy G) : SymmetricStrategy G.Question G.Answer where
  ι := S.ι
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  ψ_swap := S.ψ_swap
  meas := fun x => POVM.ofMeasurement (S.M x)

/-- Convert compact symmetric strategy data to a library symmetric strategy. -/
def toSymmetricStrategy 
    (S : SymmetricStrategy G.Question G.Answer) : MIPStarRE.QPBT.SymmetricStrategy G where
  ι := S.ι
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  ψ_swap := S.ψ_swap
  M := fun x => (S.meas x).toMeasurement
variable {G : MIPStarRE.QPBT.SymmetricGame}


/-- Library-to-compact-to-library symmetric strategy conversion is exact. -/
@[simp] theorem toSymmetricStrategy_ofSymmetricStrategy  (S : MIPStarRE.QPBT.SymmetricStrategy G) :
    toSymmetricStrategy (ofSymmetricStrategy S) = S := by
  cases S
  rfl

/-- Compact-to-library-to-compact symmetric strategy conversion is exact. -/
@[simp] theorem ofSymmetricStrategy_toSymmetricStrategy  (S : SymmetricStrategy G.Question G.Answer) :
    ofSymmetricStrategy (toSymmetricStrategy S) = S := by
  cases S
  rfl

/-- The compact and library Born values agree for a library symmetric strategy. -/
theorem value_ofSymmetricStrategy 
    (S : MIPStarRE.QPBT.SymmetricStrategy G) :
    (ofSymmetricStrategy S).toStrategy.value
        (SymmetricGame.ofSymmetricGame G).toGame = S.toStrategy.value := by
  exact Strategy.value_ofStrategy S.toStrategy

/-- Library and compact SPCC predicates are exactly equivalent. -/
theorem isSPCC_ofSymmetricStrategy_iff 
    (S : MIPStarRE.QPBT.SymmetricStrategy G) :
    (ofSymmetricStrategy S).IsSPCC (SymmetricGame.ofSymmetricGame G) ↔ S.IsSPCC := by
  change
    ((∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.M x)) ∧
      (∀ x, MIPStarRE.QPBT.Measurement.IsConsistentOn (S.M x) S.ψ) ∧
      IsCommutingOn (G.μ.toPMF G.μ_prob)
        (fun x => POVM.ofMeasurement (S.M x))
        (fun x => POVM.ofMeasurement (S.M x))) ↔ _
  rw [isCommutingOn_toPMF_iff]
  rfl

end SymmetricStrategy

end MIPStarRE.QPBT.Palomar
