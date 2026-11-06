module

public import QPBT.Palomar.Foundation
public import QPBT.Games.StrategyClasses
public import MIPStarRE.LDT.Basic.DistributionPMF

@[expose] public section

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.Palomar

open MIPStarRE.LDT MIPStarRE.Quantum

namespace Game

noncomputable def ofGame (G : MIPStarRE.QPBT.Game) :
    Game G.QuestionA G.QuestionB G.AnswerA G.AnswerB where
  μ := G.μ.toPMF G.μ_prob
  decide := G.decide

end Game

namespace SymmetricGame

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

def ofMeasurement {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (M : MIPStarRE.Quantum.Measurement A I) : POVM A I where
  effect := M.effect
  pos := fun a => Matrix.nonneg_iff_posSemidef.mp (M.pos a)
  sum_eq_one := M.sum_eq_one

def toMeasurement {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (M : POVM A I) : MIPStarRE.Quantum.Measurement A I :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne M.effect
    (fun a => Matrix.nonneg_iff_posSemidef.mpr (M.pos a)) M.sum_eq_one

end POVM

namespace Strategy

def ofStrategy {G : MIPStarRE.QPBT.Game} (S : MIPStarRE.QPBT.Strategy G) :
    Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  alice := fun x => POVM.ofMeasurement (S.A x)
  bob := fun y => POVM.ofMeasurement (S.B y)

def toStrategy {G : MIPStarRE.QPBT.Game}
    (S : Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB) :
    MIPStarRE.QPBT.Strategy G where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  A := fun x => (S.alice x).toMeasurement
  B := fun y => (S.bob y).toMeasurement

@[simp] theorem ofStrategy_toStrategy {G : MIPStarRE.QPBT.Game}
    (S : Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB) :
    ofStrategy (toStrategy S) = S := by
  cases S
  rfl

theorem value_ofStrategy {G : MIPStarRE.QPBT.Game}
    (S : MIPStarRE.QPBT.Strategy G) :
    (ofStrategy S).value (Game.ofGame G) = S.value := by
  unfold MIPStarRE.QPBT.Palomar.Strategy.value MIPStarRE.QPBT.Strategy.value
  rw [MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum G.μ G.μ_prob]
  rfl

theorem isProjective_toStrategy_iff {G : MIPStarRE.QPBT.Game}
    (S : Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB) :
    (toStrategy S).IsProjective ↔ S.IsProjective :=
  Iff.rfl

end Strategy

theorem distribution_toPMF_pos_iff {α : Type*} (μ : Distribution α)
    (hμ : μ.IsProbability) (a : α) : 0 < μ.toPMF hμ a ↔ 0 < μ.weight a := by
  rw [Distribution.toPMF_apply]
  exact ENNReal.ofReal_pos

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

def ofSymmetricStrategy {G : MIPStarRE.QPBT.SymmetricGame}
    (S : MIPStarRE.QPBT.SymmetricStrategy G) : SymmetricStrategy G.Question G.Answer where
  ι := S.ι
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  ψ_swap := S.ψ_swap
  meas := fun x => POVM.ofMeasurement (S.M x)

theorem value_ofSymmetricStrategy {G : MIPStarRE.QPBT.SymmetricGame}
    (S : MIPStarRE.QPBT.SymmetricStrategy G) :
    (ofSymmetricStrategy S).toStrategy.value
        (SymmetricGame.ofSymmetricGame G).toGame = S.toStrategy.value := Strategy.value_ofStrategy S.toStrategy

theorem isSPCC_ofSymmetricStrategy_iff {G : MIPStarRE.QPBT.SymmetricGame}
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
