module

public import QPBT.Palomar.LowDegreeGameBridge

/-!
# Strategy bridge for the compact low individual degree game

This module transports compact strategies across the exact question and answer
equivalences of `LowDegreeGameBridge`.  The transported game is the existing
low-degree game, and every compact strategy has exactly the same Born value
after conversion through the Palomar foundation bridge.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-440`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

noncomputable section

namespace POVM

section

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    [DecidableEq I] (e : A ≃ B) (M : POVM A I)
include A B I e M

/-- Relabel the outcomes of a compact POVM along an equivalence. -/
def relabel : POVM B I where
  effect := fun b => M.effect (e.symm b)
  pos := fun b => M.pos (e.symm b)
  sum_eq_one := Trans.trans (Equiv.sum_comp e.symm M.effect) M.sum_eq_one

/-- Outcome relabeling preserves every POVM effect. -/
@[simp] theorem relabel_effect (b : B) :
    (relabel e M).effect b = M.effect (e.symm b) :=
  rfl

end

/-- Outcome relabeling preserves projectivity exactly. -/
theorem relabel_isProjective_iff {A B I : Type*} [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] (e : A ≃ B) (M : POVM A I) :
    (relabel e M).IsProjective ↔ M.IsProjective := by
  constructor
  · intro h a
    simpa using h (e a)
  · tauto

end POVM

namespace Game

/-- Two compact games on fixed carriers are equal when their data fields agree. -/
theorem ext {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    {G H : Game X Y A B} (hμ : G.μ = H.μ) (hdecide : G.decide = H.decide) :
    G = H := by
  cases G
  cases H
  simp_all

/-- Relabel all question and answer carriers of a compact game. -/
def relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq A'] [DecidableEq B']
    (G : Game X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') : Game X' Y' A' B' where
  μ := G.μ.map (Equiv.prodCongr eX eY)
  decide := fun x y a b =>
    G.decide (eX.symm x) (eY.symm y) (eA.symm a) (eB.symm b)

end Game

namespace Strategy

/-- Relabel the questions and outcomes of a compact strategy. -/
def relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : Strategy X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') : Strategy X' Y' A' B' where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  alice := fun x => POVM.relabel eA (S.alice (eX.symm x))
  bob := fun y => POVM.relabel eB (S.bob (eY.symm y))

/-- Relabeling preserves each Born weight after pulling back all four labels. -/
@[simp] theorem outcomeWeight_relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : Strategy X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') (x : X') (y : Y') (a : A') (b : B') :
    (relabel S eX eY eA eB).outcomeWeight x y a b =
      S.outcomeWeight (eX.symm x) (eY.symm y) (eA.symm a) (eB.symm b) :=
  rfl

/-- Relabeling preserves projectivity exactly. -/
theorem relabel_isProjective_iff {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : Strategy X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') :
    (relabel S eX eY eA eB).IsProjective ↔ S.IsProjective := by
  dsimp only [Strategy.IsProjective, relabel]
  simp only [POVM.relabel_isProjective_iff]
  exact Iff.and (Iff.symm (Equiv.forall_congr_left eX)) (Iff.symm (Equiv.forall_congr_left eY))

private theorem sum_equiv₂ {A B A' B' : Type*} [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B'] (eA : A ≃ A') (eB : B ≃ B') (f : A → B → ℝ) :
    (∑ a : A', ∑ b : B', f (eA.symm a) (eB.symm b)) = ∑ a : A, ∑ b : B, f a b := by
  rw [Equiv.sum_comp eA.symm (fun a => ∑ b, f a (eB.symm b))]
  exact Finset.sum_congr rfl fun a _ => Equiv.sum_comp eB.symm (f a)

/-- Simultaneous relabeling of a compact game and strategy preserves value exactly. -/
theorem value_relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq A'] [DecidableEq B']
    (G : Game X Y A B) (S : Strategy X Y A B)
    (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B') :
    (relabel S eX eY eA eB).value (Game.relabel G eX eY eA eB) =
      S.value G := by
  unfold Strategy.value
  change PMF.realWeightedSum (G.μ.map (Equiv.prodCongr eX eY)) _ =
    PMF.realWeightedSum G.μ _
  rw [PMF.realWeightedSum_map]
  apply congrArg (PMF.realWeightedSum G.μ)
  funext xy
  simp only [Game.relabel, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    outcomeWeight_relabel, Equiv.symm_apply_apply]
  exact sum_equiv₂ eA eB fun a b =>
    if G.decide xy.1 xy.2 a b then S.outcomeWeight xy.1 xy.2 a b else 0

/-- Convert a relabeled strategy to the library without changing the value. -/
theorem value_toStrategy_relabel {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    {H : QPBT.Game} {G : Game X Y A B} (S : Strategy X Y A B)
    {eX : X ≃ H.QuestionA} {eY : Y ≃ H.QuestionB} {eA : A ≃ H.AnswerA} {eB : B ≃ H.AnswerB}
    (h : Game.relabel G eX eY eA eB = Game.ofGame H) :
    (toStrategy (G := H) (relabel S eX eY eA eB)).value = S.value G := by
  rw [← value_ofStrategy, ofStrategy_toStrategy, ← h, value_relabel]

end Strategy

/-- Relabeling the concrete compact game gives the original registered game. -/
theorem lowDegreeGame_relabel_eq (P : MIPStarRE.QPBT.LdParams) :
    Game.relabel
        (lowDegreeGame (LowDegreeParams.ofLdParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model))
        (lowDegreeQuestionEquiv P) (lowDegreeQuestionEquiv P)
        (lowDegreeAnswerEquiv P) (lowDegreeAnswerEquiv P) =
      Game.ofGame (MIPStarRE.QPBT.ldGame P) := by
  apply Game.ext
  · exact lowDegreeQuestionPMF_map P
  · funext x y a b
    simpa only [Game.relabel, lowDegreeGame, Game.ofGame, QPBT.ldGame, Equiv.apply_symm_apply] using
      lowDegreeWin_equiv P
      ((lowDegreeQuestionEquiv P).symm x) ((lowDegreeQuestionEquiv P).symm y)
      ((lowDegreeAnswerEquiv P).symm a) ((lowDegreeAnswerEquiv P).symm b)

section

variable (P : MIPStarRE.QPBT.LdParams)
    (S : LowDegreeStrategy (LowDegreeParams.ofLdParams P) (ScalarQ P))
include P S

/-- Convert a compact low-degree strategy into a strategy for the registered game. -/
def lowDegreeStrategyToLibrary :
    MIPStarRE.QPBT.Strategy (MIPStarRE.QPBT.ldGame P) :=
  Strategy.toStrategy (G := MIPStarRE.QPBT.ldGame P)
    (Strategy.relabel S
      (lowDegreeQuestionEquiv P) (lowDegreeQuestionEquiv P)
      (lowDegreeAnswerEquiv P) (lowDegreeAnswerEquiv P))

/-- Conversion to the registered low-degree game preserves the strategy value exactly. -/
theorem lowDegreeStrategyToLibrary_value :
    (lowDegreeStrategyToLibrary P S).value =
      S.value (lowDegreeGame (LowDegreeParams.ofLdParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)) := by
  exact Strategy.value_toStrategy_relabel S (lowDegreeGame_relabel_eq P)

/-- Conversion to the registered low-degree game preserves projectivity exactly. -/
theorem lowDegreeStrategyToLibrary_isProjective_iff :
    (lowDegreeStrategyToLibrary P S).IsProjective ↔ S.IsProjective := by
  exact (Strategy.isProjective_toStrategy_iff _).trans
    (Strategy.relabel_isProjective_iff _ _ _ _ _)

end

end

end MIPStarRE.QPBT.Palomar
