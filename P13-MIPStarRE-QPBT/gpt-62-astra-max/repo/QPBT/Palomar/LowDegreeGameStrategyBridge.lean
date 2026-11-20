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

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I] [DecidableEq I] (e : A ≃ B)
  (M : POVM A I)

/-- Relabel the outcomes of a compact POVM along an equivalence. -/
def relabel : POVM B I where
  effect := fun b => M.effect (e.symm b)
  pos := fun b => M.pos (e.symm b)
  sum_eq_one := by
    rw [← M.sum_eq_one]
    exact Equiv.sum_comp e.symm M.effect

/-- Outcome relabeling preserves every POVM effect. -/
@[simp] theorem relabel_effect (b : B) :
    (relabel e M).effect b = M.effect (e.symm b) :=
  rfl

/-- Outcome relabeling preserves projectivity exactly. -/
theorem relabel_isProjective_iff :
    (relabel e M).IsProjective ↔ M.IsProjective := by
  constructor
  · intro h a
    simpa using h (e a)
  · intro h b
    apply h

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

section

variable {X Y A B X' Y' A' B' : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype X']
  [Fintype Y'] [Fintype A'] [Fintype B'] (S : Strategy X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
  (eA : A ≃ A') (eB : B ≃ B')

/-- Relabel the questions and outcomes of a compact strategy. -/
def relabel : Strategy X' Y' A' B' where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  alice := fun x => POVM.relabel eA (S.alice (eX.symm x))
  bob := fun y => POVM.relabel eB (S.bob (eY.symm y))

/-- Relabeling preserves each Born weight after pulling back all four labels. -/
@[simp] theorem outcomeWeight_relabel (x : X') (y : Y') (a : A') (b : B') :
    (relabel S eX eY eA eB).outcomeWeight x y a b =
      S.outcomeWeight (eX.symm x) (eY.symm y) (eA.symm a) (eB.symm b) :=
  rfl

/-- Relabeling preserves projectivity exactly. -/
theorem relabel_isProjective_iff :
    (relabel S eX eY eA eB).IsProjective ↔ S.IsProjective := by
  constructor
  · rintro ⟨hA, hB⟩
    constructor
    · intro x
      have hx := hA (eX x)
      change (POVM.relabel eA _).IsProjective at hx
      simp at hx
      exact (POVM.relabel_isProjective_iff eA (S.alice x)).mp hx
    · intro y
      have hy := hB (eY y)
      change (POVM.relabel eB _).IsProjective at hy
      simp at hy
      exact (POVM.relabel_isProjective_iff eB (S.bob y)).mp hy
  · rintro ⟨hA, hB⟩
    constructor
    · intro x
      exact (POVM.relabel_isProjective_iff eA (S.alice (eX.symm x))).mpr
        (hA (eX.symm x))
    · intro y
      exact (POVM.relabel_isProjective_iff eB (S.bob (eY.symm y))).mpr
        (hB (eY.symm y))

end

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
  change PMF.realWeightedSum (G.μ.map (Equiv.prodCongr eX eY)) _ =
    _
  rw [PMF.realWeightedSum_map]
  apply congrArg
  funext xy
  simp [Game.relabel]
  calc
    _ =
        ∑ a : _, ∑ b : _, (fun a b => if G.decide xy.1 xy.2 a b then S.outcomeWeight xy.1 xy.2 a b else 0) a (eB.symm b) :=
      Equiv.sum_comp eA.symm (fun a => ∑ b : _, (fun a b => if G.decide xy.1 xy.2 a b then S.outcomeWeight xy.1 xy.2 a b else 0) a (eB.symm b))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact Equiv.sum_comp eB.symm ((fun a b => if G.decide xy.1 xy.2 a b then S.outcomeWeight xy.1 xy.2 a b else 0) a)

end Strategy

variable (P : MIPStarRE.QPBT.LdParams)

/-- Relabeling the concrete compact game gives the original registered game. -/
theorem lowDegreeGame_relabel_eq :
    Game.relabel
        (lowDegreeGame (LowDegreeParams.ofLdParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model))
        (lowDegreeQuestionEquiv P) (lowDegreeQuestionEquiv P)
        (lowDegreeAnswerEquiv P) (lowDegreeAnswerEquiv P) =
      Game.ofGame (MIPStarRE.QPBT.ldGame P) := by
  apply Game.ext
  · exact lowDegreeQuestionPMF_map P
  · funext x y a b
    change lowDegreeWin _
        (MIPStarRE.QPBT.binaryRepresentation P.model)
        ((lowDegreeQuestionEquiv P).symm x) ((lowDegreeQuestionEquiv P).symm y)
        ((lowDegreeAnswerEquiv P).symm a) ((lowDegreeAnswerEquiv P).symm b) =
      MIPStarRE.QPBT.ldWinPredicate P x y a b
    simpa using lowDegreeWin_equiv P
      ((lowDegreeQuestionEquiv P).symm x) ((lowDegreeQuestionEquiv P).symm y)
      ((lowDegreeAnswerEquiv P).symm a) ((lowDegreeAnswerEquiv P).symm b)

section

variable
  (S : Strategy (LowDegreeQuestion (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)) (LowDegreeQuestion (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)) (LowDegreeAnswer (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)) (LowDegreeAnswer (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)))

variable {P} in
/-- Convert a compact low-degree strategy into a strategy for the registered game. -/
def lowDegreeStrategyToLibrary :
    MIPStarRE.QPBT.Strategy (MIPStarRE.QPBT.ldGame P) :=
  Strategy.toStrategy (G := MIPStarRE.QPBT.ldGame P)
    (Strategy.relabel S
      (lowDegreeQuestionEquiv P) (lowDegreeQuestionEquiv P)
      (lowDegreeAnswerEquiv P) (lowDegreeAnswerEquiv P))

/-- Conversion to the registered low-degree game preserves the strategy value exactly. -/
theorem lowDegreeStrategyToLibrary_value :
    (lowDegreeStrategyToLibrary S).value =
      S.value (lowDegreeGame (LowDegreeParams.ofLdParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)) := by
  let S' := Strategy.relabel S
    (lowDegreeQuestionEquiv P) (lowDegreeQuestionEquiv P)
    (lowDegreeAnswerEquiv P) (lowDegreeAnswerEquiv P)
  calc
    _ =
        _ :=
      (Strategy.value_ofStrategy (lowDegreeStrategyToLibrary S)).symm
    _ = S'.value (Game.ofGame (MIPStarRE.QPBT.ldGame P)) := by
      rfl
    _ = S'.value (Game.relabel
        (lowDegreeGame (LowDegreeParams.ofLdParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model))
        (lowDegreeQuestionEquiv P) (lowDegreeQuestionEquiv P)
        (lowDegreeAnswerEquiv P) (lowDegreeAnswerEquiv P)) := by
      rw [lowDegreeGame_relabel_eq]
      rfl
    _ = _ :=
      Strategy.value_relabel _ _ _ _ _ _

/-- Conversion to the registered low-degree game preserves projectivity exactly. -/
theorem lowDegreeStrategyToLibrary_isProjective_iff :
    (lowDegreeStrategyToLibrary S).IsProjective ↔ S.IsProjective := by
  apply Strategy.relabel_isProjective_iff

end

end

end MIPStarRE.QPBT.Palomar
