module

public import QPBT.Palomar.PauliGameBridge
public import QPBT.Palomar.LowDegreeGameStrategyBridge
public import QPBT.Test.Completeness

/-!
# Strategy bridge for the compact Pauli basis game

This module transports compact strategies across the exact question and answer
equivalences of `PauliGameBridge`.  It preserves the game, Born value,
projectivity, symmetry, consistency, positive-support commutation, and the SPCC
predicate exactly.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1491`.
-/

@[expose] public section

namespace MIPStarRE.QPBT.Palomar

noncomputable section

local instance compactPauliQuestionDecidableEq
    (P : MIPStarRE.QPBT.AdmissibleParams) :
    DecidableEq
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :=
  instDecidableEqPauliQuestion

namespace PMF

/-- Pushing a PMF through an equivalence preserves its mass at corresponding points. -/
@[simp] theorem map_equiv_apply {X Y : Type*} (p : PMF X) (e : X ≃ Y) (x : X) :
    (p.map e) (e x) = p x := by
  classical
  simp [PMF.map_apply, e.injective.eq_iff]

/-- A PMF pushed through an equivalence is evaluated by pulling the point back. -/
theorem map_equiv_apply' {X Y : Type*} (p : PMF X) (e : X ≃ Y) (y : Y) :
    (p.map e) y = p (e.symm y) := by
  simpa only [e.apply_symm_apply] using map_equiv_apply p e (e.symm y)

end PMF

namespace POVM

/-- Outcome relabeling preserves state-dependent consistency exactly. -/
theorem relabel_isConsistentOn_iff {A B I : Type*} [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq A] [DecidableEq B] [DecidableEq I]
    (e : A ≃ B) (M : POVM A I) (ψ : EuclideanSpace ℂ (I × I)) :
    (relabel e M).IsConsistentOn ψ ↔ M.IsConsistentOn ψ := by
  exact (e.forall_congr_left (p := fun a =>
    (Matrix.kronecker (M.effect a) 1).mulVec ψ = (Matrix.kronecker 1 (M.effect a)).mulVec ψ)).symm

end POVM

/-- Positive-support commutation is invariant under exact question and outcome relabeling. -/
theorem isCommutingOn_relabel_iff
    {X Y A B X' Y' A' B' I : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    [Fintype I] [DecidableEq I]
    (μ : PMF (X × Y)) (alice : X → POVM A I) (bob : Y → POVM B I)
    (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B') :
    IsCommutingOn (μ.map (Equiv.prodCongr eX eY))
        (fun x => POVM.relabel eA (alice (eX.symm x)))
        (fun y => POVM.relabel eB (bob (eY.symm y))) ↔
      IsCommutingOn μ alice bob := by
  unfold IsCommutingOn
  refine eX.symm.forall_congr fun x => eY.symm.forall_congr fun y => ?_
  rw [PMF.map_equiv_apply' μ (eX.prodCongr eY) (x, y)]
  exact imp_congr_right fun _ =>
    eA.symm.forall_congr fun _ => eB.symm.forall_congr fun _ => Iff.rfl

namespace Game

/-- Relabeling a compact game and then relabeling by the inverse equivalences is exact. -/
theorem relabel_symm_relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq A'] [DecidableEq B']
    (G : Game X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') :
    Game.relabel (Game.relabel G eX eY eA eB)
        eX.symm eY.symm eA.symm eB.symm = G := by
  apply Game.ext
  · let e := eX.prodCongr eY
    change (G.μ.map e).map e.symm = G.μ
    rw [PMF.map_comp, e.symm_comp_self, PMF.map_id]
  · funext x y a b
    simp [Game.relabel]

end Game

namespace SymmetricGame

/-- Relabel the questions and answers of a compact symmetric game. -/
def relabel {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    [DecidableEq X] [DecidableEq A] [DecidableEq X'] [DecidableEq A']
    (G : SymmetricGame X A) (eX : X ≃ X') (eA : A ≃ A') :
    SymmetricGame X' A' where
  toGame := Game.relabel G.toGame eX eX eA eA
  μ_symm := by
    intro x y
    change (G.μ.map (Equiv.prodCongr eX eX)) (x, y) =
      (G.μ.map (Equiv.prodCongr eX eX)) (y, x)
    rw [PMF.map_equiv_apply', PMF.map_equiv_apply']
    exact G.μ_symm (eX.symm x) (eX.symm y)
  decide_symm := by
    intro x y a b
    exact G.decide_symm (eX.symm x) (eX.symm y) (eA.symm a) (eA.symm b)

end SymmetricGame

namespace SymmetricStrategy

/-- Relabel the questions and outcomes of a compact symmetric strategy. -/
def relabel {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    (S : SymmetricStrategy X A) (eX : X ≃ X') (eA : A ≃ A') :
    SymmetricStrategy X' A' where
  ι := S.ι
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  ψ_swap := S.ψ_swap
  meas := fun x => POVM.relabel eA (S.meas (eX.symm x))

/-- Symmetric relabeling preserves projectivity of the measurement family exactly. -/
theorem relabel_isProjective_iff {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    (S : SymmetricStrategy X A) (eX : X ≃ X') (eA : A ≃ A') :
    (∀ x, ((relabel S eX eA).meas x).IsProjective) ↔
      ∀ x, (S.meas x).IsProjective := by
  change (∀ x, (POVM.relabel eA (S.meas (eX.symm x))).IsProjective) ↔ _
  simp only [POVM.relabel_isProjective_iff]
  exact (eX.forall_congr_left (p := fun x => (S.meas x).IsProjective)).symm

/-- Symmetric relabeling preserves consistency exactly. -/
theorem relabel_isConsistent_iff {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    [DecidableEq A] [DecidableEq A']
    (S : SymmetricStrategy X A) (eX : X ≃ X') (eA : A ≃ A') :
    (relabel S eX eA).IsConsistent ↔ S.IsConsistent := by
  dsimp only [SymmetricStrategy.IsConsistent, relabel]
  simp only [POVM.relabel_isConsistentOn_iff]
  exact (eX.forall_congr_left (p := fun x => (S.meas x).IsConsistentOn S.ψ)).symm

/-- Symmetric relabeling preserves the SPCC predicate under the exact PMF push-forward. -/
theorem relabel_isSPCC_iff {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    [DecidableEq X] [DecidableEq A] [DecidableEq X'] [DecidableEq A']
    (G : SymmetricGame X A) (G' : SymmetricGame X' A')
    (S : SymmetricStrategy X A) (eX : X ≃ X') (eA : A ≃ A')
    (hμ : G.μ.map (Equiv.prodCongr eX eX) = G'.μ) :
    (relabel S eX eA).IsSPCC G' ↔ S.IsSPCC G := by
  rw [SymmetricStrategy.IsSPCC, SymmetricStrategy.IsSPCC, ← hμ]
  exact Iff.and (relabel_isProjective_iff S eX eA) <|
    Iff.and (relabel_isConsistent_iff S eX eA) (isCommutingOn_relabel_iff G.μ S.meas S.meas _ _ _ _)

end SymmetricStrategy

/-- Relabeling the concrete compact Pauli game gives the registered game exactly. -/
theorem pauliGame_relabel_eq (P : MIPStarRE.QPBT.AdmissibleParams) :
    Game.relabel
        (pauliGame (PauliParams.ofAdmissibleParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model)
          (MIPStarRE.QPBT.fixedBinTrace P.model))
        (pauliQuestionEquiv P) (pauliQuestionEquiv P)
        (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P) =
      Game.ofGame (MIPStarRE.QPBT.pauliBasisTest P) := by
  apply Game.ext
  · exact pauliQuestionPMF_map P
  · funext x y a b
    simpa only [Game.relabel, pauliGame, Game.ofGame, QPBT.pauliBasisTest, Equiv.apply_symm_apply] using
      pauliWin_equiv P
      ((pauliQuestionEquiv P).symm x) ((pauliQuestionEquiv P).symm y)
      ((pauliAnswerEquivCompact P).symm a) ((pauliAnswerEquivCompact P).symm b)

section

variable (P : MIPStarRE.QPBT.AdmissibleParams)
    (S : Strategy
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)))
include P S

/-- Convert a compact Pauli strategy into a strategy for the registered game. -/
def pauliStrategyToLibrary :
    MIPStarRE.QPBT.Strategy (MIPStarRE.QPBT.pauliBasisTest P) :=
  Strategy.toStrategy (G := MIPStarRE.QPBT.pauliBasisTest P)
    (Strategy.relabel S
      (pauliQuestionEquiv P) (pauliQuestionEquiv P)
      (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P))

/-- Conversion to the registered Pauli game preserves strategy value exactly. -/
theorem pauliStrategyToLibrary_value :
    (pauliStrategyToLibrary P S).value =
      S.value (pauliGame (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)
        (MIPStarRE.QPBT.fixedBinTrace P.model)) := by
  exact Strategy.value_toStrategy_relabel S (pauliGame_relabel_eq P)

end

/-- The compact Pauli game has the exact symmetric presentation transported from the source. -/
noncomputable def pauliSymmetricGame (P : MIPStarRE.QPBT.AdmissibleParams) :
    SymmetricGame
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :=
  SymmetricGame.relabel
    (SymmetricGame.ofSymmetricGame (MIPStarRE.QPBT.pauliBasisTestSymm P))
    (pauliQuestionEquiv P).symm (pauliAnswerEquivCompact P).symm

/-- The symmetric compact presentation has the compact Pauli game as its underlying game. -/
@[simp] theorem pauliSymmetricGame_toGame (P : MIPStarRE.QPBT.AdmissibleParams) :
    (pauliSymmetricGame P).toGame =
      pauliGame (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)
        (MIPStarRE.QPBT.fixedBinTrace P.model) := by
  change Game.relabel (Game.ofGame (QPBT.pauliBasisTest P))
    (pauliQuestionEquiv P).symm (pauliQuestionEquiv P).symm
    (pauliAnswerEquivCompact P).symm (pauliAnswerEquivCompact P).symm = _
  rw [← pauliGame_relabel_eq, Game.relabel_symm_relabel]

end

end MIPStarRE.QPBT.Palomar
