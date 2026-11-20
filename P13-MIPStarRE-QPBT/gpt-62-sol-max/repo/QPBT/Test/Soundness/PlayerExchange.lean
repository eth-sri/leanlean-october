module

public import QPBT.Test.SoundnessDefs
public import QPBT.Test.PauliSymmetry
public import QPBT.Games.StrategyExchange

/-! Transport of the ideal state and Pauli distances under player exchange. -/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus

section

variable {P : AdmissibleParams} {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
include P I J

/-- The ideal state with the players exchanged has the exchanged residual state. -/
theorem idealState_prodComm
    (ξ : EuclideanSpace ℂ (I × J)) :
    idealState P (reindexState (Equiv.prodComm I J) ξ) =
      reindexState (Equiv.prodComm _ _) (idealState P ξ) := by
  ext p
  simp [idealState, reindexState, eprState, eq_comm]

private theorem norm_pauli_action_prodComm
    (aux : EuclideanSpace ℂ (I × J)) (A : Op (J × PauliRegister P))
    (W : PauliKind) (u : PauliRegister P) :
    ‖applyOperatorToState (heteroKron A 1 - pauliProjOnA'' P W u)
      (idealState P (reindexState (Equiv.prodComm I J) aux))‖ =
    ‖applyOperatorToState (heteroKron 1 A - pauliProjOnB'' P W u) (idealState P aux)‖ := by
  rw [idealState_prodComm, norm_applyOperatorToState_reindexState, reindexOp_sub,
    pauliProjOnA'', reindexOp_prodComm_heteroKron, reindexOp_prodComm_heteroKron]
  rfl

end

variable {P : AdmissibleParams} {S : Strategy (pauliBasisTest P)}

section

variable (w : PauliSoundnessWitness P S)
include w

/-- Exchange the local isometries and auxiliary factors of a soundness witness. -/
@[reducible] noncomputable def PauliSoundnessWitness.swap (w : PauliSoundnessWitness P S) :
    PauliSoundnessWitness P ((pauliBasisTestSymm P).swapStrategy S) where
  ιA' := w.ιB'
  ιB' := w.ιA'
  ιAFintype := w.ιBFintype
  ιBFintype := w.ιAFintype
  ιADecidableEq := w.ιBDecidableEq
  ιBDecidableEq := w.ιADecidableEq
  φA := w.φB
  φB := w.φA
  aux := reindexState (Equiv.prodComm _ _) w.aux
  aux_norm := (reindexState_norm_eq _ _).trans w.aux_norm

/-- The state error is invariant under exchanging the two players. -/
theorem PauliSoundnessWitness.swap_state_error :
    ‖isometryTensor w.swap.φA w.swap.φB ((pauliBasisTestSymm P).swapStrategy S).ψ -
        idealState P w.swap.aux‖ =
      ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ := by
  change ‖isometryTensor w.φB w.φA (reindexState (Equiv.prodComm _ _) S.ψ) -
    idealState P (reindexState (Equiv.prodComm _ _) w.aux)‖ = _
  rw [idealState_prodComm, isometryTensor_prodComm, norm_reindexState_sub_eq]

/-- Exchanging players sends Alice's completed Pauli comparison to Bob's. -/
theorem PauliSoundnessWitness.swap_completed_distance
    (W : PauliKind) :
    pauliOperatorDistanceA P ((pauliBasisTestSymm P).swapStrategy S) w.swap W =
      pauliOperatorDistanceB P S w W := by
  exact Finset.sum_congr rfl fun u _ => congrArg (· ^ 2) (norm_pauli_action_prodComm w.aux _ W u)

/-- The same exchange applies to the raw prescribed effects. -/
theorem PauliSoundnessWitness.swap_raw_distance
    (W : PauliKind) :
    rawPauliOperatorDistanceA P ((pauliBasisTestSymm P).swapStrategy S) w.swap W =
      rawPauliOperatorDistanceB P S w W := by
  exact Finset.sum_congr rfl fun u _ => congrArg (· ^ 2) (norm_pauli_action_prodComm w.aux _ W u)

end

end MIPStarRE.QPBT
