module

public import proofs.HordijkSteelThreshold.BinaryWordCode
public import proofs.RAF.Concrete.PolymerCRS

@[expose] public section

namespace HordijkSteelThreshold

open RAF.Polymer RAF.Concrete

noncomputable def moleculeWord {n : ℕ} (x : Molecule n) : List Bool :=
  ((binaryListWordEquiv (molLength x)).symm x.2).val

theorem moleculeWord_length {n : ℕ} (x : Molecule n) :
    (moleculeWord x).length = molLength x :=
  ((binaryListWordEquiv (molLength x)).symm x.2).property

theorem binaryWordCode_moleculeWord {n : ℕ} (x : Molecule n) :
    binaryWordCode (moleculeWord x) = x.2.val := by
  exact congrArg Fin.val ((binaryListWordEquiv (molLength x)).apply_symm_apply x.2)

theorem moleculeWord_reactionLeft {n : ℕ} (r : Reaction n) :
    moleculeWord (reactionLeft r) =
      (moleculeWord (reactionProduct r)).take (reactionLeftLength r) := by
  let s := moleculeWord (reactionProduct r)
  have hlen : (moleculeWord (reactionProduct r)).length = reactionProductLength r := moleculeWord_length _
  have := reaction_length_add r
  refine binaryWordCode_injective_length
    (by rw [moleculeWord_length, molLength_reactionLeft, List.length_take_of_le (by omega)]) ?_
  have hc := binaryWordCode_append_div (s.take (reactionLeftLength r)) (s.drop (reactionLeftLength r))
  rw [List.take_append_drop, List.length_drop, hlen, show reactionProductLength r - reactionLeftLength r =
    reactionRightLength r by omega, binaryWordCode_moleculeWord] at hc
  exact (binaryWordCode_moleculeWord _).trans (hc : (reactionLeft r).2.val = _)

theorem moleculeWord_reactionRight {n : ℕ} (r : Reaction n) :
    moleculeWord (reactionRight r) =
      (moleculeWord (reactionProduct r)).drop (reactionLeftLength r) := by
  let s := moleculeWord (reactionProduct r)
  have hlen : (moleculeWord (reactionProduct r)).length = reactionProductLength r := moleculeWord_length _
  have := reaction_length_add r
  refine binaryWordCode_injective_length
    (by rw [moleculeWord_length, molLength_reactionRight, List.length_drop, hlen]; omega) ?_
  have hc := binaryWordCode_append_mod (s.take (reactionLeftLength r)) (s.drop (reactionLeftLength r))
  rw [List.take_append_drop, List.length_drop, hlen, show reactionProductLength r - reactionLeftLength r =
    reactionRightLength r by omega, binaryWordCode_moleculeWord] at hc
  exact (binaryWordCode_moleculeWord _).trans (hc : (reactionRight r).2.val = _)

end HordijkSteelThreshold
