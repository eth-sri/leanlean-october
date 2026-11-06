module

public import proofs.HordijkSteelThreshold.BinaryWordCode
public import proofs.RAF.Concrete.PolymerCRS

@[expose] public section

namespace HordijkSteelThreshold

open RAF.Polymer RAF.Concrete

variable {n : ℕ}

variable (x : Molecule n)

noncomputable def moleculeWord   : List Bool :=
  ((binaryListWordEquiv $ molLength x).symm x.2).val

theorem moleculeWord_length   :
    (moleculeWord x).length = molLength x :=
  ((binaryListWordEquiv $ molLength x).symm x.2).property

theorem binaryWordCode_moleculeWord   :
    binaryWordCode (moleculeWord x) = x.2.val := by
  exact congrArg Fin.val $ (binaryListWordEquiv $ molLength x).apply_symm_apply x.2


variable (r : Reaction n)

theorem reactionLeft_code_div   :
    (reactionLeft r).2.val = r.2.1.val / 2 ^ reactionRightLength r := by
  rfl

theorem reactionRight_code_mod   :
    (reactionRight r).2.val = r.2.1.val % 2 ^ reactionRightLength r := by
  rfl

/-- Decoding a literal source reaction gives exactly its recorded left
substring; split-position identities have not been quotiented. -/
theorem moleculeWord_reactionLeft   :
    moleculeWord (reactionLeft r) =
      (moleculeWord $ reactionProduct r).take (reactionLeftLength r) := by
  let s := moleculeWord $ reactionProduct r
  have hlen : s.length = reactionProductLength r := moleculeWord_length _
  have hdrop : (s.drop $ reactionLeftLength r).length = reactionRightLength r := by
    rw [List.length_drop]
    have h := reaction_length_add r
    omega
  apply binaryWordCode_injective_length
  · rw [moleculeWord_length, molLength_reactionLeft, List.length_take]
    rw [hlen, min_eq_left (by have h := reaction_length_add r; omega)]
  · rw [binaryWordCode_moleculeWord, reactionLeft_code_div]
    have hc := binaryWordCode_append_div (s.take $ reactionLeftLength r)
      (s.drop $ reactionLeftLength r)
    simp_all
    rw [show binaryWordCode s = r.2.1.val from binaryWordCode_moleculeWord _] at hc
    omega

/-- The right endpoint is exactly the complementary source substring. -/
theorem moleculeWord_reactionRight   :
    moleculeWord (reactionRight r) =
      (moleculeWord $ reactionProduct r).drop (reactionLeftLength r) := by
  let s := moleculeWord $ reactionProduct r
  have hdrop : (s.drop $ reactionLeftLength r).length = reactionRightLength r := by
    rw [List.length_drop, moleculeWord_length, molLength_reactionProduct]
    have h := reaction_length_add r
    omega
  apply binaryWordCode_injective_length
  · rw [moleculeWord_length, molLength_reactionRight]
    grind
  · rw [binaryWordCode_moleculeWord, reactionRight_code_mod]
    have hc := binaryWordCode_append_mod (s.take $ reactionLeftLength r)
      (s.drop $ reactionLeftLength r)
    simp_all
    rw [show binaryWordCode s = r.2.1.val from binaryWordCode_moleculeWord _] at hc
    omega

end HordijkSteelThreshold
