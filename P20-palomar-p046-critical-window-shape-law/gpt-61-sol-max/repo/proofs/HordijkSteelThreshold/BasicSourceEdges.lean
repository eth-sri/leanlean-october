
import proofs.HordijkSteelThreshold.BinaryWordCode
import proofs.RAF.Concrete.PolymerCRS
import proofs.HordijkSteelThreshold.FoodWordParents




namespace HordijkSteelThreshold

variable {n : ℕ}
open RAF.Polymer RAF.Concrete

variable  (x : Molecule n)

noncomputable def moleculeWord   :=
  ((binaryListWordEquiv (molLength x)).symm x.2).val

theorem moleculeWord_length  :
    (moleculeWord x).length = molLength x :=
  ((binaryListWordEquiv (molLength x)).symm x.2).property

theorem binaryWordCode_moleculeWord  :
    binaryWordCode (moleculeWord x) = x.2.val := congrArg Fin.val ((binaryListWordEquiv (molLength x)).apply_symm_apply x.2)

variable  (r : Reaction n)





/-- Decoding a literal source reaction gives exactly its recorded left
substring; split-position identities have not been quotiented. -/
theorem moleculeWord_reactionLeft  :
    moleculeWord (reactionLeft r) =
      (moleculeWord (reactionProduct r)).take (reactionLeftLength r) := by
  let z0 := reactionLeftLength r
  let s := moleculeWord (reactionProduct r)
  have hlen : s.length = reactionProductLength r := moleculeWord_length _
  have hdrop : (s.drop z0).length = reactionRightLength r := by grind [reaction_length_add, moleculeWord_length, molLength_reactionProduct]
  apply binaryWordCode_injective_length
  · rw [moleculeWord_length, molLength_reactionLeft, List.length_take]
    
    grind [reactionRightLength]
  · rw [binaryWordCode_moleculeWord]
    have hc := binaryWordCode_append_div (s.take z0)
      (s.drop z0)
    simp_all [s, binaryWordCode_moleculeWord]
    exact hc

/-- The right endpoint is exactly the complementary source substring. -/
theorem moleculeWord_reactionRight  :
    moleculeWord (reactionRight r) =
      (moleculeWord (reactionProduct r)).drop (reactionLeftLength r) := by
  let z0 := reactionLeftLength r
  let s := moleculeWord (reactionProduct r)
  have hdrop : (s.drop z0).length = reactionRightLength r := by
    grind [reaction_length_add, moleculeWord_length, molLength_reactionProduct]
  apply binaryWordCode_injective_length
  · rw [moleculeWord_length, molLength_reactionRight]
    exact hdrop.symm
  · rw [binaryWordCode_moleculeWord]
    have hc := binaryWordCode_append_mod (s.take z0)
      (s.drop z0)
    simp_all [s, binaryWordCode_moleculeWord]
    exact hc

variable (L : ℕ) (s : List Bool)

def contractFoodWord   :=
  if s.length ≤ L then [] else s


end HordijkSteelThreshold
