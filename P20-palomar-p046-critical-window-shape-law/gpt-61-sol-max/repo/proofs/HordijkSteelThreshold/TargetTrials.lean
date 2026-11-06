
import proofs.HordijkSteelThreshold.StaticSeedClosure
import proofs.RAFCriticalWindowQuantitative.FiniteClosure




namespace HordijkSteelThreshold
open RAF.Polymer RAF.Concrete

theorem source_append_split {N : ℕ} (u v : List Bool)
    (hu : 0 < u.length) (hv : 0 < v.length) (hN : u.length + v.length ≤ N) :
    ∃ r : Reaction N,
      moleculeWord (reactionLeft r) = u ∧
      moleculeWord (reactionRight r) = v ∧
      moleculeWord (reactionProduct r) = u ++ v := by
  let x := sourceWordMolecule (u ++ v) (by simp; omega) (by simpa using hN)
  let r := sourceSplitReaction x u.length hu (by simp [x]; omega)
  have hp : reactionProduct r = x := rfl
  refine ⟨r, ?_, ?_, ?_⟩ <;>
    simp [hp, r, moleculeWord_reactionLeft, moleculeWord_reactionRight, x]

end HordijkSteelThreshold
