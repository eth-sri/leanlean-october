module

public import proofs.HordijkSteelThreshold.TerminalReactionClosure
public import proofs.HordijkSteelThreshold.PeelingStabilization
public import proofs.HordijkSteelThreshold.ScalarHistoryLaw

@[expose] public section

namespace RAFEmergenceApprox
open Classical RAF RAF.Polymer RAF.Concrete HordijkSteelThreshold

/-- Extraction needs nonemptiness, not growth beyond food. -/
theorem usable_isRAF {N L : ℕ} (A : Finset (Reaction N))
    (Cat : Catalysis (Molecule N) (Reaction N))
    (hcat : ∀ r ∈ A, ∃ x ∈ temporaryReactionClosure L A, Cat x r)
    (hne : (usableClosureReactions L A).Nonempty) :
    IsRevRAF (binaryPolymerCRS N L) Cat (usableClosureReactions L A) := by
  refine ⟨hne, ?_, ?_⟩
  · intro r hr
    have hh := (Finset.mem_filter.mp hr).2
    have he := usableClosureReactions_closure (L := L) A
    have hl : reactionLeft r ∈ temporaryReactionClosure L (usableClosureReactions L A) := by
      rw [he]; exact hh.1
    have hr' : reactionRight r ∈ temporaryReactionClosure L (usableClosureReactions L A) := by
      rw [he]; exact hh.2.1
    have hp : reactionProduct r ∈ temporaryReactionClosure L (usableClosureReactions L A) := by
      rw [he]; exact hh.2.2
    obtain ⟨kl,hkl⟩ := (mem_temporaryReactionClosure _ _).mp hl
    obtain ⟨kr,hkr⟩ := (mem_temporaryReactionClosure _ _).mp hr'
    obtain ⟨kp,hkp⟩ := (mem_temporaryReactionClosure _ _).mp hp
    have hlk := revClosureAt_mono_stage _ _ (Nat.le_max_left kl (max kr kp)) hkl
    have hrk := revClosureAt_mono_stage _ _
      ((Nat.le_max_left kr kp).trans (Nat.le_max_right kl (max kr kp))) hkr
    have hpk := revClosureAt_mono_stage _ _
      ((Nat.le_max_right kr kp).trans (Nat.le_max_right kl (max kr kp))) hkp
    refine ⟨max kl (max kr kp), ?_⟩
    intro y hy
    have hmem : y = reactionLeft r ∨ y = reactionRight r ∨ y = reactionProduct r := by
      simpa [binaryPolymerCRS] using hy
    rcases hmem with rfl | rfl | rfl
    · exact hlk
    · exact hrk
    · exact hpk
  · intro r hr
    obtain ⟨x,hx,hxr⟩ := hcat r (Finset.mem_filter.mp hr).1
    rw [← usableClosureReactions_closure A] at hx
    obtain ⟨k,hk⟩ := (mem_temporaryReactionClosure _ _).mp hx
    exact ⟨x,k,hk,hxr⟩

end RAFEmergenceApprox
