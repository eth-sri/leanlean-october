module

public import proofs.HordijkSteelThreshold.StaticSeedClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF RAF.Polymer RAF.Concrete

noncomputable def usableClosureReactions {N : ℕ} (L : ℕ) (A : Finset $ Reaction N) :=
  A.filter $ fun r => reactionLeft r ∈ temporaryReactionClosure L A ∧
    reactionRight r ∈ temporaryReactionClosure L A ∧
    reactionProduct r ∈ temporaryReactionClosure L A

variable {N L : ℕ} (A : Finset $ Reaction N)

/-- Removing reactions whose endpoints are unavailable does not remove any
actual generation step. Both reversible directions are retained. -/
theorem usableClosureReactions_closure  :
    temporaryReactionClosure L (usableClosureReactions L A) = temporaryReactionClosure L A := by
  have hm := temporaryReactionClosure_mono (L := L) (Finset.filter_subset _ A : usableClosureReactions L A ⊆ A)
  refine hm.antisymm fun x hx => temporaryReactionClosure_induction A _
    (temporaryReactionClosure_food _) (fun r hr hl hh => temporaryReactionClosure_ligation _ r
      (Finset.mem_filter.mpr ⟨hr, hm hl, hm hh, temporaryReactionClosure_ligation A r hr (hm hl) $ hm hh⟩)
      hl hh) (fun r hr hp => ?_) x hx
  have hh := temporaryReactionClosure_cleavage A r hr $ hm hp
  exact temporaryReactionClosure_cleavage _ r (Finset.mem_filter.mpr ⟨hr, hh.1, hh.2, hm hp⟩) hp

theorem usableClosureReactions_nonempty
    (hx : ∃ x ∈ temporaryReactionClosure L A, L < molLength x) :
    (usableClosureReactions L A).Nonempty := by
  obtain ⟨x,hx,hxl⟩ := hx
  rw [← usableClosureReactions_closure A] at hx
  by_contra he
  have := temporaryReactionClosure_induction (usableClosureReactions L A)
    (molLength · ≤ L) (fun _ h => h) (by simp_all) (by simp_all) x hx
  omega

/-- Internally catalyzed active reactions yield a literal RAF after removal of
unavailable reactions, provided their closure contains a nonfood molecule. -/
theorem usableClosureReactions_isRAF
    (Cat : Catalysis (Molecule N) $ Reaction N)
    (hcat : ∀ r ∈ A, ∃ x ∈ temporaryReactionClosure L A, Cat x r)
    (hx : ∃ x ∈ temporaryReactionClosure L A, L < molLength x) :
    IsRevRAF (binaryPolymerCRS N L) Cat (usableClosureReactions L A) := by
  refine ⟨usableClosureReactions_nonempty A hx, ?_, ?_⟩
  · intro r hr
    have hh := (Finset.mem_filter.mp hr).2
    rw [← usableClosureReactions_closure A] at hh
    simp at hh
    obtain ⟨⟨kl,hkl⟩,⟨kr,hkr⟩,⟨kp,hkp⟩⟩ := hh
    have := revClosureAt_mono_stage _ _ (by omega : kl ≤ max kl (max kr kp)) hkl
    have := revClosureAt_mono_stage _ _ (by omega : kr ≤ max kl (max kr kp)) hkr
    have := revClosureAt_mono_stage _ _ (by omega : kp ≤ max kl (max kr kp)) hkp
    refine ⟨max kl $ max kr kp, fun y hy => ?_⟩
    simp [binaryPolymerCRS] at hy
    grind
  · intro r hr
    obtain ⟨x,hx,hxr⟩ := hcat r (Finset.mem_filter.mp hr).1
    rw [← usableClosureReactions_closure A] at hx
    obtain ⟨k,hk⟩ := (mem_temporaryReactionClosure _ _).mp hx
    tauto

end HordijkSteelThreshold
