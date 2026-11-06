module

public import proofs.HordijkSteelThreshold.StaticSeedClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF RAF.Polymer RAF.Concrete

noncomputable def usableClosureReactions {N : ℕ} (L : ℕ) (A : Finset (Reaction N)) :=
  A.filter (fun r => reactionLeft r ∈ temporaryReactionClosure L A ∧
    reactionRight r ∈ temporaryReactionClosure L A ∧
    reactionProduct r ∈ temporaryReactionClosure L A)

theorem usableClosureReactions_isRAF {N L : ℕ} (A : Finset (Reaction N))
    (Cat : Catalysis (Molecule N) (Reaction N))
    (hcat : ∀ r ∈ A, ∃ x ∈ temporaryReactionClosure L A, Cat x r)
    (hx : ∃ x ∈ temporaryReactionClosure L A, L < molLength x) :
    IsRevRAF (binaryPolymerCRS N L) Cat (usableClosureReactions L A) := by
  have hm := temporaryReactionClosure_mono (L := L) (Finset.filter_subset _ A : usableClosureReactions L A ⊆ A)
  have hcl : temporaryReactionClosure L (usableClosureReactions L A) = temporaryReactionClosure L A :=
    Finset.Subset.antisymm hm fun x hx =>
      temporaryReactionClosure_induction A
        (fun y => y ∈ temporaryReactionClosure L (usableClosureReactions L A))
        (temporaryReactionClosure_food _)
        (fun r hr hl hh => temporaryReactionClosure_ligation _ r
          (Finset.mem_filter.mpr ⟨hr, hm hl, hm hh, temporaryReactionClosure_ligation A r hr (hm hl) (hm hh)⟩) hl hh)
        (fun r hr hp => by
          have hh := temporaryReactionClosure_cleavage A r hr (hm hp)
          exact temporaryReactionClosure_cleavage _ r (Finset.mem_filter.mpr ⟨hr, hh.1, hh.2, hm hp⟩) hp) x hx
  refine ⟨?_, fun r hr => ?_, fun r hr => ?_⟩
  · obtain ⟨x, hx, hxl⟩ := hx
    rw [← hcl] at hx; by_contra! he
    exact hxl.not_ge <| temporaryReactionClosure_induction (usableClosureReactions L A)
      (fun y => molLength y ≤ L) (fun _ h => h) (by simp [he]) (by simp [he]) x hx
  · have hh := (Finset.mem_filter.mp hr).2
    simp_rw [← hcl, mem_temporaryReactionClosure] at hh
    obtain ⟨⟨kl, hkl⟩, ⟨kr, hkr⟩, ⟨kp, hkp⟩⟩ := hh
    refine ⟨max kl (max kr kp), fun y hy => ?_⟩
    rcases (by simpa [binaryPolymerCRS] using hy :
        y = reactionLeft r ∨ y = reactionRight r ∨ y = reactionProduct r) with rfl | rfl | rfl
    · exact revClosureAt_mono_stage _ _ (by omega) hkl
    · exact revClosureAt_mono_stage _ _ (by omega) hkr
    · exact revClosureAt_mono_stage _ _ (by omega) hkp
  · obtain ⟨x, hx, hxr⟩ := hcat r (Finset.mem_filter.mp hr).1
    rw [← hcl, mem_temporaryReactionClosure] at hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨x, k, hk, hxr⟩

end HordijkSteelThreshold
