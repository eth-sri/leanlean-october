module

public import proofs.HordijkSteelThreshold.StaticSeedClosure

public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

variable {N : ℕ}

theorem source_append_split  (u v : List Bool)
    (hu : 0 < u.length) (hv : 0 < v.length) (hN : u.length + v.length ≤ N) :
    ∃ r : Reaction N,
      moleculeWord (reactionLeft r) = u ∧
      moleculeWord (reactionRight r) = v ∧
      moleculeWord (reactionProduct r) = u ++ v := by
  let x := sourceWordMolecule (u ++ v) (by simp_all) $ by simpa using hN
  let r := sourceSplitReaction x u.length hu $ by aesop
  refine ⟨r, ?_, ?_, ?_⟩ <;> simp [r, x, moleculeWord_reactionLeft, moleculeWord_reactionRight]

/-- Appending a word needs at most one literal reaction per new letter.
The statement retains its cap and product-length band for disjoint trials. -/
theorem append_trial_support  (w v : List Bool)
    (hw : 0 < w.length) (hN : w.length + v.length ≤ N) :
    ∃ S : Finset $ Reaction N, S.card ≤ v.length ∧
      (∀ r ∈ S, w.length < molLength (reactionProduct r) ∧
        molLength (reactionProduct r) ≤ w.length + v.length) ∧
      ∀ T : Finset $ Reaction N, S ⊆ T →
        ∀ x ∈ temporaryReactionClosure 2 T, moleculeWord x = w →
          ∃ y ∈ temporaryReactionClosure 2 T, moleculeWord y = w ++ v := by
  induction v using List.reverseRecOn with
  | nil => exact ⟨∅, by simp, by simp, by grind⟩
  | append_singleton v b ih =>
    obtain ⟨S, hcard, hband, hgen⟩ := ih $ by grind
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) (w ++ v) [b]
      (by grind) (by simp) $ by grind
    have hlen : molLength (reactionProduct r) = w.length + v.length + 1 := by
      rw [← moleculeWord_length]
      grind
    refine ⟨insert r S, by grind, by grind, fun T hST x hx he => ?_⟩
    obtain ⟨y, hy, hey⟩ := hgen T (fun q hq => hST $ Finset.mem_insert_of_mem hq) x hx he
    have hleft := moleculeWord_injective $ hl.trans hey.symm
    have hright : molLength (reactionRight r) ≤ 2 := by rw [← moleculeWord_length, hr]; simp
    refine ⟨reactionProduct r, temporaryReactionClosure_ligation T r
      (hST $ Finset.mem_insert_self _ _) (hleft.symm ▸ hy)
      (temporaryReactionClosure_food T _ hright), ?_⟩
    grind

end HordijkSteelThreshold
