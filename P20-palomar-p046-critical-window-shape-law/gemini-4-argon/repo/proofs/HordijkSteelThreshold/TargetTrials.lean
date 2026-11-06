module

public import proofs.HordijkSteelThreshold.StaticSeedClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

theorem source_append_split {N : ℕ} (u v : List Bool)
    (hu : 0 < u.length) (hv : 0 < v.length) (hN : u.length + v.length ≤ N) :
    ∃ r : Reaction N,
      moleculeWord (reactionLeft r) = u ∧
      moleculeWord (reactionRight r) = v ∧
      moleculeWord (reactionProduct r) = u ++ v := by
  let x := sourceWordMolecule (u ++ v) (by simp; omega) (by simpa using hN)
  exact ⟨sourceSplitReaction x u.length hu (by simp [x]; omega),
    by simp [moleculeWord_reactionLeft, x], by simp [moleculeWord_reactionRight, x], by simp [x]⟩

theorem target_trial_support {N : ℕ} (w v : List Bool)
    (hw : 0 < w.length) (hv : 0 < v.length) (hN : w.length + v.length ≤ N) :
    ∃ S : Finset (Reaction N), S.card ≤ v.length + 1 ∧
      (∀ r ∈ S, w.length < molLength (reactionProduct r) ∧
        molLength (reactionProduct r) ≤ w.length + v.length) ∧
      ∀ T : Finset (Reaction N), S ⊆ T →
        ∀ x ∈ temporaryReactionClosure 2 T, moleculeWord x = w →
          ∃ y ∈ temporaryReactionClosure 2 T, moleculeWord y = v := by
  have happ (v : List Bool) (hN : w.length + v.length ≤ N) :
      ∃ S : Finset (Reaction N), S.card ≤ v.length ∧
        (∀ r ∈ S, w.length < molLength (reactionProduct r) ∧
          molLength (reactionProduct r) ≤ w.length + v.length) ∧
        ∀ T : Finset (Reaction N), S ⊆ T →
          ∀ x ∈ temporaryReactionClosure 2 T, moleculeWord x = w →
            ∃ y ∈ temporaryReactionClosure 2 T, moleculeWord y = w ++ v := by
    induction v using List.reverseRecOn with
    | nil => exact ⟨∅, by simp, by simp, fun _ _ x hx he => ⟨x, hx, by simpa using he⟩⟩
    | append_singleton v b ih =>
      obtain ⟨S, hcard, hband, hgen⟩ := ih (by simp at hN; omega)
      obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) (w ++ v) [b]
        (by simp; omega) (by simp) (by simpa [List.length_append, Nat.add_assoc] using hN)
      have hlen : molLength (reactionProduct r) = w.length + v.length + 1 := by
        rw [← moleculeWord_length, hp]; simp [Nat.add_assoc]
      refine ⟨insert r S, (Finset.card_insert_le r S).trans (by simp; omega), fun q hq => ?_, fun T hST x hx he => ?_⟩
      · rcases Finset.mem_insert.mp hq with rfl | hq
        · simp only [List.length_append, List.length_singleton]; omega
        · have := hband q hq; simp only [List.length_append, List.length_singleton]; omega
      · obtain ⟨y, hy, hey⟩ := hgen T (fun q hq => hST (Finset.mem_insert_of_mem hq)) x hx he
        exact ⟨reactionProduct r, temporaryReactionClosure_ligation T r
          (hST (Finset.mem_insert_self _ _)) (moleculeWord_injective (hl.trans hey.symm) ▸ hy)
          (temporaryReactionClosure_food T _ (by rw [← moleculeWord_length, hr]; simp)),
          by simpa [List.append_assoc] using hp⟩
  obtain ⟨S, hc, hb, hg⟩ := happ v hN
  obtain ⟨r, _, hr, hp⟩ := source_append_split (N := N) w v hw hv hN
  have hlen : molLength (reactionProduct r) = w.length + v.length := by
    rw [← moleculeWord_length, hp, List.length_append]
  refine ⟨insert r S, (Finset.card_insert_le r S).trans (by omega), fun q hq => ?_, fun T hST x hx he => ?_⟩
  · rcases Finset.mem_insert.mp hq with rfl | hq
    · omega
    · exact hb q hq
  · obtain ⟨y, hy, hey⟩ := hg T (fun q hq => hST (Finset.mem_insert_of_mem hq)) x hx he
    exact ⟨reactionRight r, (temporaryReactionClosure_cleavage T r
      (hST (Finset.mem_insert_self _ _)) (moleculeWord_injective (hp.trans hey.symm) ▸ hy)).2, hr⟩

end HordijkSteelThreshold
