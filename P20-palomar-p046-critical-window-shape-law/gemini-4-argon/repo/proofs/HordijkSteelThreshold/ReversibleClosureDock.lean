module

public import proofs.HordijkSteelThreshold.ReversibleFiniteCertificates
public import proofs.HordijkSteelThreshold.TargetTrials

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

noncomputable def restrictedSplitReactions (N : ℕ) (field : InfiniteSplitEnvironment) :
    Finset (Reaction N) := Finset.univ.filter
      (fun r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r))

theorem moleculeWord_nonempty {N : ℕ} (x : Molecule N) : moleculeWord x ≠ [] := by
  rw [← List.length_pos_iff, moleculeWord_length, molLength]; omega

theorem moleculeWord_cap {N : ℕ} (x : Molecule N) : (moleculeWord x).length ≤ N := by
  rw [moleculeWord_length, molLength]; have := x.1.isLt; omega

theorem reaction_words_append {N : ℕ} (r : Reaction N) :
    moleculeWord (reactionLeft r) ++ moleculeWord (reactionRight r) =
      moleculeWord (reactionProduct r) := by
  rw [moleculeWord_reactionLeft, moleculeWord_reactionRight, List.take_append_drop]

theorem literalClosure_to_finiteReversible {N L : ℕ} (field : InfiniteSplitEnvironment)
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure L (restrictedSplitReactions N field)) :
    FiniteReversibleGenerated N L field (moleculeWord x) := by
  refine temporaryReactionClosure_induction (restrictedSplitReactions N field)
    (fun y => FiniteReversibleGenerated N L field (moleculeWord y))
    (fun y hy => .food (moleculeWord_nonempty y) (by rwa [moleculeWord_length]) (moleculeWord_cap y))
    (fun r hr hl hh => ?_) (fun r hr hp => ?_) x hx
  · have ho := (Finset.mem_filter.mp hr).2
    rw [← reaction_words_append r] at ho ⊢
    exact .ligate hl hh (by simpa only [moleculeWord_length, molLength_reactionLeft] using ho)
      (reaction_words_append r ▸ moleculeWord_cap _)
  · have ho := (Finset.mem_filter.mp hr).2
    rw [← reaction_words_append r] at ho hp
    have hf : field (moleculeWord (reactionLeft r) ++ moleculeWord (reactionRight r))
        (moleculeWord (reactionLeft r)).length := by
      simpa only [moleculeWord_length, molLength_reactionLeft] using ho
    exact ⟨.left (moleculeWord_nonempty _) (moleculeWord_nonempty _) hp hf,
      .right (moleculeWord_nonempty _) (moleculeWord_nonempty _) hp hf⟩

theorem finiteReversible_to_literalClosure {N L : ℕ} {field : InfiniteSplitEnvironment}
    {w : List Bool} (hw : FiniteReversibleGenerated N L field w) :
    ∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions N field), moleculeWord x = w := by
  let S := restrictedSplitReactions N field
  have split_mem (u v : List Bool) (r : Reaction N)
      (hl : moleculeWord (reactionLeft r) = u)
      (hp : moleculeWord (reactionProduct r) = u ++ v) (ho : field (u ++ v) u.length) : r ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rwa [hp, ← molLength_reactionLeft, ← moleculeWord_length, hl]
  have cleave {u v} (hu : u ≠ []) (hv : v ≠ []) (ho : field (u ++ v) u.length)
      (ih : ∃ x ∈ temporaryReactionClosure L S, moleculeWord x = u ++ v) :
      (∃ x ∈ temporaryReactionClosure L S, moleculeWord x = u) ∧
      (∃ x ∈ temporaryReactionClosure L S, moleculeWord x = v) := by
    obtain ⟨x, hx, hxp⟩ := ih
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr hu) (List.length_pos_iff.mpr hv)
      (by rw [← List.length_append, ← hxp]; exact moleculeWord_cap x)
    have hc := temporaryReactionClosure_cleavage S r (split_mem u v r hl hp ho)
      (moleculeWord_injective (hp.trans hxp.symm) ▸ hx)
    exact ⟨⟨_, hc.1, hl⟩, ⟨_, hc.2, hr⟩⟩
  induction hw with
  | @food w hn hL hN =>
    exact ⟨_, temporaryReactionClosure_food S _ (by simpa using hL),
      sourceWordMolecule_word w (List.length_pos_iff.mpr hn) hN⟩
  | @ligate u v _ _ ho hN ihu ihv =>
    obtain ⟨x, hx, hxu⟩ := ihu
    obtain ⟨y, hy, hyv⟩ := ihv
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr (hxu ▸ moleculeWord_nonempty x))
      (List.length_pos_iff.mpr (hyv ▸ moleculeWord_nonempty y)) (by simpa using hN)
    exact ⟨_, temporaryReactionClosure_ligation S r (split_mem u v r hl hp ho)
      (moleculeWord_injective (hl.trans hxu.symm) ▸ hx)
      (moleculeWord_injective (hr.trans hyv.symm) ▸ hy), hp⟩
  | left hu hv _ ho ih => exact (cleave hu hv ho ih).1
  | right hu hv _ ho ih => exact (cleave hu hv ho ih).2

theorem finiteReversible_iff_literalClosure {N L : ℕ} (field : InfiniteSplitEnvironment)
    (w : List Bool) : FiniteReversibleGenerated N L field w ↔
      ∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions N field), moleculeWord x = w :=
  ⟨finiteReversible_to_literalClosure,
    fun ⟨x, hx, he⟩ => he ▸ literalClosure_to_finiteReversible field x hx⟩

end HordijkSteelThreshold
