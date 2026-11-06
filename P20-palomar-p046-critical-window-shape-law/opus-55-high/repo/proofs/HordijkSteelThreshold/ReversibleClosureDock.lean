module

public import proofs.HordijkSteelThreshold.ReversibleFiniteCertificates
public import proofs.HordijkSteelThreshold.TargetTrials

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

noncomputable def restrictedSplitReactions (N : ℕ) (field : InfiniteSplitEnvironment) :
    Finset (Reaction N) := Finset.univ.filter
      (fun r => field (moleculeWord $ reactionProduct r) $ reactionLeftLength r)

variable {N : ℕ}

variable (x : Molecule N)

theorem moleculeWord_nonempty   : moleculeWord x ≠ [] :=
  fun he => by simpa [he, molLength] using moleculeWord_length x

theorem moleculeWord_cap   : (moleculeWord x).length ≤ N :=
  moleculeWord_length x ▸ x.1.isLt


theorem reaction_words_append  (r : Reaction N) :
    moleculeWord (reactionLeft r) ++ moleculeWord (reactionRight r) =
      moleculeWord (reactionProduct r) := by
  rw [moleculeWord_reactionLeft, moleculeWord_reactionRight, List.take_append_drop]


theorem literalClosure_to_finiteReversible {N L : ℕ} (field : InfiniteSplitEnvironment)
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure L (restrictedSplitReactions N field)) :
    FiniteReversibleGenerated N L field (moleculeWord x) := by
  have hf r (hr : r ∈ restrictedSplitReactions N field) : field (moleculeWord (reactionLeft r) ++
      moleculeWord (reactionRight r)) (moleculeWord $ reactionLeft r).length := by
    simpa [reaction_words_append, moleculeWord_length] using (Finset.mem_filter.mp hr).2
  apply temporaryReactionClosure_induction (restrictedSplitReactions N field)
    (FiniteReversibleGenerated N L field $ moleculeWord ·) ?_ ?_ ?_ x hx
  · exact fun y hy => .food (moleculeWord_nonempty y) (by rwa [moleculeWord_length]) $ moleculeWord_cap y
  · intro r hr hl hh
    rw [← reaction_words_append r]
    exact .ligate hl hh (hf r hr) $ reaction_words_append r ▸ moleculeWord_cap _
  · intro r hr hp
    rw [← reaction_words_append r] at hp
    exact ⟨.left (moleculeWord_nonempty _) (moleculeWord_nonempty _) hp $ hf r hr,
      .right (moleculeWord_nonempty _) (moleculeWord_nonempty _) hp $ hf r hr⟩

theorem finiteReversible_to_literalClosure {N L : ℕ} {field : InfiniteSplitEnvironment}
    {w : List Bool} (hw : FiniteReversibleGenerated N L field w) :
    ∃ x ∈ temporaryReactionClosure L $ restrictedSplitReactions N field, moleculeWord x = w := by
  let S := restrictedSplitReactions N field
  have split_mem (u v) r
      (hl : moleculeWord (reactionLeft r) = u)
      (hp : moleculeWord (reactionProduct r) = u ++ v) (ho : field (u ++ v) u.length) : r ∈ S := by
    have hk : reactionLeftLength r = u.length := by
      rw [← molLength_reactionLeft, ← moleculeWord_length, hl]
    simp_all [S, restrictedSplitReactions]
  induction hw with
  | @food w hn hL hN =>
    let x := sourceWordMolecule w (List.length_pos_iff.mpr hn) hN
    exact ⟨x, temporaryReactionClosure_food S x $ by aesop,
      sourceWordMolecule_word _ _ _⟩
  | @ligate u v _ _ ho hN ihu ihv =>
    obtain ⟨x, hx, hxu⟩ := ihu
    obtain ⟨y, hy, hyv⟩ := ihv
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr $ hxu ▸ moleculeWord_nonempty x)
      (List.length_pos_iff.mpr $ hyv ▸ moleculeWord_nonempty y) $ by simp_all
    have heL := moleculeWord_injective $ hl.trans hxu.symm
    have heR := moleculeWord_injective $ hr.trans hyv.symm
    exact ⟨reactionProduct r, temporaryReactionClosure_ligation S r (split_mem u v r hl hp ho)
      (heL.symm ▸ hx) $ heR.symm ▸ hy, hp⟩
  | @left u v hu hv _ ho ih | @right u v hu hv _ ho ih =>
    obtain ⟨x, hx, hxp⟩ := ih
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr hu) (List.length_pos_iff.mpr hv)
      (by rw [← List.length_append, ← hxp]; exact moleculeWord_cap x)
    have h := temporaryReactionClosure_cleavage S r (split_mem u v r hl hp ho)
      (moleculeWord_injective (hp.trans hxp.symm) ▸ hx)
    grind

theorem finiteReversible_iff_literalClosure {N L : ℕ} (field : InfiniteSplitEnvironment)
    (w : List Bool) : FiniteReversibleGenerated N L field w ↔
      ∃ x ∈ temporaryReactionClosure L $ restrictedSplitReactions N field, moleculeWord x = w :=
  ⟨finiteReversible_to_literalClosure,
    fun ⟨x, hx, he⟩ => he ▸ literalClosure_to_finiteReversible field x hx⟩

end HordijkSteelThreshold
