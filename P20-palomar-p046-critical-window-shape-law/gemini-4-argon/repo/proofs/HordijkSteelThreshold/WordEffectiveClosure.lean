module

public import proofs.HordijkSteelThreshold.TemporaryReactionClosure
public import proofs.HordijkSteelThreshold.WordRootedMass

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

theorem literalFoodPath_generated_iff {N L : ℕ} {S T : Finset (Reaction N)} (hST : S ⊆ T)
    {u v : List Bool} (h : Relation.EqvGen (literalFoodEdge L S) u v) :
    contractedWordGenerated L T u ↔ contractedWordGenerated L T v := by
  induction h with
  | rel _ _ h =>
    obtain ⟨r, hr, hp, ⟨hl, he⟩ | ⟨hh, he⟩⟩ := h <;> rw [← hp, ← he, contractedWordGenerated_iff, contractedWordGenerated_iff]
    · exact ⟨fun h => (temporaryReactionClosure_cleavage T r (hST hr) h).2,
        fun h => temporaryReactionClosure_ligation T r (hST hr) (temporaryReactionClosure_food T _ hl) h⟩
    · exact ⟨fun h => (temporaryReactionClosure_cleavage T r (hST hr) h).1,
        fun h => temporaryReactionClosure_ligation T r (hST hr) h (temporaryReactionClosure_food T _ hh)⟩
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

noncomputable def staticOpenReactions {N : ℕ} (ω : Reaction N → Prop) : Finset (Reaction N) :=
  Finset.univ.filter ω

theorem wordEffective_reach_generated_iff {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) {u v : BoundedFoodWord L N}
    (h : indexedEdgeReach (wordEffectiveEdges hL ω) Prod.fst wordEdgeParent u v) :
    contractedWordGenerated L (staticOpenReactions ω) u.val ↔
      contractedWordGenerated L (staticOpenReactions ω) v.val := by
  induction h with
  | rel u v h =>
    obtain ⟨e, he, rfl, rfl⟩ := h
    obtain ⟨hb, j, hj⟩ := Finset.mem_filter.mp he
    have hn : e.1 ≠ boundedFoodRoot L N := (Finset.mem_filter.mp hb).2
    have hf := literalFoodPath_generated_iff (T := staticOpenReactions ω)
      (fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj r hr⟩)
      (wordDetourSource_reach_parent hL (e, j) hn)
    simpa only [wordShortStart, contractFoodWord, ite_eq_right (not_le.mpr (boundedFoodWord_nonroot_length e.1 hn))] using hf
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

noncomputable def actualWordSource {N : ℕ} (s : ActualBinaryWord N) : Molecule N :=
  sourceWordMolecule s.val (List.length_pos_iff.mpr ((mem_actualBinaryWords s.val N).mp s.property).1)
    ((mem_actualBinaryWords s.val N).mp s.property).2

theorem rootedMolecularWords_card_le_closure {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) :
    (rootedMolecularWords hL ω).card ≤ (temporaryReactionClosure L (staticOpenReactions ω)).card := by
  refine Finset.card_le_card_of_injOn actualWordSource (fun s hs => ?_)
    fun _ _ _ _ h => Subtype.ext (by simpa [actualWordSource, sourceWordMolecule_word] using congrArg moleculeWord h)
  have hg := (wordEffective_reach_generated_iff hL ω (Finset.mem_filter.mp hs).2).mp
    (contractedWordGenerated_root _)
  have hval : (molecularWordVertex L N s.val).val = contractFoodWord L s.val := by
    by_cases hL : s.val.length ≤ L
    · simp [molecularWordVertex_food s.val hL, contractFoodWord, hL, boundedFoodRoot]
    · simp [molecularWordVertex, not_le.mp hL, ((mem_actualBinaryWords s.val N).mp s.property).2, contractFoodWord, hL]
  rw [hval] at hg
  exact (contractedWordGenerated_iff (staticOpenReactions ω) (actualWordSource s)).mp
    (by simpa only [actualWordSource, sourceWordMolecule_word] using hg)

end HordijkSteelThreshold
