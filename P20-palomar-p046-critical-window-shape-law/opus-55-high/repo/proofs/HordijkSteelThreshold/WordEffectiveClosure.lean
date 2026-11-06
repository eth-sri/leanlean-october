module

public import proofs.HordijkSteelThreshold.TemporaryReactionClosure
public import proofs.HordijkSteelThreshold.WordRootedMass

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

theorem literalFoodEdge_generated_iff {N L : ℕ} (S : Finset $ Reaction N)
    {u v : List Bool} (h : literalFoodEdge L S u v) :
    contractedWordGenerated L S u ↔ contractedWordGenerated L S v := by
  obtain ⟨r, hr, hp, hf⟩ := h
  rw [← hp, contractedWordGenerated_iff]
  rcases hf with ⟨hl, he⟩ | ⟨hh, he⟩ <;> rw [← he, contractedWordGenerated_iff] <;>
    grind [temporaryReactionClosure_cleavage, temporaryReactionClosure_ligation, temporaryReactionClosure_food]

theorem literalFoodPath_generated_iff {N L : ℕ} (S : Finset $ Reaction N)
    {u v : List Bool} (h : Relation.EqvGen (literalFoodEdge L S) u v) :
    contractedWordGenerated L S u ↔ contractedWordGenerated L S v :=
  (eqvGen_congr _ (fun _ _ h => propext $ literalFoodEdge_generated_iff S h) h).to_iff

theorem literalFoodPath_mono {N L : ℕ} {S T : Finset $ Reaction N} (hST : S ⊆ T)
    {u v : List Bool} (h : Relation.EqvGen (literalFoodEdge L S) u v) :
    Relation.EqvGen (literalFoodEdge L T) u v :=
  h.mono fun _ _ ⟨r, hr, hp, hf⟩ => ⟨r, hST hr, hp, hf⟩

variable {N : ℕ}

noncomputable def staticOpenReactions  (ω : Reaction N → Prop) : Finset (Reaction N) :=
  Finset.univ.filter ω

theorem wordEffective_generated_iff {L N w : ℕ} (hL : 2*w ≤ L) (ω : Reaction N → Prop)
    (e : WordBasicEdge L N) (he : e ∈ wordEffectiveEdges hL ω) :
    contractedWordGenerated L (staticOpenReactions ω) e.1.val ↔
      contractedWordGenerated L (staticOpenReactions ω) (wordEdgeParent e).val := by
  obtain ⟨hb, j, hj⟩ := Finset.mem_filter.mp he
  have hn := (Finset.mem_filter.mp hb).2
  have hp := wordDetourSource_reach_parent hL (e,j) hn
  have hf := literalFoodPath_generated_iff (staticOpenReactions ω)
    (literalFoodPath_mono (fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj r hr⟩) hp)
  have hlen := boundedFoodWord_nonroot_length e.1 hn
  simpa only [wordShortStart, contractFoodWord, ite_eq_right $ not_le.mpr hlen] using hf

theorem wordEffective_reach_generated_iff {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) {u v : BoundedFoodWord L N}
    (h : indexedEdgeReach (wordEffectiveEdges hL ω) Prod.fst wordEdgeParent u v) :
    contractedWordGenerated L (staticOpenReactions ω) u.val ↔
      contractedWordGenerated L (staticOpenReactions ω) v.val :=
  (eqvGen_congr (fun u : BoundedFoodWord L N => contractedWordGenerated L (staticOpenReactions ω) u.val)
    (fun _ _ ⟨e, he, hu, hv⟩ => hu ▸ hv ▸ propext (wordEffective_generated_iff hL ω e he)) h).to_iff

theorem molecularWordVertex_val {L N : ℕ} (s : List Bool) (hN : s.length ≤ N) :
    (molecularWordVertex L N s).val = contractFoodWord L s := by
  by_cases hL : s.length ≤ L
  · simp [molecularWordVertex_food s hL, contractFoodWord, hL, boundedFoodRoot]
  · simp [molecularWordVertex, not_le.mp hL, hN, contractFoodWord]

variable (s : ActualBinaryWord N)

noncomputable def actualWordSource   : Molecule N :=
  sourceWordMolecule s.val (List.length_pos_iff.mpr ((mem_actualBinaryWords s.val N).mp s.property).1)
    ((mem_actualBinaryWords s.val N).mp s.property).2

@[simp] theorem actualWordSource_word   :
    moleculeWord (actualWordSource s) = s.val := sourceWordMolecule_word _ _ _


theorem actualWordSource_injective  : Function.Injective (@actualWordSource N) :=
  fun s t h => Subtype.ext $ by simpa using congrArg moleculeWord h


/-- The rooted effective component really is contained in ordinary reversible
closure from temporary food, using only reactions open in this same field. -/
theorem rootedMolecularWords_source_mem {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) (s : ActualBinaryWord N) (hs : s ∈ rootedMolecularWords hL ω) :
    actualWordSource s ∈ temporaryReactionClosure L (staticOpenReactions ω) := by
  have hg := (wordEffective_reach_generated_iff hL ω (Finset.mem_filter.mp hs).2).mp
    (contractedWordGenerated_root _)
  rw [molecularWordVertex_val s.val ((mem_actualBinaryWords s.val N).mp s.property).2] at hg
  apply (contractedWordGenerated_iff (staticOpenReactions ω) $ actualWordSource s).mp
  simp_all

end HordijkSteelThreshold
