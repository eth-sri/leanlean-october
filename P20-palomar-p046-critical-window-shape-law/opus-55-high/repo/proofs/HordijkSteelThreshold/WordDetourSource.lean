module

public import proofs.HordijkSteelThreshold.ShortSourceReactions
public import proofs.HordijkSteelThreshold.WordDetourIncidence

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

section
variable {N : ℕ} (s : List Bool) (hs : 0 < s.length) (hN : s.length ≤ N)

def sourceWordMolecule  : Molecule N := moleculeOfCode hs hN $ listWord s

@[simp] theorem sourceWordMolecule_length  :
    molLength (sourceWordMolecule s hs hN) = s.length := by
  simp [sourceWordMolecule]

@[simp] theorem sourceWordMolecule_word  :
    moleculeWord (sourceWordMolecule s hs hN) = s := by
  apply binaryWordCode_injective_length
  · rw [moleculeWord_length, sourceWordMolecule_length]
  · rw [binaryWordCode_moleculeWord]
    rfl

end

theorem boundedFoodWord_nonroot_length {L N : ℕ} (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) : L < v.val.length := by
  rcases v.property with h | h
  · exact False.elim $ hv $ Subtype.ext h
  omega

/-- Literal source realization of each nonfood short key. Root keys produce no reaction. -/
noncomputable def wordShortSourceOption {L N w : ℕ} (hL : 2*w ≤ L)
    (r : WordShortKey L N w) : Option (Reaction N) :=
  if hr : r.1.1 = boundedFoodRoot L N then none else
    let x := sourceWordMolecule r.1.1.val
      (by have h := boundedFoodWord_nonroot_length r.1.1 hr; omega)
      (boundedFoodWord_length_le r.1.1)
    some $ sourceShortReaction x r.1.2 (r.2.val+1) (by omega)
      (by have h := boundedFoodWord_nonroot_length r.1.1 hr
          have hj := r.2.isLt
          simp only [x, sourceWordMolecule_length]
          omega)

theorem wordShortSourceOption_injective {L N w : ℕ} (hL : 2*w ≤ L)
    (r s : WordShortKey L N w) (a : Reaction N)
    (hr : wordShortSourceOption hL r = some a)
    (hs : wordShortSourceOption hL s = some a) : r = s := by
  unfold wordShortSourceOption at hr hs
  split_ifs at hr hs with hrn hsn
  have hsl := boundedFoodWord_nonroot_length s.1.1 hsn
  have he := (Option.some.inj hr).trans (Option.some.inj hs).symm
  have hw := congrArg (moleculeWord ∘ reactionProduct) he
  have hl := congrArg reactionLeftLength he
  simp only [Function.comp, sourceShortReaction_product, sourceWordMolecule_word, sourceShortReaction_leftLength,
    sourceShortSplit] at hw hl
  refine Prod.ext (Prod.ext (Subtype.ext hw) ?_) (Fin.ext ?_) <;> revert hl <;>
    cases r.1.2 <;> cases s.1.2 <;> simp_all <;> omega

noncomputable def wordDetourSourceReactions {L N w : ℕ} (hL : 2*w ≤ L)
    (d : WordShortKey L N w) : Finset (Reaction N) :=
  (wordDetourKeys d).biUnion $ fun r => (wordShortSourceOption hL r).toFinset

theorem wordDetourSourceReactions_card {L N w : ℕ} (hL : 2*w ≤ L)
    (d : WordShortKey L N w) : (wordDetourSourceReactions hL d).card ≤ 2 :=
  Finset.card_biUnion_le.trans $ (Finset.sum_le_card_nsmul _ _ 1 fun r _ => by
    cases wordShortSourceOption hL r <;> simp).trans $ by simpa using wordDetourKeys_card d

/-- The actual source ID overlap bound, without an independence assumption on
basic edges or a quotient of coincident reaction IDs. -/
theorem wordDetourSourceReactions_incidence {L N w : ℕ} (hL : 2*w ≤ L)
    (a : Reaction N) :
    (Finset.univ.filter (fun d : WordShortKey L N w =>
      a ∈ wordDetourSourceReactions hL d)).card ≤ 3 := by
  by_cases ha : ∃ r : WordShortKey L N w, wordShortSourceOption hL r = some a
  · obtain ⟨r, hr⟩ := ha
    refine (Finset.card_le_card fun d hd => ?_).trans $ wordDetourKeys_incidence r
    obtain ⟨s, hs, hsa⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hd).2
    simp_all [wordShortSourceOption_injective hL s r a (Option.mem_toFinset.mp hsa) hr]
  · simp_all [wordDetourSourceReactions]

end HordijkSteelThreshold
