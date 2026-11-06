module

public import proofs.HordijkSteelThreshold.ShortSourceReactions
public import proofs.HordijkSteelThreshold.WordDetourIncidence

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

def sourceWordMolecule {N : ℕ} (s : List Bool) (hs : 0 < s.length)
    (hN : s.length ≤ N) : Molecule N := moleculeOfCode hs hN (listWord s)

@[simp] theorem sourceWordMolecule_length {N : ℕ} (s : List Bool)
    (hs : 0 < s.length) (hN : s.length ≤ N) :
    molLength (sourceWordMolecule s hs hN) = s.length := by
  simp [sourceWordMolecule]

@[simp] theorem sourceWordMolecule_word {N : ℕ} (s : List Bool)
    (hs : 0 < s.length) (hN : s.length ≤ N) :
    moleculeWord (sourceWordMolecule s hs hN) = s :=
  binaryWordCode_injective_length (by rw [moleculeWord_length, sourceWordMolecule_length])
    (by rw [binaryWordCode_moleculeWord]; rfl)

theorem boundedFoodWord_nonroot_length {L N : ℕ} (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) : L < v.val.length :=
  v.2.elim (fun h => (hv (Subtype.ext h)).elim) And.left

/-- Literal source realization of each nonfood short key. Root keys produce no reaction. -/
noncomputable def wordShortSourceOption {L N w : ℕ} (hL : 2*w ≤ L)
    (r : WordShortKey L N w) : Option (Reaction N) :=
  if hr : r.1.1 = boundedFoodRoot L N then none else
    let x := sourceWordMolecule r.1.1.val
      (by have := boundedFoodWord_nonroot_length r.1.1 hr; omega)
      (boundedFoodWord_length_le r.1.1)
    some (sourceShortReaction x r.1.2 (r.2.val+1) (by omega)
      (by have := boundedFoodWord_nonroot_length r.1.1 hr; have := r.2.isLt; simp only [x, sourceWordMolecule_length]; omega))

noncomputable def wordDetourSourceReactions {L N w : ℕ} (hL : 2*w ≤ L)
    (d : WordShortKey L N w) : Finset (Reaction N) :=
  (wordDetourKeys d).biUnion (fun r => (wordShortSourceOption hL r).toFinset)

theorem wordDetourSourceReactions_card {L N w : ℕ} (hL : 2*w ≤ L)
    (d : WordShortKey L N w) : (wordDetourSourceReactions hL d).card ≤ 2 := by
  refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum (g := fun _ => 1) fun r _ => ?_).trans ?_)
  · cases wordShortSourceOption hL r <;> simp
  · simpa using wordDetourKeys_card d

theorem wordDetourSourceReactions_incidence {L N w : ℕ} (hL : 2*w ≤ L)
    (a : Reaction N) :
    (Finset.univ.filter (fun d : WordShortKey L N w =>
      a ∈ wordDetourSourceReactions hL d)).card ≤ 3 := by
  by_cases ha : ∃ r : WordShortKey L N w, wordShortSourceOption hL r = some a
  · obtain ⟨r, hr⟩ := ha
    refine (Finset.card_le_card fun d hd => ?_).trans (wordDetourKeys_incidence r)
    obtain ⟨s, hs, hsa⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hd).2
    have hsr : s = r := by
      have hs' : wordShortSourceOption hL s = some a := Option.mem_toFinset.mp hsa
      unfold wordShortSourceOption at hs' hr
      split_ifs at hs' hr with hsn hrn
      have he := (Option.some.inj hs').trans (Option.some.inj hr).symm
      have := boundedFoodWord_nonroot_length s.1.1 hsn
      have := boundedFoodWord_nonroot_length r.1.1 hrn
      obtain ⟨hp, hb, hk⟩ := sourceShortReaction_coordinates (w := w) _ _ s.1.2 r.1.2
        (s.2.val+1) (r.2.val+1) (by omega) (by omega) (by omega) (by omega)
        (by simp; omega) (by simp; omega) he
      have hw := congrArg moleculeWord hp
      simp only [sourceWordMolecule_word] at hw
      exact Prod.ext (Prod.ext (Subtype.ext hw) hb) (Fin.ext (by omega))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsr ▸ hs⟩
  · rw [Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun d hd => ?_)]; omega
    obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hd).2
    exact ha ⟨r, Option.mem_toFinset.mp hr⟩

end HordijkSteelThreshold
