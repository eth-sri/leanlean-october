
import proofs.HordijkSteelThreshold.BasicSourceEdges
import proofs.HordijkSteelThreshold.WordDetourIncidence




namespace HordijkSteelThreshold

variable {n N : ℕ}
open RAF.Polymer RAF.Concrete

section
variable  (x : Molecule n) (k : ℕ) (hk : 0 < k) (hkm : k < molLength x)

/-- Arbitrary literal split, retaining its product and split-position identity. -/
def sourceSplitReaction  : Reaction n :=
  ⟨x.1, x.2, ⟨k - 1, by grind [molLength]⟩⟩



@[simp] theorem sourceSplitReaction_leftLength  :
    reactionLeftLength (sourceSplitReaction x k hk hkm) = k := by
  change k - 1 + 1 = k
  omega
end


/-- The side indicates deletion of a short suffix (true) or prefix (false). -/
def sourceShortSplit {n : ℕ} (x : Molecule n) (side : Bool) (k : ℕ)  :=
  if side then molLength x - k else k

section
variable  (x : Molecule n) (side : Bool) (k : ℕ) (hk : 0 < k) (hkm : k < molLength x)

def sourceShortReaction   :=
  sourceSplitReaction x (sourceShortSplit x side k)
    (by grind [sourceShortSplit])
    (by grind [sourceShortSplit])





@[simp] theorem sourceShortReaction_product  :
    reactionProduct (sourceShortReaction x side k hk hkm) = x := rfl

@[simp] theorem sourceShortReaction_leftLength  :
    reactionLeftLength (sourceShortReaction x side k hk hkm) =
      sourceShortSplit x side k := sourceSplitReaction_leftLength _ _ _ _
end





section
variable  (s : List Bool) (hs : 0 < s.length) (hN : s.length ≤ N)

def sourceWordMolecule   := moleculeOfCode hs hN (listWord s)

@[simp] theorem sourceWordMolecule_length  :
    molLength (sourceWordMolecule s hs hN) = s.length := by
  simp [sourceWordMolecule]

@[simp] theorem sourceWordMolecule_word  :
    moleculeWord (sourceWordMolecule s hs hN) = s := by
  apply binaryWordCode_injective_length
  · rw [moleculeWord_length, sourceWordMolecule_length]
  solve_by_elim [binaryWordCode_moleculeWord]
end


theorem boundedFoodWord_nonroot_length {L N : ℕ} (v : _)
    (hv : v ≠ boundedFoodRoot L N) : L < v.val.length := by
  grind [boundedFoodRoot]

section
variable {L w : ℕ} (hL : 2*w ≤ L)

/-- Literal source realization of each nonfood short key. Root keys produce no reaction. -/
noncomputable def wordShortSourceOption 
    (r : WordShortKey L N w)  :=
  if hr : r.1.1 = boundedFoodRoot L N then none else
    let x := sourceWordMolecule r.1.1.val
      (by grind [boundedFoodRoot])
      (boundedFoodWord_length_le r.1.1)
    some (sourceShortReaction x r.1.2 (r.2.val+1) (by omega)
      (by have h := boundedFoodWord_nonroot_length r.1.1 hr
          simp_all +zetaDelta ; omega))



variable (d : WordShortKey L N w)

noncomputable def wordDetourSourceReactions 
      :=
  (wordDetourKeys d).biUnion fun r => (wordShortSourceOption hL r).toFinset

theorem wordDetourSourceReactions_card 
     : (wordDetourSourceReactions hL d).card ≤ 2 := by
  refine (Finset.card_biUnion_le_card_mul _ _ 1 ?_).trans ?_
  · intro r _
    cases wordShortSourceOption hL r <;> simp
  · simpa using by
                  have hc : (wordDetourLower d).toFinset.card ≤ 1 := by
                    cases wordDetourLower d <;> simp
                  grind [wordDetourKeys]



end

end HordijkSteelThreshold
