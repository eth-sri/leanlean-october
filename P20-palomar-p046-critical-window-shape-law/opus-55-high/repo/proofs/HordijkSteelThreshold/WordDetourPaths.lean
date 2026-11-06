module

public import proofs.HordijkSteelThreshold.WordDetourIncidence
public import proofs.HordijkSteelThreshold.BasicSourceEdges

@[expose] public section

namespace HordijkSteelThreshold
open Classical

variable (s : List Bool) (side : Bool)

variable (k : ℕ)

def wordDropShort   : List Bool :=
  if side then s.take (s.length-k) else s.drop k

theorem wordDropShort_length   :
    (wordDropShort s side k).length = s.length-k := by
  cases side <;> simp [wordDropShort]


theorem wordDropShort_one  :
    wordDropShort s side 1 = if side then s.dropLast else s.tail := by
  cases side <;> simp [wordDropShort, List.dropLast_eq_take]

theorem wordDropShort_comp  (j : ℕ) :
    wordDropShort (wordDropShort s side 1) side j =
      wordDropShort s side (j+1) := by
  cases side
  · simp [wordDropShort]
  · simp only [wordDropShort, ↓reduceIte, List.length_take]
    grind


variable {L N : ℕ} (e : WordBasicEdge L N)

theorem contract_wordDropShort_one  :
    contractFoodWord L (wordDropShort e.1.val e.2 1) = (wordEdgeParent e).val := by
  rcases e with ⟨v, _ | _⟩ <;> rw [wordDropShort_one]
  exacts [contractFoodWord_tail L v.val, contractFoodWord_dropLast L v.val]

theorem wordEdgeParent_nonroot_word
    (h : wordEdgeParent e ≠ boundedFoodRoot L N) :
    (wordEdgeParent e).val = wordDropShort e.1.val e.2 1 := by
  have he := contract_wordDropShort_one e
  unfold contractFoodWord at he
  split_ifs at he
  · exact (h $ Subtype.ext he.symm).elim
  simp_all

theorem wordEdgeParent_root_length
    (h : wordEdgeParent e = boundedFoodRoot L N) : e.1.val.length ≤ L+1 := by
  have he := contract_wordDropShort_one e
  have := wordDropShort_length e.1.val e.2 1
  grind [contractFoodWord, boundedFoodRoot]


def wordShortStart {L N w : ℕ} (r : WordShortKey L N w) : List Bool :=
  contractFoodWord L r.1.1.val

def wordShortEnd {L N w : ℕ} (r : WordShortKey L N w) : List Bool :=
  contractFoodWord L $ wordDropShort r.1.1.val r.1.2 $ r.2.val+1

/-- Every detour is a genuine one- or two-edge path after food contraction.
No assertion of reaction openness or catalytic support is assumed here. -/
theorem wordDetourKeys_reach_parent {L N w : ℕ} (d : WordShortKey L N w) :
    indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd
      (wordShortStart d) (wordEdgeParent d.1).val := by
  have hd : d ∈ wordDetourKeys d := by simp [wordDetourKeys]
  have upper : indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd
      (wordShortStart d) (wordShortEnd d) :=
    Relation.EqvGen.rel _ _ ⟨d, hd, rfl, rfl⟩
  by_cases hj : d.2.val = 0
  · have he : wordShortEnd d = (wordEdgeParent d.1).val := by
      simpa only [wordShortEnd, hj] using contract_wordDropShort_one d.1
    simp_all
  · by_cases hp : wordEdgeParent d.1 = boundedFoodRoot L N
    · have hm := wordEdgeParent_root_length d.1 hp
      have := wordDropShort_length d.1.1.val d.1.2 $ d.2.val+1
      have he : wordShortEnd d = (wordEdgeParent d.1).val := by
        grind [wordShortEnd, contractFoodWord, boundedFoodRoot]
      simp_all
    · let r : WordShortKey L N w :=
        ((wordEdgeParent d.1, d.1.2), ⟨d.2.val-1, lt_of_le_of_lt (Nat.sub_le _ _) d.2.isLt⟩)
      have hlower : wordDetourLower d = some r := by
        simp only [wordDetourLower, hj, hp, or_self]
        rfl
      have hrs : wordShortStart r = (wordEdgeParent d.1).val := by
        grind [wordShortStart, contractFoodWord]
      have hre : wordShortEnd r = wordShortEnd d := by
        have hjr : d.2.val-1+1 = d.2.val := by omega
        change contractFoodWord L (wordDropShort (wordEdgeParent d.1).val d.1.2
          (d.2.val-1+1)) = wordShortEnd d
        rw [hjr, wordEdgeParent_nonroot_word d.1 hp, wordDropShort_comp]
        rfl
      exact upper.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨r, by simp [wordDetourKeys, hlower], hrs, hre⟩).symm

end HordijkSteelThreshold
