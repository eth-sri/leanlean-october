module

public import proofs.HordijkSteelThreshold.WordDetourIncidence
public import proofs.HordijkSteelThreshold.BasicSourceEdges

@[expose] public section

namespace HordijkSteelThreshold
open Classical

def wordDropShort (s : List Bool) (side : Bool) (k : ℕ) : List Bool :=
  if side then s.take (s.length-k) else s.drop k

theorem wordDropShort_length (s : List Bool) (side : Bool) (k : ℕ) :
    (wordDropShort s side k).length = s.length-k := by
  cases side <;> simp [wordDropShort]

theorem contract_wordDropShort_one {L N : ℕ} (e : WordBasicEdge L N) :
    contractFoodWord L (wordDropShort e.1.val e.2 1) = (wordEdgeParent e).val := by
  rcases e with ⟨v, side⟩
  cases side
  · simpa [wordDropShort, wordEdgeParent, boundedFoodLeft] using contractFoodWord_tail L v.val
  · simpa [wordDropShort, List.dropLast_eq_take, wordEdgeParent, boundedFoodRight] using contractFoodWord_dropLast L v.val

def wordShortStart {L N w : ℕ} (r : WordShortKey L N w) : List Bool :=
  contractFoodWord L r.1.1.val

def wordShortEnd {L N w : ℕ} (r : WordShortKey L N w) : List Bool :=
  contractFoodWord L (wordDropShort r.1.1.val r.1.2 (r.2.val+1))

theorem wordDetourKeys_reach_parent {L N w : ℕ} (d : WordShortKey L N w) :
    indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd
      (wordShortStart d) (wordEdgeParent d.1).val := by
  have upper : indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd
      (wordShortStart d) (wordShortEnd d) :=
    .rel _ _ ⟨d, by simp [wordDetourKeys], rfl, rfl⟩
  have he1 := contract_wordDropShort_one d.1
  by_cases hj : d.2.val = 0
  · exact (by simpa only [wordShortEnd, hj, zero_add] using he1 :
      wordShortEnd d = (wordEdgeParent d.1).val) ▸ upper
  · by_cases hp : wordEdgeParent d.1 = boundedFoodRoot L N
    · rw [hp] at he1
      change contractFoodWord L (wordDropShort d.1.1.val d.1.2 1) = [] at he1
      unfold contractFoodWord at he1
      have hm : d.1.1.val.length ≤ L + 1 := by
        split_ifs at he1 with hs
        · rw [wordDropShort_length] at hs; omega
        · have hz := congrArg List.length he1
          simp [wordDropShort_length] at hz hs; omega
      have he : wordShortEnd d = (wordEdgeParent d.1).val := by
        rw [hp]; exact ite_eq_left (by rw [wordDropShort_length]; omega)
      exact he ▸ upper
    · let r : WordShortKey L N w :=
        ((wordEdgeParent d.1, d.1.2), ⟨d.2.val-1, lt_of_le_of_lt (Nat.sub_le _ _) d.2.isLt⟩)
      have hlower : wordDetourLower d = some r := by simp [wordDetourLower, hj, hp]; rfl
      have hrs : wordShortStart r = (wordEdgeParent d.1).val :=
        ite_eq_right fun (hh : (wordEdgeParent d.1).1.length ≤ L) =>
          (wordEdgeParent d.1).2.elim (fun h => hp (Subtype.ext h)) (by omega)
      have hpw : (wordEdgeParent d.1).val = wordDropShort d.1.1.val d.1.2 1 := by
        unfold contractFoodWord at he1
        split_ifs at he1 with hs
        · exact (hp (Subtype.ext he1.symm)).elim
        · exact he1.symm
      have hcomp (s : List Bool) (side : Bool) (j : ℕ) :
          wordDropShort (wordDropShort s side 1) side j = wordDropShort s side (j+1) := by
        cases side
        · simp [wordDropShort]
        · simp only [wordDropShort, ↓reduceIte, List.length_take, List.take_take]; congr 1; omega
      have hre : wordShortEnd r = wordShortEnd d := by
        change contractFoodWord L (wordDropShort (wordEdgeParent d.1).val d.1.2 (d.2.val-1+1)) = _
        rw [Nat.sub_add_cancel (by omega), hpw, hcomp]
        rfl
      exact .trans _ _ _ upper (.symm _ _ (.rel _ _ ⟨r, by simp [wordDetourKeys, hlower], hrs, hre⟩))

end HordijkSteelThreshold
