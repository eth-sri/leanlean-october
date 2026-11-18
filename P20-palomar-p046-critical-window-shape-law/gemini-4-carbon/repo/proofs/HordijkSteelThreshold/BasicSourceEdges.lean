module

public import proofs.HordijkSteelThreshold.BinaryReactionSplit
public import proofs.HordijkSteelThreshold.FoodWordParents

@[expose] public section

namespace HordijkSteelThreshold

open RAF.Polymer RAF.Concrete

def contractFoodWord (L : ℕ) (s : List Bool) : List Bool :=
  if s.length ≤ L then [] else s

theorem contractFoodWord_tail (L : ℕ) (s : List Bool) :
    contractFoodWord L s.tail = foodWordLeft L s := by
  have h : s.length - 1 ≤ L ↔ s.length ≤ L + 1 := by omega
  simp only [contractFoodWord, foodWordLeft, List.length_tail, h]

theorem contractFoodWord_dropLast (L : ℕ) (s : List Bool) :
    contractFoodWord L s.dropLast = foodWordRight L s := by
  have h : s.length - 1 ≤ L ↔ s.length ≤ L + 1 := by omega
  simp only [contractFoodWord, foodWordRight, List.length_dropLast, h]

end HordijkSteelThreshold
