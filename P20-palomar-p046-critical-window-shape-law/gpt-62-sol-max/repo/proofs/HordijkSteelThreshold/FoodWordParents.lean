module

public import proofs.HordijkSteelThreshold.DiamondCutPotential

@[expose] public section

namespace HordijkSteelThreshold

/-- Empty list represents the contracted food root. Nonfood parents remove
one end bit; a parent reaching the food cutoff is sent to that root. -/
def foodWordLeft (L : ℕ) (s : List Bool) : List Bool :=
  if s.length ≤ L + 1 then [] else s.tail

def foodWordRight (L : ℕ) (s : List Bool) : List Bool :=
  if s.length ≤ L + 1 then [] else s.dropLast

def foodWordHeight (L : ℕ) (s : List Bool) : ℕ := s.length - L

theorem foodWordParents_commute (L : ℕ) (s : List Bool) :
    foodWordLeft L (foodWordRight L s) = foodWordRight L (foodWordLeft L s) := by
  by_cases h : s.length ≤ L + 1
  · simp [foodWordLeft, foodWordRight, h]
  · simp only [foodWordLeft, foodWordRight, ite_eq_right h, List.length_dropLast,
      List.length_tail]
    split_ifs <;> simp [List.tail_dropLast]

theorem foodWordRight_height (L : ℕ) (s : List Bool) :
    foodWordHeight L (foodWordRight L s) ≤ foodWordHeight L s - 1 := by
  simp only [foodWordHeight, foodWordRight]
  split_ifs <;> simp only [List.length_nil, List.length_dropLast] <;> omega

end HordijkSteelThreshold
