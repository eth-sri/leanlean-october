module

public import proofs.HordijkSteelThreshold.DiamondCutPotential

@[expose] public section

namespace HordijkSteelThreshold

variable (L : ℕ) (s : List Bool)

/-- Empty list represents the contracted food root. Nonfood parents remove
one end bit; a parent reaching the food cutoff is sent to that root. -/
def foodWordLeft  : List Bool :=
  if s.length ≤ L + 1 then [] else s.tail

def foodWordRight  : List Bool :=
  if s.length ≤ L + 1 then [] else s.dropLast

def foodWordHeight  : ℕ := s.length - L

theorem foodWordParents_commute  :
    foodWordLeft L (foodWordRight L s) = foodWordRight L (foodWordLeft L s) := by
  by_cases h : s.length ≤ L + 1
  · simp [foodWordLeft, foodWordRight, h]
  · simp only [foodWordLeft, foodWordRight, ite_eq_right h,
      List.length_tail]
    grind

theorem foodWordRight_height  :
    foodWordHeight L (foodWordRight L s) ≤ foodWordHeight L s - 1 := by
  simp only [foodWordHeight, foodWordRight]
  grind

end HordijkSteelThreshold
