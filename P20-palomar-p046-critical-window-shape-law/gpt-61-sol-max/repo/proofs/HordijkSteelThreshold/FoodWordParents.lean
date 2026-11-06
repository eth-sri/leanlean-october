
import Mathlib.Tactic




namespace HordijkSteelThreshold

variable (L : ℕ) (s : List Bool)

/-- Empty list represents the contracted food root. Nonfood parents remove
one end bit; a parent reaching the food cutoff is sent to that root. -/
def foodWordLeft   :=
  if s.length ≤ L + 1 then [] else s.tail

def foodWordRight   :=
  if s.length ≤ L + 1 then [] else s.dropLast



end HordijkSteelThreshold
