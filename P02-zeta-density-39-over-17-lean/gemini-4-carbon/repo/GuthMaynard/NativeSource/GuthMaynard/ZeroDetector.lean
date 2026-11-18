module
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace GuthMaynard.NativeMoment

def DivisorCountBoundProp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε

end GuthMaynard.NativeMoment
