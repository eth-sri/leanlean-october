
import GradedNear.Defs

/-!
# Proof-side auxiliary definitions (not part of the statement)
-/

namespace GradedNear

/-- The Selberg majorant `ν_V(n) = (Σ_{d ∣ n} ψ_d)²` with the weights of `grahamWeight`. -/
noncomputable abbrev sieveNu (V : ℝ) (n : ℕ) : ℝ := (∑ d ∈ n.divisors, grahamWeight V d) ^ 2

end GradedNear
