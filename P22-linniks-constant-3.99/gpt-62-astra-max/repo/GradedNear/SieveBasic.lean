module

public import GradedNear.Defs

/-!
# Proof-side auxiliary definitions (not part of the statement)
-/

@[expose] public section

namespace GradedNear

/-- The closed integer interval covering a half-open logarithmic cell. The sieve
majorant is nonnegative, so including the upper endpoint is harmless. -/
noncomputable abbrev cell (q : ℕ) (t u : ℝ) := Finset.Icc ⌈(q:ℝ)^t⌉₊ ⌊(q:ℝ)^u⌋₊

/-- Smooth Abel weight. -/
noncomputable def wt (s : ℂ) (x : ℝ) : ℂ := (Real.log x : ℂ) * (x : ℂ)^(-s)

noncomputable def sieveTerm {q : ℕ} (V : ℝ) (ψ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) :=
  (sieveNu V n : ℂ) * (ψ n * wt s n)

end GradedNear
