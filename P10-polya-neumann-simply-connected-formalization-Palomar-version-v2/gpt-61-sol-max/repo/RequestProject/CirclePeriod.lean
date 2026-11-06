module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The common period of the boundary Fourier and transport constructions. -/

@[expose] public section

namespace PolyaNeumann

scoped notation "circlePeriod" => (2 * Real.pi)

instance circlePeriodPositive : Fact (0 < circlePeriod) := ⟨Real.two_pi_pos⟩

end PolyaNeumann
