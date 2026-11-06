module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace PolyaNeumann

instance factTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

end PolyaNeumann

end
