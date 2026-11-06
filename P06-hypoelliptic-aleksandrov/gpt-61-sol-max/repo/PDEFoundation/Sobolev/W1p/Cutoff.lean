module

public import PDEFoundation.Sobolev.Cutoff.Basic
public import PDEFoundation.Sobolev.W1p.Product

/-!
# Multiplication by quantitative smooth cutoffs

This file specializes the existing smooth compact-support product rule to
`QuantitativeSmoothCutoff`. The weak product rule is not reproved: the
constructor delegates directly to
`W1pFunction.mulContDiffHasCompactSupport`.

The resulting value and coordinate-gradient estimates retain the explicit
coefficients `1` and `ENNReal.ofReal K`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

namespace W1pFunction

variable {d : ℕ}
variable {U inner outer : Set (Vec d)}
variable {p : ℝ≥0∞}
variable {K : ℝ}

variable (u : W1pFunction U p) (η : QuantitativeSmoothCutoff inner outer K) (hp : 1 ≤ p)











end W1pFunction

end PDE
