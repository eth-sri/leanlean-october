module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Cutoff

/-!
# Quantitative smooth cutoffs in `H¹`

This file is the exact `p = 2` facade over the generic cutoff multiplier API.
It keeps the chosen value and gradient representatives literal, including the
formula for multiplication by a squared cutoff.
-/

@[expose] public section



namespace PDE

namespace H1Function

variable {d : ℕ}
variable {U inner outer : Set (Vec d)}
variable {K : ℝ}

variable (u : H1Function U) (η : QuantitativeSmoothCutoff inner outer K)











end H1Function

end PDE
