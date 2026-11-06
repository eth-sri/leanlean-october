/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # The two separate dual crossing coefficient extractions

A real connection matrix has entries u,v,w,x.
The diagonal zero-channel form has coefficients d₀,d₁; cancellation of its
one-channel mixed term is d₀uv+d₁wx=0. These are ordinary finite matrix identities.
-/

public section

namespace DOZZ.Proofs


variable (d₀ d₁ u v w x : ℝ) (hcross : d₀ * u * v + d₁ * w * x = 0)



include d₀ d₁ u v w x hcross in
/-- The same diagonal coefficient gives the distinct second crossing seed. -/
theorem dual_connection_diagonal_second_from_second  (hu : u ≠ 0) :
    d₀ * v ^ 2 + d₁ * x ^ 2 = d₁ * x * (u * x - v * w) / u := by
  grind

include d₀ d₁ u v w x hcross in
/-- The first coefficient extraction can be inverted once the connection entry and determinant are nonzero. -/
theorem dual_connection_first_seed_scalar 
    (hw : w ≠ 0) (hv : v ≠ 0) (hdet : u * x - v * w ≠ 0) :
    d₀ = (-w / (v * (u * x - v * w))) * (d₀ * v ^ 2 + d₁ * x ^ 2) := by
  grind

end DOZZ.Proofs
