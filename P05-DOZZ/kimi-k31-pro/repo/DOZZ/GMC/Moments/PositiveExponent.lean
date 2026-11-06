/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Defs.Q

/-! The unweighted annular exponent governing the positive-moment induction. -/


namespace DOZZ.Proofs

/-- The exact-scale moment exponent `ξγ(p)`. -/
noncomputable def gmcScaleExponent (γ p : ℝ) : ℝ :=
  γ * Q γ * p - γ ^ 2 * p ^ 2 / 2

end DOZZ.Proofs
