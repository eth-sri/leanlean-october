/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.CircleCross

/-! The definition `DOZZ.circleSelfEnergy`. -/

@[expose] public section


namespace DOZZ

/-- Self-energy `∬ G dσ_{x,r} dσ_{x,r}` of the circle measure (`= E[X_r(x)²]`). -/
noncomputable def circleSelfEnergy (x : ℂ) (r : ℝ) : ℝ :=
  ∫ z, ∫ w, gffKernel z w ∂circleMeasure x r ∂circleMeasure x r

end DOZZ
