/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.Q
public import DOZZ.Statements.Defs.LFun
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! The definition `DOZZ.gaussSlitPlane`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The principal continuation domain ℂ \ [1,∞), see [KRV, (Fpmdef)]. -/
def gaussSlitPlane : Set ℂ := {z | z.im ≠ 0 ∨ z.re < 1}

theorem gaussSlitPlane_isOpen : IsOpen gaussSlitPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z : ℂ | z.re < 1})
  exact (isOpen_ne.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

end DOZZ
