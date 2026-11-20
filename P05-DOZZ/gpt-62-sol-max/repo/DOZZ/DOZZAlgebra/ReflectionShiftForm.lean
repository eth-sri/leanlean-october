/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
public import Mathlib.Topology.DiscreteSubset

/-! Common forms of the reflection shift equations for the probabilistic and DOZZ coefficients. -/

@[expose] public section
open Filter
namespace DOZZ

noncomputable def reflectionFirstShiftDenom (γ : ℝ) (z : ℂ) : ℂ :=
  lFun (-(γ : ℂ) ^ 2 / 4) * lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
    lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)

noncomputable def reflectionDualShiftDenom (γ : ℝ) (z : ℂ) : ℂ :=
  lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * z / γ) * lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * z / γ)

noncomputable def reflectionDOZZDualConst (γ μ : ℝ) : ℂ :=
  (dozzBase γ μ : ℂ) ^ ((4 / γ ^ 2 : ℝ) : ℂ) / lFun ((4 / γ ^ 2 : ℝ) : ℂ)

abbrev ReflectionFirstShift (γ μ : ℝ) (R : ℂ → ℂ) : Prop :=
  ∀ᶠ z in codiscrete ℂ, R (z - γ / 2) = -(μ * Real.pi : ℂ) * R z / reflectionFirstShiftDenom γ z

abbrev ReflectionDualShift (γ : ℝ) (c : ℂ) (R : ℂ → ℂ) : Prop :=
  ∀ᶠ z in codiscrete ℂ, R z = -c * R (z + 2 / γ) / reflectionDualShiftDenom γ z

end DOZZ
