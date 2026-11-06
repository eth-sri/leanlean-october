/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Notation for the unit interval in the radial variable -/

/-- The open unit interval in the radial variable. -/
notation "Ioo01" => Set.Ioo (0 : ℝ) 1

/-- The half-open unit interval in the radial variable. -/
notation "Ico01" => Set.Ico (0 : ℝ) 1

/-- The closed unit interval in the radial variable. -/
notation "Icc01" => Set.Icc (0 : ℝ) 1

/-- The full angle `τ = 2 * π`. -/
notation "τ" => 2 * Real.pi
