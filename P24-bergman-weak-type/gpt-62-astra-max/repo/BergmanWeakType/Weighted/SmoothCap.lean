/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # A smooth nonnegative approximation to truncation by a level -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace BergmanWeakType

/-- Smooth concave approximation to the negative part `min x 0`, anchored at zero. -/
def smoothCap (ε x : ℝ) : ℝ := (x + ε - Real.sqrt (x^2 + ε^2)) / 2
def capD (ε x : ℝ) : ℝ := (1 - x / Real.sqrt (x^2 + ε^2)) / 2
def capDD (ε x : ℝ) : ℝ := -ε^2 / (2 * Real.sqrt (x^2 + ε^2)^3)

@[simp] theorem smoothCap_zero (x : ℝ) : smoothCap 0 x = min x 0 := by
  simp [smoothCap, Real.sqrt_sq_eq_abs]; grind

theorem cap_jet {ε : ℝ} (hε : 0 < ε) (x : ℝ) : JetAt (smoothCap ε) (capD ε) (capDD ε x) x := by
  constructor
  · unfold smoothCap; scalar_deriv; simp [capD]; ring
  · unfold capD; scalar_deriv; unfold capDD; grind

/-- Monotonicity, concavity, and the tangent-line bound at zero. -/
theorem cap_signs {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ capD ε x ∧ capDD ε x ≤ 0 ∧ capD ε x * x ≤ smoothCap ε x := by
  have hp : 0 < Real.sqrt (x^2+ε^2) := by positivity
  have hs := Real.sq_sqrt (by positivity : 0 ≤ x^2+ε^2)
  unfold capD capDD smoothCap
  refine ⟨div_nonneg (sub_nonneg.mpr ((div_le_one hp).mpr (by nlinarith))) zero_le_two,
    div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity), ?_⟩
  field_simp; nlinarith

end BergmanWeakType
