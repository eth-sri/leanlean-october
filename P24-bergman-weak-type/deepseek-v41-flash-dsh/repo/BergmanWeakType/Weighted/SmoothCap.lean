/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Notation

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

/-- Continuity of a two-variable function on the radial strip `[0,1) × ℝ`. -/
def OnStrip (G : ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (fun p : ℝ × ℝ ↦ G p.1 p.2) (Set.Ico 0 1 ×ˢ Set.univ)

/-- A smooth approximation to `min x c`, shifted to stay nonnegative for nonnegative inputs. -/
def smoothCap (ε c x : ℝ) : ℝ :=
  (x + c - Real.sqrt ((x - c) ^ 2 + ε ^ 2) + ε) / 2

/-- The derivative of the smooth truncation with respect to its level. -/
def smoothCapLevelDeriv (ε c x : ℝ) : ℝ :=
  (1 + (x - c) / Real.sqrt ((x - c) ^ 2 + ε ^ 2)) / 2

/-- The derivative of the smooth truncation with respect to its input. -/
def smoothCapInputDeriv (ε c x : ℝ) : ℝ :=
  (1 - (x - c) / Real.sqrt ((x - c) ^ 2 + ε ^ 2)) / 2

theorem smoothCap_le_min_add {ε c x : ℝ} : smoothCap ε c x ≤ min x c + ε / 2 := by
  have hsq : |x - c| ≤ Real.sqrt ((x - c) ^ 2 + ε ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
  dsimp [smoothCap]
  rcases le_total x c with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)] at *
    linarith
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)] at *
    linarith

theorem min_le_smoothCap {ε c x : ℝ} (hε : 0 ≤ ε) : min x c ≤ smoothCap ε c x := by
  have hsq : Real.sqrt ((x - c) ^ 2 + ε ^ 2) ≤ |x - c| + ε := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_abs (x - c), mul_nonneg (abs_nonneg (x - c)) hε]
  dsimp [smoothCap]
  rcases le_total x c with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)] at *
    linarith
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)] at *
    linarith

theorem smoothCapLevelDeriv_mem_Icc {ε c x : ℝ} (hε : 0 < ε) :
    smoothCapLevelDeriv ε c x ∈ Icc01 := by
  have hp : 0 < Real.sqrt ((x - c) ^ 2 + ε ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (x - c)])
  have hsq : |x - c| ≤ Real.sqrt ((x - c) ^ 2 + ε ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
  have hratio : |(x - c) / Real.sqrt ((x - c) ^ 2 + ε ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hp]
    exact (div_le_one hp).mpr hsq
  rcases abs_le.mp hratio with ⟨hl, hu⟩
  constructor <;> dsimp [smoothCapLevelDeriv] <;> linarith

theorem smoothCapInputDeriv_mem_Icc {ε c x : ℝ} (hε : 0 < ε) :
    smoothCapInputDeriv ε c x ∈ Icc01 := by
  rcases smoothCapLevelDeriv_mem_Icc (c := c) (x := x) hε with ⟨hl, hu⟩
  constructor <;> dsimp [smoothCapInputDeriv, smoothCapLevelDeriv] at * <;> linarith

theorem hasDerivAt_smoothCap_input {ε c x : ℝ} (hε : 0 < ε) :
    HasDerivAt (smoothCap ε c) (smoothCapInputDeriv ε c x) x := by
  unfold smoothCap
  have hn : (x - c) ^ 2 + ε ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg (x - c)])
  have hs := (((hasDerivAt_id x).sub_const c).pow 2 |>.add_const (ε ^ 2)).sqrt hn
  convert (((hasDerivAt_id x).add_const c).sub hs |>.add_const ε).div_const 2 using 1 <;>
    dsimp [smoothCap, smoothCapInputDeriv]
  ring

theorem hasDerivAt_smoothCapInputDeriv {ε c x : ℝ} (hε : 0 < ε) :
    HasDerivAt (smoothCapInputDeriv ε c)
      (-(ε ^ 2) / (2 * Real.sqrt ((x - c) ^ 2 + ε ^ 2) ^ 3)) x := by
  have hp : 0 < (x - c) ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg (x - c)]
  have hs := (((hasDerivAt_id x).sub_const c).pow 2 |>.add_const (ε ^ 2)).sqrt hp.ne'
  have hr := ((hasDerivAt_id x).sub_const c).div hs (Real.sqrt_pos.mpr hp).ne'
  unfold smoothCapInputDeriv
  convert (hr.const_sub 1).div_const 2 using 1 <;> dsimp
  have heq := Real.sq_sqrt hp.le
  field_simp [(Real.sqrt_pos.mpr hp).ne']
  nlinarith

theorem smoothCap_secondDeriv_nonpos {ε c x : ℝ} :
    -(ε ^ 2) / (2 * Real.sqrt ((x - c) ^ 2 + ε ^ 2) ^ 3) ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (sq_nonneg ε)
  · positivity

end BergmanWeakType
