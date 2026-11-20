/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Slots
public import ThreeSumApsp.Lang.Tactics
public import Mathlib.Data.Nat.Log

/-!
# Logarithms, the cube root and halves, without division

Four routines on local variables only; none of them touches the memory.

* log2(x) returns ⌊log₂ x⌋ (0 for x = 0) by doubling (`log2_meets`).
* clog2(x) returns ⌈log₂ x⌉ (0 for x ≤ 1) by doubling (`clog2_meets`).
* cbrtCeil(n) returns the least s with s³ ≥ n, which is ⌈n^{1/3}⌉, by counting up
  (`cbrtCeil_meets`).
* half(h) returns ⌈h/2⌉ by counting up (`half_meets`).

Each of them is one loop that tries the candidates 0, 1, 2, … in turn.  Local variable 0 holds the
argument and receives the result, local variable 1 holds the candidate (`Arg`, `Cand`), and the two
logarithms keep a power of two in local variable 2 (`Power`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Logs

/-- The local variables of the routines: the argument, which the result replaces, the candidate,
and a power of two. -/
slots 0 Arg Cand Power

end Logs

open Logs

/-! ## The logarithm, rounded down -/

/-- log2(x): the candidate is L, and the power is 2^(L + 1). -/
def log2Body : Stmt :=
  .set Cand (k 0) ;;
  .set Power (k 2) ;;
  .while (v Power ≤' v Arg) (
    .set Power (v Power +' v Power) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of log2. -/
@[simp] def log2Time (x : ℕ) : ℕ := 14 * Nat.log 2 x + 12

/-- **log2(x)** returns ⌊log₂ x⌋ and leaves the memory as it is. -/
theorem log2_meets {p x } (hp : P[p]? = some log2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [x] μ (log2Time x) fun r μ' => r = (Nat.log 2 x : ℤ) ∧ μ' = μ := by
  have hlt : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  refine .of_body hp ?_
  light_set 0
  light_set 2
  -- while p ≤ x.  Before round i, L = i and p = 2^(i + 1).
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [x, i, (2 ^ (i + 1) : ℕ)], μ⟩)
    (Nat.log 2 x) (by simp) ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hx : x ≠ 0 := by
      rintro rfl
      simp at hi
    have hle : 2 ^ (i + 1) ≤ x :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_log_le_self 2 hx)
    have hix : i < x := lt_of_lt_of_le (Nat.lt_pow_self (by norm_num))
      ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans hle)
    rw [show 2 ^ (i + 1 + 1) = 2 ^ (i + 1) + 2 ^ (i + 1) by ring]
    generalize 2 ^ (i + 1) = q at hle
    -- The test is safe and holds.  p := p + p; L := L + 1 is safe and leads to the next state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize 2 ^ (Nat.log 2 x + 1) = q at hlt
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is L
    light_set (Nat.log 2 x)
    simp

/-! ## The logarithm, rounded up -/

/-- clog2(x): the candidate is L, and the power is 2^L. -/
def clog2Body : Stmt :=
  .set Cand (k 0) ;;
  .set Power (k 1) ;;
  .while (v Power <' v Arg) (
    .set Power (v Power +' v Power) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of clog2. -/
@[simp] def clog2Time (x : ℕ) : ℕ := 12 * Nat.clog 2 x + 10

/-- **clog2(x)** returns ⌈log₂ x⌉ and leaves the memory as it is. -/
theorem clog2_meets {p x } (hp : P[p]? = some clog2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [x] μ (clog2Time x) fun r μ' => r = (Nat.clog 2 x : ℤ) ∧ μ' = μ := by
  have hle : x ≤ 2 ^ Nat.clog 2 x := Nat.le_pow_clog (by norm_num) x
  refine .of_body hp ?_
  light_set 0
  light_set 1
  -- while p < x.  Before round i, L = i and p = 2^i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [x, i, (2 ^ i : ℕ)], μ⟩)
    (Nat.clog 2 x) (by simp) ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt := (Nat.lt_clog_iff_pow_lt (by norm_num)).1 hi
    have hix := lt_trans (Nat.lt_pow_self (by norm_num)) hlt
    rw [show 2 ^ (i + 1) = 2 ^ i + 2 ^ i by ring]
    generalize 2 ^ i = q at hlt
    -- The test is safe and holds.  p := p + p; L := L + 1 is safe and leads to the next state.
    exact ⟨by simp, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize 2 ^ Nat.clog 2 x = q at hle
    refine ⟨by simp, by light_side, ?_⟩
    -- the result is L
    light_set (Nat.clog 2 x)
    simp

/-! ## The cube root, rounded up -/

/-! ## Halves, rounded up -/

end Light
