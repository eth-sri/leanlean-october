/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Tactics
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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


namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Logs

/- The local variables of the routines: the argument, which the result replaces, the candidate,
and a power of two. -/
slots Arg Cand Power

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

variable {p x : ℕ}

/-- **log2(x)** returns ⌊log₂ x⌋ and leaves the memory as it is. -/
theorem log2_meets (hp : P[p]? = some log2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 2 : ℕ) : ℤ) ≤ lim.word := by omega) :
    Meets lim P p d [x] μ (log2Time x) fun r μ' => r = (Nat.log 2 x : ℤ) ∧ μ' = μ := by
  have hlt : x < 2 ^ (Nat.log 2 x + 1) := by grind [Nat.lt_pow_succ_log_self]
  refine .of_body hp ?_
  light_set 0
  light_set 2
  -- while p ≤ x.  Before round i, L = i and p = 2^(i + 1).
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [x, i, (2 ^ (i + 1) : ℕ)], μ⟩)
    _ (by simp) ?_ ?_ le_rfl)
  ·
    rintro i _ hi rfl
    have hx : x ≠ 0 := by
      aesop
    have hle : 2 ^ (i + 1) ≤ x :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_log_le_self 2 hx)
    have hix : i < x := by grind [lt_of_lt_of_le, Nat.lt_pow_self, Nat.pow_le_pow_right]
    rw [show 2 ^ (i + 1 + 1) = 2 ^ (i + 1) + 2 ^ (i + 1) by ring]
    generalize 2 ^ (i + 1) = q at hle
    -- The test is safe and holds.  p := p + p; L := L + 1 is safe and leads to the next state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  ·
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
theorem clog2_meets (hp : P[p]? = some clog2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 1 : ℕ) : ℤ) ≤ lim.word := by omega) :
    Meets lim P p d [x] μ (clog2Time x) fun r μ' => r = (Nat.clog 2 x : ℤ) ∧ μ' = μ := by
  have hle : x ≤ 2 ^ Nat.clog 2 x := by grind [Nat.le_pow_clog]
  refine .of_body hp ?_
  light_set 0
  light_set 1
  -- while p < x.  Before round i, L = i and p = 2^i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [x, i, (2 ^ i : ℕ)], μ⟩)
    _ (by simp) ?_ ?_ le_rfl)
  ·
    rintro i _ hi rfl
    have hlt : 2 ^ i < x := by grind [Nat.lt_clog_iff_pow_lt]
    have hix : i < x := by grind [lt_trans, Nat.lt_pow_self]
    rw [show 2 ^ (i + 1) = 2 ^ i + 2 ^ i by ring]
    generalize 2 ^ i = q at hlt
    -- The test is safe and holds.  p := p + p; L := L + 1 is safe and leads to the next state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  ·
    rintro _ rfl
    generalize 2 ^ Nat.clog 2 x = q at hle
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is L
    light_set (Nat.clog 2 x)
    simp

/-! ## The cube root, rounded up -/

/-- Some cube is at least n. -/
theorem exists_le_cube (n : ℕ) : ∃ s, n ≤ s ^ 3 := ⟨n, by grind [Nat.le_self_pow]⟩

/-- The least s with s³ ≥ n. -/
def cbrtLeast (n : ℕ) : ℕ := Nat.find (exists_le_cube n)

theorem le_cbrtLeast_pow (n : ℕ) : n ≤ cbrtLeast n ^ 3 := Nat.find_spec (exists_le_cube n)

variable {n s : ℕ}

theorem pow_lt_of_lt_cbrtLeast (h : s < cbrtLeast n := by omega) : s ^ 3 < n :=
  not_le.1 (Nat.find_min (exists_le_cube n) h)

theorem cbrtLeast_le (h : n ≤ s ^ 3) : cbrtLeast n ≤ s :=
  Nat.find_min' _ h

theorem cbrtLeast_le_self (n : ℕ) : cbrtLeast n ≤ n :=
  by simp_all [cbrtLeast_le, Nat.le_self_pow]

/-- The number ⌈n^{1/3}⌉ is at least 1 for n ≥ 1. -/
theorem one_le_cbrtLeast (hn : 1 ≤ n) : 1 ≤ cbrtLeast n := by
  grind [le_cbrtLeast_pow]

/-- The cube of the rounded cube root is at most 8 n. -/
theorem cbrtLeast_pow_le (n : ℕ) : cbrtLeast n ^ 3 ≤ 8 * n := by
  rcases Nat.eq_zero_or_pos (cbrtLeast n) with h | h
  · simp_all
  obtain ⟨s, hs⟩ : ∃ s, cbrtLeast n = s + 1 := by simp_all
  have h1 : s ^ 3 < n := pow_lt_of_lt_cbrtLeast
  rw [hs]
  rcases s.eq_zero_or_pos with h0 | h0
  · grind
  · calc (s + 1) ^ 3 ≤ (2 * s) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * s ^ 3 := by ring
      _ ≤ 8 * n := by omega

/-- The squares and cubes of the candidates fit in a word. -/
theorem abs_cube_le {i : ℕ} (hword : ((8 * n + 1 : ℕ) : ℤ) ≤ lim.word)
    (hi : i ≤ cbrtLeast n) : |(i : ℤ) * i| ≤ lim.word ∧ |(i : ℤ) * i * i| ≤ lim.word := by
  have hcube :=
    calc i * i * i = i ^ 3 := by ring
      _ ≤ cbrtLeast n ^ 3 := Nat.pow_le_pow_left hi 3
      _ ≤ 8 * n := cbrtLeast_pow_le n
  have hsquare : i * i ≤ i * i * i := by
    rcases i.eq_zero_or_pos with rfl | h
    · simp
    aesop
  grind

/-- cbrtCeil(n): the candidate is s. -/
def cbrtCeilBody : Stmt :=
  .set Cand (k 0) ;;
  .while (v Cand *' v Cand *' v Cand <' v Arg) (
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of cbrtCeil. -/
@[simp] def cbrtCeilTime (n : ℕ) : ℕ := 12 * cbrtLeast n + 12

/-- **cbrtCeil(n)** returns the least s with s³ ≥ n and leaves the memory as it is. -/
theorem cbrtCeil_meets (hp : P[p]? = some cbrtCeilBody) (μ : ℕ → ℤ)
    (hword : ((8 * n + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [n] μ (cbrtCeilTime n) fun r μ' => r = (cbrtLeast n : ℤ) ∧ μ' = μ := by
  have hsn := cbrtLeast_le_self n
  refine .of_body hp ?_
  light_set 0
  -- while s³ < n.  Before round i, s = i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [n, i], μ⟩) _ (by simp)
    ?_ ?_ le_rfl)
  ·
    rintro i _ hi rfl
    have hlt : (i : ℤ) * i * i < n := by
      have := pow_lt_of_lt_cbrtLeast hi
      linarith
    -- The test is safe and holds.  s := s + 1 is safe and leads to the next state.
    exact ⟨by simpa using abs_cube_le hword hi.le, by assumption, by light_side,
      by simp [update_frame_setLocal]⟩
  ·
    rintro _ rfl
    have hle : n ≤ (cbrtLeast n : ℤ) * cbrtLeast n * cbrtLeast n := by
      have := le_cbrtLeast_pow n
      linarith
    refine ⟨by simpa using abs_cube_le hword le_rfl, by simp_all, ?_⟩
    -- the result is s
    light_set (cbrtLeast n)
    simp

/-! ## Halves, rounded up -/

/-- half(h): the candidate is r. -/
def halfBody : Stmt :=
  .set Cand (k 0) ;;
  .while (v Cand +' v Cand <' v Arg) (
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of half. -/
@[simp] def halfTime (h : ℕ) : ℕ := 10 * ((h + 1) / 2) + 10

/-- **half(h)** returns ⌈h/2⌉ and leaves the memory as it is. -/
theorem half_meets {h : ℕ} (hp : P[p]? = some halfBody) (μ : ℕ → ℤ)
    (hword : ((h + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [h] μ (halfTime h) fun r μ' => r = (((h + 1) / 2 : ℕ) : ℤ) ∧ μ' = μ := by
  refine .of_body hp ?_
  light_set 0
  -- while r + r < h.  Before round i, r = i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [h, i], μ⟩) ((h + 1) / 2) (by simp)
    ?_ ?_ le_rfl)
  ·
    rintro i _ hi rfl
    -- The test is safe and holds.  r := r + 1 is safe and leads to the next state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  ·
    rintro _ rfl
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is r
    light_set ((h + 1) / 2)
    simp
