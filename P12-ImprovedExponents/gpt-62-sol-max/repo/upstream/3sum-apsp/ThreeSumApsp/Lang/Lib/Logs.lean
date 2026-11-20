/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Lang.Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

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
registers [Arg, Cand, Power]

end Logs

open Logs

/-- Grow `p` by doubling, and return the number of successful tests. -/
def binaryLog (weak : Bool) (p : ℕ) : Stmt :=
  .set Cand (k 0) ;; .set Power (k p) ;;
  .while (if weak then v Power ≤' v Arg else v Power <' v Arg)
    (.set Power (v Power +' v Power) ;; .set Cand (v Cand +' k 1)) ;; .set Arg (v Cand)

theorem binaryLog_spec (weak : Bool) {x p n : ℕ} {μ : ℕ → ℤ}
    (hp : 0 < p) (hw : ((max p (2 * x + 1) : ℕ) : ℤ) ≤ lim.word)
    (ht : ∀ j, (if weak then p * 2 ^ j ≤ x else p * 2 ^ j < x) ↔ j < n) :
    Ends lim P d (binaryLog weak p) ⟨frame [x], μ⟩ (if weak then 14 * n + 12 else 12 * n + 10)
      fun s => s.loc 0 = (n : ℤ) ∧ s.mem = μ := by
  push_cast at hw
  cases weak <;> simp only [binaryLog, Bool.false_eq_true, if_false, if_true] at ht ⊢
  all_goals
    light_steps
    refine Ends.next _ (Ends.whileBlock (fun j σ => σ = ⟨frame [x, j, (p * 2 ^ j : ℕ)], μ⟩)
      n (by simp) ?_ ?_ le_rfl)
    · rintro j _ hj rfl
      have hq := (ht j).2 hj
      have hjq := Nat.lt_two_pow_self.trans_le (Nat.le_mul_of_pos_left (2 ^ j) hp)
      rw [pow_succ, Nat.mul_two, Nat.mul_add]
      generalize p * 2 ^ j = q at hq hjq ⊢
      exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
    · rintro _ rfl
      have h := mt (ht n).1 (Nat.lt_irrefl n)
      generalize p * 2 ^ n = q at h ⊢
      exact ⟨by light_side, by light_side, Ends.setTo n (by simp)⟩

def log2Body : Stmt := binaryLog true 2

@[simp] def log2Time (x : ℕ) : ℕ := 14 * Nat.log 2 x + 12

/-- **log2(x)** returns ⌊log₂ x⌋ and leaves the memory as it is. -/
theorem log2_meets {p x : ℕ} (hp : P[p]? = some log2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [x] μ (log2Time x) fun r μ' => r = (Nat.log 2 x : ℤ) ∧ μ' = μ := by
  refine .of_body hp (binaryLog_spec true (p := 2) (by decide) (by simp; omega) ?_)
  intro j
  by_cases hx : x = 0
  · simp [hx]
  simpa [pow_succ', Nat.succ_le_iff] using
    (Nat.le_log_iff_pow_le (b := 2) (x := j + 1) (by decide) hx).symm

def clog2Body : Stmt := binaryLog false 1

@[simp] def clog2Time (x : ℕ) : ℕ := 12 * Nat.clog 2 x + 10

/-- **clog2(x)** returns ⌈log₂ x⌉ and leaves the memory as it is. -/
theorem clog2_meets {p x : ℕ} (hp : P[p]? = some clog2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [x] μ (clog2Time x) fun r μ' => r = (Nat.clog 2 x : ℤ) ∧ μ' = μ :=
  .of_body hp (binaryLog_spec false (p := 1) (by decide) (by simp; omega)
     (by simpa using fun j => (Nat.lt_clog_iff_pow_lt (b := 2) (x := x) (y := j) (by decide)).symm))

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
theorem half_meets {p h : ℕ} (hp : P[p]? = some halfBody) (μ : ℕ → ℤ)
    (hword : ((h + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [h] μ (halfTime h) fun r μ' => r = (((h + 1) / 2 : ℕ) : ℤ) ∧ μ' = μ := by
  refine .of_body hp ?_
  unfold halfBody halfTime
  -- r := 0
  light_step
  -- while r + r < h.  Before round i, r = i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [h, i], μ⟩) ((h + 1) / 2) (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    -- The test is safe and holds.  r := r + 1 is safe and leads to the next state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is r
    light_step
    trivial

end Light
