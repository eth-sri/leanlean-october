/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import PaperStatements
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.SuccPred

/-!
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light

open ThreeSumApsp.WordRam

/-- The bound 2^s · ((p₁ + 1) (p₂ + 1) ⋯)^k in the parameters of an instance. -/
def polyBound s k (params : List ℕ) := 2 ^ s * (params.map (· + 1)).prod ^ k

private theorem prod_succ_le (params : List ℕ) :
    (params.map (· + 1)).prod ≤ 2 ^ ((params.map Nat.log2).sum + params.length) := by
  induction params with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons]
    calc (p + 1) * (ps.map (· + 1)).prod
        ≤ 2 ^ (p.log2 + 1) * 2 ^ ((ps.map Nat.log2).sum + ps.length) :=
          Nat.mul_le_mul Nat.lt_log2_self ih
      _ = 2 ^ (p.log2 + (ps.map Nat.log2).sum + ps.length + 1) := by
          ring

/-- At an admissible word size, words have room for a polynomial bound in the parameters, if the
slope is large enough. -/
theorem polyBound_le {b W s k r} {params} (h : Admissible b params W)
    (hr : params.length ≤ r) (hb : s + k * r + k ≤ b) : polyBound s k params ≤ 2 ^ W := by
  set S := (params.map Nat.log2).sum
  have hexp :=
    calc s + (S + params.length) * k ≤ s + (S + r) * k := by gcongr
      -- the difference is s S + k r S + k
      _ ≤ (s + k * r + k) * (S + 1) := Nat.le.intro (k := s * S + k * r * S + k) (by ring)
      _ ≤ b * (S + 1) := Nat.mul_le_mul_right _ hb
      _ ≤ W := h
  calc polyBound s k params ≤ 2 ^ s * (2 ^ (S + params.length)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (prod_succ_le params) k)
    _ = 2 ^ (s + (S + params.length) * k) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hexp

/-- The bound is positive. -/
theorem one_le_polyBound s k params : 1 ≤ polyBound s k params := by
  have : 0 < (params.map (· + 1)).prod := List.prod_pos (by simp)
  exact Nat.mul_pos (by positivity) (by positivity)

/-- The bound grows with its two exponents. -/
theorem polyBound_mono {s s' k k'} (hs : s ≤ s') (hk : k ≤ k') params :
    polyBound s k params ≤ polyBound s' k' params := by
  have : 0 < (params.map (· + 1)).prod := List.prod_pos (by simp)
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hs) (Nat.pow_le_pow_right this hk)

/-- A power of two times the bound is a bound of the same form. -/
theorem polyBound_mul s s' k params :
    2 ^ s' * polyBound s k params = polyBound (s' + s) k params := by
  simp only [polyBound, pow_add, mul_assoc]

/-- The sum of two numbers with such bounds has such a bound. -/
theorem add_le_polyBound {a b s s' k k'} {params} (ha : a ≤ polyBound s k params)
    (hb : b ≤ polyBound s' k' params) : a + b ≤ polyBound (1 + (s + s')) (k + k') params := by
  have  := ha.trans (polyBound_mono (Nat.le_add_right s s') (Nat.le_add_right k k') params)
  have  := hb.trans (polyBound_mono (Nat.le_add_left s' s) (Nat.le_add_left k' k) params)
  rw [← polyBound_mul]
  omega

end Light
