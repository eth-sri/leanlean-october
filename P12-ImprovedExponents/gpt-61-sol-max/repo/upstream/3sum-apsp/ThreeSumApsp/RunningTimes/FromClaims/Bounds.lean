/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Machine.Realized
public import ThreeSumApsp.TimeClaims.Sec3.Definitions

/-!
# From a realized running time to a program with the paper's bound

A claim gives a running time `T` with `T ≤ C X`, where `X` is the bound that the paper prints, and
`RealizedWithin` gives a program that takes `c T + c` steps.  This file puts the two together.

* Bounds in several parameters, valid on a domain on which `X ≥ 1`: `exists_solves`, and
  `exists_solves_nonneg` with `exists_solves_pair` for two programs with one slope and one constant.
* Bounds `O(n^a (log n)^e)` in one size, valid for all large `n`: `solvedAt_of_realized`, and for
  every exponent `κ` of the magnitude `solvedInTime_of_claim` and `solvedInPolylogTime_of_claim`.
* An instance with numbers bounded by `n^κ` is also one with numbers bounded by `n^κ'`, `κ ≤ κ'`
  (`solvedInTimeAt_mono`), so that a bound for all `κ ≥ 1` is a bound for all `κ`
  (`solvedInTime_of_one_le`).
-/

public section

namespace ThreeSumApsp.FromClaims

open ThreeSumApsp.WordRam


/-! ## Bounds on a domain -/

/-! ## Bounds in one size, for all large sizes -/

/-- From a realized running time with a bound for all large sizes to a program with that bound. -/
theorem solvedAt_of_realized {Q} T κ
    (hR : Realized Q T) {C a} {e}
    (hev : ∀ᶠ n : ℕ in Filter.atTop,
      T n (n ^ ((κ : ℕ) : ℝ)) ≤ C * (n ^ a * Real.log n ^ e)) :
    SolvedInTimeAt Q κ a e := by
  obtain ⟨P, b, c, hc, hS⟩ := hR κ
  have hg : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ a * Real.log n ^ e := fun n =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Real.log_natCast_nonneg _) _)
  -- a bound for all large `n` gives a bound for all `n`
  obtain ⟨C', hC', hb⟩ := Dominated.of_eventually_add_one hev hg
  refine solvedInTimeAt_iff.2 ⟨P, b, c * C' + c, hS.mono le_rfl (fun x hx => hx) fun x hx => ?_⟩

  rw [(by
    simp_all
   : (x.U : ℝ) = (x.n : ℝ) ^ (κ : ℝ))]
  -- `c max(T, 0) + c ≤ c C' (X + 1) + c ≤ (c C' + c) (X + 1)`, where `X = n^a (log n)^e ≥ 0`
  have  :=
    mul_le_mul_of_nonneg_left (max_le (hb x.n trivial) (mul_nonneg hC' (by linarith [hg x.n]))) hc
  linarith [mul_nonneg hc (hg x.n)]

/-- A claim "solved in `O(n^a)` time on numbers of absolute value at most `n^κ`, for every `κ`", in
a reading `S` of "is solved in time T" that is realized, gives programs. -/
theorem solvedInTime_of_claim {S} {Q}
    (hR : ∀ T, S T → Realized Q T) {a} (h : Claim.SolvedAlongPow S UpperBigOPow a) :
    SolvedInTime Q a 0 := by
  intro κ
  obtain ⟨T, hT, C, hb⟩ := h κ (Nat.cast_nonneg κ)
  exact solvedAt_of_realized T κ (hR T hT) (C := C)
    (by simp_all)

/-- A claim "solved in `O(n^a (log n)^{O(1)})` time on numbers of absolute value at most `n^κ`, for
every `κ`", in a reading `S` of "is solved in time T" that is realized, gives programs. -/
theorem solvedInPolylogTime_of_claim {S} {Q}
    (hR : ∀ T, S T → Realized Q T) {a} (h : Claim.SolvedAlongPow S UpperPowPolylog a) :
    SolvedInPolylogTime Q a := by
  intro κ
  obtain ⟨T, hT, C, e, hb⟩ := h κ (Nat.cast_nonneg κ)
  exact ⟨e, solvedAt_of_realized T κ (hR T hT) hb⟩

end ThreeSumApsp.FromClaims
