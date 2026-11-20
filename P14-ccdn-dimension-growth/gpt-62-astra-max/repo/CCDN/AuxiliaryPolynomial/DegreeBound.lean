/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Named quantities in the determinant and auxiliary-polynomial bounds for a
hypersurface of degree `d` in `ℙ^(n+2)`, and the bracket `auxDegreeBound` of the
coefficient-sensitive auxiliary theorem (CCDN Theorem 3.1.1). -/

@[expose] public section
namespace CCDN
noncomputable section

variable (n d : ℕ) (B b H : ℝ)

/-- The root `d ^ (1 / (n + 1))` of the degree. -/
abbrev degreeRoot : ℝ := (d : ℝ) ^ (1 / (n + 1 : ℝ))

/-- The root `((n + 1)!) ^ (1 / (n + 1))`. -/
abbrev factorialRoot : ℝ := ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ))

/-- The coefficient-height exponent `1 / ((n + 1) d d ^ (1 / (n + 1)))`. -/
abbrev heightExponent : ℝ := 1 / ((n + 1 : ℝ) * d * degreeRoot n d)

/-- The radius exponent `(n + 2) / ((n + 1) d ^ (1 / (n + 1)))`. -/
abbrev boxExponent : ℝ := (n + 2 : ℝ) / ((n + 1 : ℝ) * degreeRoot n d)

/-- The bad-prime factor `exp (∑ p ∈ bad, log p / p)` of a finite set of primes. -/
abbrev primeSetFactor (bad : Finset ℕ) : ℝ := Real.exp (∑ p ∈ bad, Real.log p / p)

/-- The main term `d^(4 - 1/(n+1)) b B^boxExponent / H^heightExponent` of the
coefficient-sensitive auxiliary degree bound, for points of height at most `B` on an
equation with coefficient height `H` and bad-prime factor `b`. -/
def auxMainTerm : ℝ :=
  (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b * B ^ boxExponent n d / H ^ heightExponent n d

/-- The bracket `auxMainTerm + d^(1 - 1/(n+1)) log B + d^(4 - 1/(n+1))` of the
coefficient-sensitive auxiliary degree bound. -/
def auxDegreeBound : ℝ :=
  auxMainTerm n d B b H + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
    (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))

private lemma one_le_four_sub_inv : (1 : ℝ) ≤ 4 - 1 / (n + 1 : ℝ) := by
  have h := (div_le_one (by positivity)).mpr
    (show 1 ≤ (n + 1 : ℝ) by linarith)
  linarith

/-- `d ≤ d ^ (4 - 1 / (n + 1))` for a positive degree. -/
lemma le_rpow_four_sub_inv {n d : ℕ} (hd : 0 < d) :
    (d : ℝ) ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  simpa using Real.rpow_le_rpow_of_exponent_le hd1 (one_le_four_sub_inv n)

/-- For nonnegative reals `l` and `R`, there is an integer `M` with `d ≤ M`, `l ≤ M`, `R < M` and
`M ≤ d + l + R + 2`. -/
lemma auxiliary_integer_degree_selection {l R : ℝ} (hl : 0 ≤ l) (hR : 0 ≤ R) :
    ∃ M : ℕ, d ≤ M ∧ l ≤ M ∧ R < M ∧ (M : ℝ) ≤ d + l + R + 2 := by
  refine ⟨d + ⌈l⌉₊ + ⌊R⌋₊ + 1, by omega, ?_, ?_, ?_⟩
  grind [Nat.le_ceil]
  · have h := Nat.lt_floor_add_one R
    grind
  grind [Nat.ceil_lt_add_one, Nat.floor_le]

end
end CCDN
