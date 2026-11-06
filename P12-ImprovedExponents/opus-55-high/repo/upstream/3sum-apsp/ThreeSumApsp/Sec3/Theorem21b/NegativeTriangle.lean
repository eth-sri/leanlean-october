/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import PaperStatements

/-!
# Theorem 21(b): Negative Triangle reduces to Exact Triangle

[VW13, Theorem 3.3] in the form needed for Theorem 21(b): one question about a negative triangle
becomes `O(log U)` questions about a zero triangle.  Shifting the weights turns "the triangle is
negative" into `x + y < v` for natural numbers (`S_neg_iff`).  Let the gap at level `ℓ` be
`⌊2v/2^ℓ⌋ - ⌊2x/2^ℓ⌋ - ⌊2y/2^ℓ⌋` (`prefixGap`).  If `x + y < v`, the gap at level 0 is
`2(v - x - y) ≥ 2`, which is why the numbers are doubled; from one level to the next a gap of at
least 4 stays at least 2, and the gap is below 2 once `2^ℓ > v`.  So at some level the gap is
exactly 2 or exactly 3, and conversely a gap of at least 2 gives `x + y < v`
(`lt_iff_exists_prefixGap`).  "The gap is `e`" is an exact condition on a triangle (`negToExact`,
`negToExact_isZeroTriangle_iff`).  Together: `hasNegativeTriangle_iff` and
`theorem_21b_negative_to_exact`.
-/


namespace ThreeSumApsp

namespace Theorem21

/-- The gap at level `ℓ`: the difference `⌊2v/2^ℓ⌋ - ⌊2x/2^ℓ⌋ - ⌊2y/2^ℓ⌋` of the prefixes of `2v`,
`2x` and `2y`. -/
def prefixGap (x y v ℓ : ℕ) : ℤ :=
  ((2 * v / 2 ^ ℓ : ℕ) : ℤ) - ((2 * x / 2 ^ ℓ : ℕ) : ℤ) - ((2 * y / 2 ^ ℓ : ℕ) : ℤ)

variable {y x v ℓ : ℕ}

/-- A gap of at least 2 gives `x + y < v`: with `X`, `Y`, `V` for the three prefixes,
`2x + 2y < (X + Y + 2) 2^ℓ ≤ V 2^ℓ ≤ 2v`. -/
theorem add_lt_of_two_le_prefixGap (h : 2 ≤ prefixGap x y v ℓ) :
    x + y < v := by
  unfold prefixGap at h
  have hpos : 0 < 2 ^ ℓ := by simp
  have hV := Nat.mul_div_le (2 * v) (2 ^ ℓ)
  have hX := Nat.div_add_mod (2 * x) (2 ^ ℓ)
  have hXrem := Nat.mod_lt (2 * x) hpos
  have hY := Nat.div_add_mod (2 * y) (2 ^ ℓ)
  have hYrem := Nat.mod_lt (2 * y) hpos
  have hmul : 2 ^ ℓ * (2 * x / 2 ^ ℓ + 2 * y / 2 ^ ℓ + 2) ≤ 2 ^ ℓ * (2 * v / 2 ^ ℓ) :=
    Nat.mul_le_mul_left _ (by omega)
  linarith

/-- A gap of at least 2 needs `2^ℓ ≤ v`: the prefix `V` of `2v` is at least 2, so
`2 · 2^ℓ ≤ V 2^ℓ ≤ 2v`. -/
theorem pow_le_of_two_le_prefixGap (h : 2 ≤ prefixGap x y v ℓ) :
    2 ^ ℓ ≤ v := by
  unfold prefixGap at h
  have hX := Int.natCast_nonneg (2 * x / 2 ^ ℓ)
  have hY := Int.natCast_nonneg (2 * y / 2 ^ ℓ)
  have hV := Nat.mul_div_le (2 * v) (2 ^ ℓ)
  have hmul : 2 ^ ℓ * 2 ≤ 2 ^ ℓ * (2 * v / 2 ^ ℓ) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- A gap of at least 4 leaves a gap of at least 2 at the next level: a prefix at level `ℓ + 1` is
half the prefix at level `ℓ`, rounded down, so the new gap is at least `(4 - 1)/2`. -/
theorem two_le_prefixGap_succ (h : 4 ≤ prefixGap x y v ℓ) :
    2 ≤ prefixGap x y v (ℓ + 1) := by
  unfold prefixGap at h ⊢
  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  omega

/-- Climbing from a level at which the gap is at least 2, the first level at which the gap is below
4 has gap 2 or 3.  There is such a level, because a gap of at least 2 needs `2^ℓ ≤ v`. -/
theorem exists_prefixGap_eq (h : 2 ≤ prefixGap x y v ℓ) :
    ∃ ℓ' : ℕ, prefixGap x y v ℓ' = 2 ∨ prefixGap x y v ℓ' = 3 := by
  induction hk : v + 1 - ℓ generalizing ℓ with
  | zero =>
    -- The level cannot be above `v`, since `ℓ < 2^ℓ ≤ v`.
    have hle := pow_le_of_two_le_prefixGap h
    grind [Nat.lt_two_pow_self]
  | succ k ih =>
    by_cases h4 : 4 ≤ prefixGap x y v ℓ
    · exact ih (two_le_prefixGap_succ h4) (by omega)
    grind

variable {L : ℕ}

/-- For Theorem 21(b), after [VW13, Proposition 3.4]: whether a triangle has negative weight is
expressed by O(log U) equations between binary prefixes of the shifted weights.
One way to write this: for natural numbers with `v < 2^L`, `x + y < v` if and only if
at one of the levels `ℓ < L` the gap `⌊2v/2^ℓ⌋ - ⌊2x/2^ℓ⌋ - ⌊2y/2^ℓ⌋` is exactly 2 or exactly 3.
(This form need not be literally the one of [VW13].) -/
theorem lt_iff_exists_prefixGap (hL : v < 2 ^ L := by aesop) :
    x + y < v ↔ ∃ ℓ < L, ∃ e : ℤ, (e = 2 ∨ e = 3) ∧ prefixGap x y v ℓ = e := by
  constructor
  · intro h
    -- At level 0 the gap is `2(v - x - y) ≥ 2`.
    have hzero : 2 ≤ prefixGap x y v 0 := by
      grind [prefixGap]
    obtain ⟨ℓ, hℓ⟩ := exists_prefixGap_eq hzero
    have hle : 2 ^ ℓ ≤ v := pow_le_of_two_le_prefixGap (x := x) (y := y) (by omega)
    exact ⟨ℓ, (Nat.pow_lt_pow_iff_right (by norm_num)).mp (hle.trans_lt hL), _, hℓ, rfl⟩
  · rintro ⟨ℓ, -, e, he, h⟩
    exact add_lt_of_two_le_prefixGap (ℓ := ℓ) (by omega)

/-- The Exact Triangle instance for the level `ℓ` and the exact value `e`.  The weights `w(a,b)`,
`w(b,c)` and `w(a,c)` in `[-U, U]` are first shifted to the natural numbers `x = w(a,b) + U`,
`y = w(b,c) + U` and `v = 2U - w(a,c)`, so that the triangle is negative exactly if `x + y < v`;
then `x` and `y` are replaced by the prefixes `⌊2x/2^ℓ⌋` and `⌊2y/2^ℓ⌋`, and `v` by `e - ⌊2v/2^ℓ⌋`.
-/
def negToExact (U ℓ : ℕ) (e : ℤ) : (ℤ → ℤ) × (ℤ → ℤ) × (ℤ → ℤ) :=
  (fun wAB => ((2 * (wAB + U).toNat / 2 ^ ℓ : ℕ) : ℤ),
    fun wBC => ((2 * (wBC + U).toNat / 2 ^ ℓ : ℕ) : ℤ),
    fun wAC => e - ((2 * (2 * U - wAC).toNat / 2 ^ ℓ : ℕ) : ℤ))

variable {n : ℕ}

/-- A triangle has weight zero in the instance for `ℓ` and `e` exactly if the gap at level `ℓ` is
`e`. -/
theorem negToExact_isZeroTriangle_iff (T : TriangleInstance ℤ n) (U ℓ : ℕ) (e : ℤ)
    (a b c : Fin n) :
    (T.mapWeights (negToExact U ℓ e)).IsZeroTriangle a b c ↔
      prefixGap (T.wAB a b + U).toNat (T.wBC b c + U).toNat (2 * U - T.wAC a c).toNat ℓ = e := by
  simp [TriangleInstance.IsZeroTriangle, TriangleInstance.S, TriangleInstance.mapWeights,
    negToExact, prefixGap]
  omega

/-- A triangle is negative exactly if the shifted weights satisfy `x + y < v`. -/
theorem S_neg_iff (T : TriangleInstance ℤ n) (U : ℕ)
    (hT : T.WeightsBoundedBy (U : ℤ)) (a b c : Fin n) :
    T.S a b c < 0 ↔
      (T.wAB a b + U).toNat + (T.wBC b c + U).toNat < (2 * U - T.wAC a c).toNat := by
  obtain ⟨hTAB, hTBC, hTAC⟩ := hT
  grind [TriangleInstance.S]

/-- The reduction of [VW13, Theorem 3.3], for weights in `[-U, U]` with `3U < 2^L`: there is a
negative triangle if and only if, at one of the levels `ℓ < L` and for `e = 2` or `e = 3`, the
instance made of the prefixes has a zero triangle. -/
theorem hasNegativeTriangle_iff {U : ℕ} (T : TriangleInstance ℤ n)
    (hT : T.WeightsBoundedBy (U : ℤ)) (hL : 3 * U < 2 ^ L) :
    T.HasNegativeTriangle ↔ ∃ ℓ < L, ∃ e : ℤ, (e = 2 ∨ e = 3) ∧
      (T.mapWeights (negToExact U ℓ e)).HasZeroTriangle := by
  have hv (a c : Fin n) : (2 * U - T.wAC a c).toNat < 2 ^ L := by
    obtain ⟨-, -, hTAC⟩ := hT
    grind
  constructor
  · rintro ⟨a, b, c, h⟩
    obtain ⟨ℓ, hℓ, e, he, hgap⟩ :=
      (lt_iff_exists_prefixGap).1 ((S_neg_iff T U hT a b c).1 h)
    exact ⟨ℓ, hℓ, e, he, a, b, c, by grind [negToExact_isZeroTriangle_iff]⟩
  · rintro ⟨ℓ, hℓ, e, he, a, b, c, h⟩
    exact ⟨a, b, c, (S_neg_iff T U hT a b c).2 ((lt_iff_exists_prefixGap (by simp_all)).2
      ⟨ℓ, hℓ, e, he, by grind [negToExact_isZeroTriangle_iff]⟩)⟩
