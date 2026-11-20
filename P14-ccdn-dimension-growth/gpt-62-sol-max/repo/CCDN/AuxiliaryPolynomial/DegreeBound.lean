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

/-- The root `d ^ (1 / (n + 1))` of the degree. -/
abbrev degreeRoot (n d : ℕ) : ℝ := (d : ℝ) ^ (1 / (n + 1 : ℝ))

/-- The root `((n + 1)!) ^ (1 / (n + 1))`. -/
abbrev factorialRoot (n : ℕ) : ℝ := ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ))

/-- The coefficient-height exponent `1 / ((n + 1) d d ^ (1 / (n + 1)))`. -/
abbrev heightExponent (n d : ℕ) : ℝ := 1 / ((n + 1 : ℝ) * d * degreeRoot n d)

/-- The radius exponent `(n + 2) / ((n + 1) d ^ (1 / (n + 1)))`. -/
abbrev boxExponent (n d : ℕ) : ℝ := (n + 2 : ℝ) / (n + 1 : ℝ) / degreeRoot n d

/-- The excess radius exponent in the projective estimate over the affine one. -/
abbrev scaleExponent (n d : ℕ) : ℝ := 1 / ((n + 1 : ℝ) * degreeRoot n d)

lemma scaleExponent_le_one (n : ℕ) {d : ℕ} (hd : 0 < d) : scaleExponent n d ≤ 1 := by
  apply (div_le_one (by positivity)).mpr
  exact one_le_mul_of_one_le_of_one_le (by simp) (Real.one_le_rpow (by exact_mod_cast hd) (by positivity))

lemma box_power_div_scale (n : ℕ) {d : ℕ} (hd : 0 < d) {a B : ℝ} (ha : 0 < a) (hB : 0 < B) :
    B ^ boxExponent n d / a ^ scaleExponent n d = B ^ (1 / degreeRoot n d) * (B / a) ^ scaleExponent n d := by
  have he : boxExponent n d = 1 / degreeRoot n d + scaleExponent n d := by
    dsimp [boxExponent, scaleExponent]
    field_simp
    ring
  rw [he, Real.rpow_add hB, Real.div_rpow hB.le ha.le, mul_div_assoc]

/-- The bad-prime factor `exp (∑ p ∈ bad, log p / p)` of a finite set of primes. -/
abbrev primeSetFactor (bad : Finset ℕ) : ℝ := Real.exp (∑ p ∈ bad, Real.log p / p)

/-- The degree-dependent scale for the auxiliary degree bound. -/
abbrev auxDegreeScale (n d : ℕ) : ℝ := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))

/-- The logarithmic remainder, normalized by the degree root. -/
abbrev auxLogTerm (n d : ℕ) (B : ℝ) : ℝ := (d : ℝ) * Real.log B / degreeRoot n d

/-- Main term of the coefficient-sensitive auxiliary degree bound. -/
def auxMainTerm (n d : ℕ) (B b H : ℝ) : ℝ :=
  auxDegreeScale n d * B ^ boxExponent n d * (b / H ^ heightExponent n d)

/-- The bracket in the coefficient-sensitive auxiliary degree bound. -/
def auxDegreeBound (n d : ℕ) (B b H : ℝ) : ℝ :=
  auxMainTerm n d B b H + auxLogTerm n d B + auxDegreeScale n d

lemma le_auxDegreeScale {n d : ℕ} (hd : 0 < d) : (d : ℝ) ≤ auxDegreeScale n d := by
  have h := (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr (show 1 ≤ (n + 1 : ℝ) by simp)
  simpa only [auxDegreeScale, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hd : (1 : ℝ) ≤ d) (show (1 : ℝ) ≤ 4 - 1 / (n + 1 : ℝ) by linarith)

/-- The logarithmic and constant terms are absorbed by any radius power at least `1 / d^(1/(n+1))`. -/
lemma auxDegree_remainder_le {n d : ℕ} (hd : 0 < d) {B α : ℝ} (hB : 1 ≤ B)
    (hα : 1 / degreeRoot n d ≤ α) :
    auxLogTerm n d B + auxDegreeScale n d ≤ 2 * (auxDegreeScale n d * B ^ α) := by
  have hX : 0 < degreeRoot n d := by positivity
  have hlog : Real.log B ≤ B ^ (1 / degreeRoot n d) * degreeRoot n d := by
    simpa only [one_div, div_inv_eq_mul] using
      Real.log_le_rpow_div (by linarith : 0 ≤ B) (by positivity : 0 < 1 / degreeRoot n d)
  have h := Real.rpow_le_rpow_of_exponent_le hB hα
  have hBα : 1 ≤ B ^ α := (Real.one_le_rpow hB (by positivity : 0 ≤ 1 / degreeRoot n d)).trans h
  have hL : auxLogTerm n d B ≤ auxDegreeScale n d * B ^ α := by
    apply (div_le_iff₀ hX).mpr
    calc
      _ ≤ (d : ℝ) * (B ^ (1 / degreeRoot n d) * degreeRoot n d) := by gcongr
      _ = (d : ℝ) * B ^ (1 / degreeRoot n d) * degreeRoot n d := by ring
      _ ≤ _ := by gcongr; exact le_auxDegreeScale hd
  linarith [le_mul_of_one_le_right (show 0 ≤ auxDegreeScale n d by positivity) hBα]

/-- For nonnegative reals `l` and `R`, there is an integer `M` with `d ≤ M`, `l ≤ M`, `R < M` and
`M ≤ d + l + R + 2`. -/
lemma auxiliary_integer_degree_selection (d : ℕ) {l R : ℝ} (hl : 0 ≤ l) (hR : 0 ≤ R) :
    ∃ M : ℕ, d ≤ M ∧ l ≤ M ∧ R < M ∧ (M : ℝ) ≤ d + l + R + 2 := by
  refine ⟨d + ⌈l⌉₊ + ⌊R⌋₊ + 1, by omega, ?_, ?_, ?_⟩
  · have h := Nat.le_ceil l
    grind
  · have h := Nat.lt_floor_add_one R
    grind
  · have hc := Nat.ceil_lt_add_one hl
    have hf := Nat.floor_le hR
    push_cast
    linarith

end
end CCDN
