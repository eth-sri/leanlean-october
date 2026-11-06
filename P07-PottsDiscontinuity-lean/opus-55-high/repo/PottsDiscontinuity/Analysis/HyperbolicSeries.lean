module

public import Mathlib

/-!
# Partial-fraction series for `coth`, `tanh` and `1 / sinh`

All identities are derived from Mathlib's Mittag-Leffler expansion of the cotangent
(`cot_series_rep'`).  For `a > 0`:

* `π coth (π a) = 1 / a + ∑_{n ≥ 1} 2 a / (a² + n²)` (`pi_coth_eq`);
* `∑_{k ≥ 0} 1 / (a² + (2k+1)²) = (π / (4a)) tanh (π a / 2)` (`hasSum_inv_sq_add_odd_sq`);
* `∑_{n ≥ 0} (-1)^n / (a² + n²) = π / (2a sinh (π a)) + 1 / (2a²)` (`hasSum_alt_inv_sq_add_sq`).
-/

public section

open Real

namespace PottsDiscontinuity

section
variable (a : ℝ)
theorem summable_inv_sq_add_succ_sq  :
    Summable (fun n : ℕ => 1 / (a ^ 2 + ((n : ℝ) + 1) ^ 2)) := by
  have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simp_all
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h1
  · positivity
  · apply one_div_le_one_div_of_le (by positivity)
    nlinarith

/-- The `coth` series, from Mathlib's `cot_series_rep'` evaluated at `i a`. -/
theorem pi_coth_eq (ha : 0 < a) :
    π * (Real.cosh (π * a) / Real.sinh (π * a)) =
      1 / a + ∑' n : ℕ, 2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) := by
  have hx : ((a : ℂ) * Complex.I) ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    simp at this
    linarith
  have h := cot_series_rep' hx
  have hcot : Complex.cot (π * ((a : ℂ) * Complex.I)) =
      -(Complex.I * ((Real.cosh (π * a) / Real.sinh (π * a) : ℝ) : ℂ)) := by
    rw [Complex.cot_eq_cos_div_sin,
      show (π : ℂ) * ((a : ℂ) * Complex.I) = ((π * a : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.cos_mul_I, Complex.sin_mul_I]
    field_simp
    simp
  have hterm : ∀ n : ℕ, (1 / ((a : ℂ) * Complex.I - ((n : ℂ) + 1)) +
      1 / ((a : ℂ) * Complex.I + ((n : ℂ) + 1))) =
      -(Complex.I * ((2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ)) := by
    intro n
    have h1 : (a : ℂ) ^ 2 + ((n : ℂ) + 1) ^ 2 ≠ 0 := by
      exact_mod_cast (by positivity)
    have h2 : (a : ℂ) * Complex.I - ((n : ℂ) + 1) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      linarith
    have h3 : (a : ℂ) * Complex.I + ((n : ℂ) + 1) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      linarith
    push_cast
    field_simp
    ring_nf
    simp
  simp_rw [hterm] at h
  rw [hcot] at h
  have h4 : ∑' n : ℕ, -(Complex.I * ((2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ)) =
      -(Complex.I * ((∑' n : ℕ, 2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_tsum, tsum_neg, tsum_mul_left]
  rw [h4] at h
  have h5 : (1 : ℂ) / ((a : ℂ) * Complex.I) = -(Complex.I * ((1 / a : ℝ) : ℂ)) := by
    simp
  rw [h5] at h
  have h7 : ((π * (Real.cosh (π * a) / Real.sinh (π * a)) : ℝ) : ℂ) =
      ((1 / a + ∑' n : ℕ, 2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    have hI := Complex.I_ne_zero
    push_cast at h ⊢
    grind
  exact_mod_cast h7

/-- The value `∑_{n ≥ 0} 1 / (a² + n²)`. -/
noncomputable def invSqSumValue  : ℝ :=
  π * (Real.cosh (π * a) / Real.sinh (π * a)) / (2 * a) + 1 / (2 * a ^ 2)
end

theorem hasSum_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    HasSum (fun n : ℕ => 1 / (a ^ 2 + (n : ℝ) ^ 2)) (invSqSumValue a) := by
  have h0 := pi_coth_eq a ha
  have hsum : HasSum (fun n : ℕ => 2 * a * (1 / (a ^ 2 + ((n : ℝ) + 1) ^ 2)))
      (π * (Real.cosh (π * a) / Real.sinh (π * a)) - 1 / a) := by
    have := ((summable_inv_sq_add_succ_sq a).mul_left (2 * a)).hasSum
    grind
  have hsum2 := hsum.div_const (2 * a)
  have hne : (2 * a) ≠ 0 := by positivity
  have hsum3 : HasSum (fun n : ℕ => 1 / (a ^ 2 + (((n + 1 : ℕ) : ℝ)) ^ 2))
      ((π * (Real.cosh (π * a) / Real.sinh (π * a)) - 1 / a) / (2 * a)) := by
    simp_all
  have := (hasSum_nat_add_iff' (f := fun n : ℕ => 1 / (a ^ 2 + (n : ℝ) ^ 2)) 1
    (g := invSqSumValue a)).1
  apply this
  convert hsum3 using 1
  simp only [invSqSumValue, Finset.sum_range_one, Nat.cast_zero]
  ring


section
variable (x : ℝ) (hx : 0 < x)
include hx
theorem two_coth_two_mul_sub_coth  :
    2 * (Real.cosh (2 * x) / Real.sinh (2 * x)) - Real.cosh x / Real.sinh x =
      Real.sinh x / Real.cosh x := by
  rw [Real.sinh_two_mul, Real.cosh_two_mul]
  grind

theorem coth_sub_coth_two_mul  :
    Real.cosh x / Real.sinh x - Real.cosh (2 * x) / Real.sinh (2 * x) =
      1 / Real.sinh (2 * x) := by
  rw [Real.sinh_two_mul, Real.cosh_two_mul]
  field_simp
  nlinarith [Real.cosh_sq x]
end

section
variable {a : ℝ} (ha : 0 < a)
include ha
theorem hasSum_inv_sq_add_even  :
    HasSum (fun k : ℕ => 1 / (a ^ 2 + ((2 * k : ℕ) : ℝ) ^ 2)) (invSqSumValue (a / 2) / 4) := by
  have h := (hasSum_inv_sq_add_sq (half_pos ha)).div_const 4
  grind

theorem hasSum_inv_sq_add_odd  :
    HasSum (fun k : ℕ => 1 / (a ^ 2 + ((2 * k + 1 : ℕ) : ℝ) ^ 2))
      (invSqSumValue a - invSqSumValue (a / 2) / 4) := by
  have hf := hasSum_inv_sq_add_sq ha
  have hodd : Summable (fun k : ℕ => 1 / (a ^ 2 + ((2 * k + 1 : ℕ) : ℝ) ^ 2)) :=
    hf.summable.comp_injective (fun x y h => by linarith)
  have h2 := HasSum.even_add_odd (f := fun n : ℕ => 1 / (a ^ 2 + (n : ℝ) ^ 2))
    (hasSum_inv_sq_add_even ha) hodd.hasSum
  have h3 := hf.unique h2
  have : ∑' k : ℕ, 1 / (a ^ 2 + ((2 * k + 1 : ℕ) : ℝ) ^ 2) =
      invSqSumValue a - invSqSumValue (a / 2) / 4 := by linarith
  rw [← this]
  exact hodd.hasSum

/-- The `tanh` partial fractions: `∑_{k ≥ 0} 1 / (a² + (2k+1)²) = (π / (4a)) tanh (π a / 2)`. -/
theorem hasSum_inv_sq_add_odd_sq  :
    HasSum (fun k : ℕ => 1 / (a ^ 2 + (2 * (k : ℝ) + 1) ^ 2))
      (π / (4 * a) * Real.tanh (π * a / 2)) := by
  have H := two_coth_two_mul_sub_coth (π * a / 2) (by positivity)
  rw [Real.tanh_eq_sinh_div_cosh, ← H]
  convert (hasSum_inv_sq_add_odd ha) using 1
  · simp
  · simp only [invSqSumValue]
    ring

/-- The alternating series
`∑_{n ≥ 0} (-1)^n / (a² + n²) = π / (2a sinh (π a)) + 1 / (2a²)`. -/
theorem hasSum_alt_inv_sq_add_sq  :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (a ^ 2 + (n : ℝ) ^ 2))
      (π / (2 * a * Real.sinh (π * a)) + 1 / (2 * a ^ 2)) := by
  have he := hasSum_inv_sq_add_even ha
  have h := HasSum.even_add_odd (f := fun n : ℕ => (-1 : ℝ) ^ n / (a ^ 2 + (n : ℝ) ^ 2))
    (by
      aesop)
    (by
      convert ((hasSum_inv_sq_add_odd ha).neg) using 1
      simp [pow_succ, pow_mul]
      ring)
  convert h using 1
  have H := coth_sub_coth_two_mul (π * a / 2) (by positivity)
  simp only [invSqSumValue]
  grind
end

end PottsDiscontinuity
