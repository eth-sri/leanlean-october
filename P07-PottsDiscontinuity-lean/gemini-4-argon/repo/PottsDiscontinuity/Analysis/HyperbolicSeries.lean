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

@[expose] public section

open Real

namespace PottsDiscontinuity

theorem summable_inv_sq_add_succ_sq (a : ℝ) :
    Summable (fun n : ℕ => 1 / (a ^ 2 + ((n : ℝ) + 1) ^ 2)) :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun n => one_div_le_one_div_of_le (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)
      (by nlinarith [sq_nonneg a]))
    (by simpa using (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two))

/-- The `coth` series, from Mathlib's `cot_series_rep'` evaluated at `i a`. -/
theorem pi_coth_eq (a : ℝ) (ha : 0 < a) :
    π * (Real.cosh (π * a) / Real.sinh (π * a)) =
      1 / a + ∑' n : ℕ, 2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) := by
  have hx : ((a : ℂ) * Complex.I) ∈ Complex.integerComplement := fun ⟨n, hn⟩ =>
    ha.ne' (by simpa using (congrArg Complex.im hn).symm)
  have h := cot_series_rep' hx
  have hsinh : Real.sinh (π * a) ≠ 0 := (Real.sinh_pos_iff.2 (by positivity)).ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hs : (Real.sinh (π * a) : ℂ) ≠ 0 := by exact_mod_cast hsinh
  have hcot : Complex.cot (π * ((a : ℂ) * Complex.I)) =
      -(Complex.I * ((Real.cosh (π * a) / Real.sinh (π * a) : ℝ) : ℂ)) := by
    rw [Complex.cot_eq_cos_div_sin,
      show (π : ℂ) * ((a : ℂ) * Complex.I) = ((π * a : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.cos_mul_I, Complex.sin_mul_I]
    have hs' : Complex.sinh ((π : ℂ) * a) ≠ 0 := by
      have := hs; rw [Complex.ofReal_sinh] at this; push_cast at this; exact this
    push_cast; field_simp; simp [Complex.I_sq]
  have hterm (n : ℕ) : (1 / ((a : ℂ) * Complex.I - ((n : ℂ) + 1)) +
      1 / ((a : ℂ) * Complex.I + ((n : ℂ) + 1))) =
      -(Complex.I * ((2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ)) := by
    have h1 : (a : ℂ) ^ 2 + ((n : ℂ) + 1) ^ 2 ≠ 0 := by
      exact_mod_cast (by positivity : (a ^ 2 + ((n : ℝ) + 1) ^ 2) ≠ 0)
    have h2 : (a : ℂ) * Complex.I - ((n : ℂ) + 1) ≠ 0 := fun h0 =>
      ha.ne' (by simpa using congrArg Complex.im h0)
    have h3 : (a : ℂ) * Complex.I + ((n : ℂ) + 1) ≠ 0 := fun h0 =>
      ha.ne' (by simpa using congrArg Complex.im h0)
    push_cast; field_simp; ring_nf; simp
  simp_rw [hterm] at h
  rw [hcot, tsum_neg, tsum_mul_left, ← Complex.ofReal_tsum,
    show (1 : ℂ) / ((a : ℂ) * Complex.I) = -(Complex.I * ((1 / a : ℝ) : ℂ)) by
      push_cast; field_simp; simp [Complex.I_sq]] at h
  have h7 : ((π * (Real.cosh (π * a) / Real.sinh (π * a)) : ℝ) : ℂ) =
      ((1 / a + ∑' n : ℕ, 2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    push_cast at h ⊢
    linear_combination (-1 : ℂ) * h
  exact_mod_cast h7

/-- The value `∑_{n ≥ 0} 1 / (a² + n²)`. -/
noncomputable def invSqSumValue (a : ℝ) : ℝ :=
  π * (Real.cosh (π * a) / Real.sinh (π * a)) / (2 * a) + 1 / (2 * a ^ 2)

theorem hasSum_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    HasSum (fun n : ℕ => 1 / (a ^ 2 + (n : ℝ) ^ 2)) (invSqSumValue a) := by
  have hsum : HasSum (fun n : ℕ => 2 * a * (1 / (a ^ 2 + ((n : ℝ) + 1) ^ 2)))
      (π * (Real.cosh (π * a) / Real.sinh (π * a)) - 1 / a) := by
    have h := ((summable_inv_sq_add_succ_sq a).mul_left (2 * a)).hasSum
    rwa [show ∑' n : ℕ, 2 * a * (1 / (a ^ 2 + ((n : ℝ) + 1) ^ 2)) =
        π * (Real.cosh (π * a) / Real.sinh (π * a)) - 1 / a by
      rw [pi_coth_eq a ha]; simp_rw [mul_one_div]; ring] at h
  have hne : (2 * a) ≠ 0 := by positivity
  have ha0 : a ≠ 0 := ha.ne'
  refine (hasSum_nat_add_iff' (f := fun n : ℕ => 1 / (a ^ 2 + (n : ℝ) ^ 2)) 1
    (g := invSqSumValue a)).1 ?_
  convert hsum.div_const (2 * a) using 1
  · funext n; push_cast; field_simp
  · simp only [invSqSumValue, Finset.sum_range_one, Nat.cast_zero]; field_simp; ring

theorem two_coth_two_mul_sub_coth (x : ℝ) (hx : 0 < x) :
    2 * (Real.cosh (2 * x) / Real.sinh (2 * x)) - Real.cosh x / Real.sinh x =
      Real.sinh x / Real.cosh x := by
  have hs : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.2 hx).ne'
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  rw [Real.sinh_two_mul, Real.cosh_two_mul]; field_simp; nlinarith [Real.cosh_sq x]

theorem coth_sub_coth_two_mul (x : ℝ) (hx : 0 < x) :
    Real.cosh x / Real.sinh x - Real.cosh (2 * x) / Real.sinh (2 * x) =
      1 / Real.sinh (2 * x) := by
  have hs : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.2 hx).ne'
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  rw [Real.sinh_two_mul, Real.cosh_two_mul]; field_simp; nlinarith [Real.cosh_sq x]

theorem hasSum_inv_sq_add_even {a : ℝ} (ha : 0 < a) :
    HasSum (fun k : ℕ => 1 / (a ^ 2 + ((2 * k : ℕ) : ℝ) ^ 2)) (invSqSumValue (a / 2) / 4) := by
  convert (hasSum_inv_sq_add_sq (half_pos ha)).div_const 4 using 1
  funext k; push_cast; field_simp; norm_num

theorem hasSum_inv_sq_add_odd {a : ℝ} (ha : 0 < a) :
    HasSum (fun k : ℕ => 1 / (a ^ 2 + ((2 * k + 1 : ℕ) : ℝ) ^ 2))
      (invSqSumValue a - invSqSumValue (a / 2) / 4) := by
  have hf := hasSum_inv_sq_add_sq ha
  have hodd : Summable (fun k : ℕ => 1 / (a ^ 2 + ((2 * k + 1 : ℕ) : ℝ) ^ 2)) :=
    hf.summable.comp_injective (i := fun k : ℕ => 2 * k + 1) fun _ _ h => by simp only at h; omega
  have h3 := hf.unique (HasSum.even_add_odd (f := fun n : ℕ => 1 / (a ^ 2 + (n : ℝ) ^ 2))
    (hasSum_inv_sq_add_even ha) hodd.hasSum)
  rw [show invSqSumValue a - invSqSumValue (a / 2) / 4 =
    ∑' k : ℕ, 1 / (a ^ 2 + ((2 * k + 1 : ℕ) : ℝ) ^ 2) by linarith]
  exact hodd.hasSum

/-- The `tanh` partial fractions: `∑_{k ≥ 0} 1 / (a² + (2k+1)²) = (π / (4a)) tanh (π a / 2)`. -/
theorem hasSum_inv_sq_add_odd_sq {a : ℝ} (ha : 0 < a) :
    HasSum (fun k : ℕ => 1 / (a ^ 2 + (2 * (k : ℝ) + 1) ^ 2))
      (π / (4 * a) * Real.tanh (π * a / 2)) := by
  have H := two_coth_two_mul_sub_coth (π * a / 2) (by positivity)
  rw [show 2 * (π * a / 2) = π * a by ring] at H
  rw [Real.tanh_eq_sinh_div_cosh, ← H]
  convert hasSum_inv_sq_add_odd ha using 1
  · funext k; push_cast; rfl
  · simp only [invSqSumValue]
    rw [show π * (a / 2) = π * a / 2 by ring]
    have ha0 : a ≠ 0 := ha.ne'
    field_simp; ring

/-- The alternating series
`∑_{n ≥ 0} (-1)^n / (a² + n²) = π / (2a sinh (π a)) + 1 / (2a²)`. -/
theorem hasSum_alt_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (a ^ 2 + (n : ℝ) ^ 2))
      (π / (2 * a * Real.sinh (π * a)) + 1 / (2 * a ^ 2)) := by
  have h := HasSum.even_add_odd (f := fun n : ℕ => (-1 : ℝ) ^ n / (a ^ 2 + (n : ℝ) ^ 2))
    (by convert hasSum_inv_sq_add_even ha using 1; funext k; simp [pow_mul])
    (by convert (hasSum_inv_sq_add_odd ha).neg using 1; funext k; simp [pow_succ, pow_mul]; ring)
  convert h using 1
  have H := coth_sub_coth_two_mul (π * a / 2) (by positivity)
  rw [show 2 * (π * a / 2) = π * a by ring] at H
  simp only [invSqSumValue]
  rw [show π * (a / 2) = π * a / 2 by ring,
    show Real.cosh (π * a / 2) / Real.sinh (π * a / 2) =
      Real.cosh (π * a) / Real.sinh (π * a) + 1 / Real.sinh (π * a) by linarith]
  have ha0 : a ≠ 0 := ha.ne'
  have hs : Real.sinh (π * a) ≠ 0 := (Real.sinh_pos_iff.2 (by positivity)).ne'
  field_simp; ring

end PottsDiscontinuity
