module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.FiniteExponentialSums

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The finite arithmetic term in the weighted-integral estimate

The half-integer reciprocal sum is evaluated using the actual digamma recurrence.
The resulting bound preserves the correction 1/(8y²) in source Lemma 5.
-/

namespace DhimanKadiriQuesadaHerrera2026

open scoped BigOperators

/-- The real-valued positive-index sum has the same precise endpoint convention. -/
theorem sum_Icc_one_eq_sum_range_real (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ n ∈ Finset.range N, f (n + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  grind

section
variable (N : ℕ)
include N
/-- The weighted alternating prefix has an exact closed form for either parity. -/
theorem alternating_linear_sum_eq :
    (∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m * (m : ℝ)) =
      ((-1 : ℝ) ^ N * (2 * (N : ℝ) + 1) - 1) / 4 := by
  rw [sum_Icc_one_eq_sum_range_real]
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

/-- The weighted alternating boundary term keeps the sharp half-size growth. -/
theorem abs_alternating_linear_sum_le :
    |∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m * (m : ℝ)| ≤ ((N : ℝ) + 1) / 2 := by
  rw [alternating_linear_sum_eq, abs_div]
  have h := abs_sub ((-1 : ℝ) ^ N * (2 * (N : ℝ) + 1)) 1
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (show 0 ≤ 2 * (N : ℝ) + 1 by positivity)] at h
  rw [show |(4 : ℝ)| = 4 by norm_num]
  linarith

/-- The same boundary estimate holds for the literal complex alternating sum. -/
theorem norm_alternating_linear_sum_le :
    ‖∑ m ∈ Finset.Icc 1 N, (-1 : ℂ) ^ m * (m : ℂ)‖ ≤ ((N : ℝ) + 1) / 2 := by
  have he : (∑ m ∈ Finset.Icc 1 N, (-1 : ℂ) ^ m * (m : ℂ)) =
      ((∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m * (m : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact abs_alternating_linear_sum_le N

/-- The unweighted complex alternating boundary sum is uniformly at most one. -/
theorem norm_alternating_sum_le_one :
    ‖∑ m ∈ Finset.Icc 1 N, (-1 : ℂ) ^ m‖ ≤ 1 := by
  have hs : Real.sin (Real.pi * (1 / 2)) ≠ 0 := by
    rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
    norm_num
  have h := norm_finiteS0_le hs (N : ℝ)
  have hm (m : ℕ) : expMode (1 / 2) m = (-1 : ℂ) ^ m := by
    simpa only [Int.cast_zero, zero_add] using expMode_half_integer 0 m
  simpa only [finiteS0, Nat.floor_natCast, hm, show Real.pi * (1 / 2) = Real.pi / 2 by ring,
    Real.sin_pi_div_two, abs_one, div_one] using h
end

end DhimanKadiriQuesadaHerrera2026
