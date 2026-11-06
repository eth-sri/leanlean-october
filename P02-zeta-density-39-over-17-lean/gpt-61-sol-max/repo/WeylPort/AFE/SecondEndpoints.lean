module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.SecondCoeffBounds

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Actual second-order Poisson endpoint simplifications -/

namespace DhimanKadiriQuesadaHerrera2026
open Complex MeasureTheory

/-- Conjugation changes the sign of the actual positive-tail endpoint. -/
theorem conj_positiveTail (x y : ℝ) : starRingEnd ℂ (positiveTail x y) = positiveTail (-x) y := by
  unfold positiveTail
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  split_ifs
  · rw [map_div₀, conj_expMode, Complex.conj_ofReal]
  · simp

/-- The positive-tail norm is unchanged when the endpoint is negated. -/
theorem norm_positiveTail_neg (x y : ℝ) : ‖positiveTail (-x) y‖ = ‖positiveTail x y‖ := by
  rw [← conj_positiveTail, Complex.norm_conj]

/-- The source H amplitude is nonnegative for all actual functions. -/
theorem secondH_nonneg (f g : ℝ → ℝ) (x : ℝ) : 0 ≤ secondH f g x := by
  unfold secondH
  positivity

/-- The source H₁ amplitude is nonnegative for all actual functions. -/
theorem secondH1_nonneg (f g : ℝ → ℝ) (x : ℝ) : 0 ≤ secondH1 f g x := by
  unfold secondH1
  positivity

/-- The actual positive oscillatory tail has a uniform bound even at integer endpoints. -/
theorem norm_positiveTail_le_two {y : ℝ} (hy : 0 < y) (x : ℝ) : ‖positiveTail x y‖ ≤ 2 := by
  rw [positiveTail_eq_shift hy]
  have hs := reciprocal_square_series_bounds (by norm_num : (0 : ℝ) < 1)
  have hb : ‖∑' n : ℕ, (1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))) • expMode x (n + 1)‖ ≤
      ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
    apply tsum_of_norm_bounded hs.1.hasSum
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))),
      norm_expMode, mul_one]
    apply one_div_le_one_div_of_le (by positivity : 0 < ((n : ℝ) + 1) ^ 2)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact hb.trans (by simpa only [one_pow, div_one, one_add_one_eq_two] using hs.2.2)

/-- At small positive derivative, the actual negative tail is uniformly bounded for every cutoff and endpoint. -/
theorem norm_negativeTail_le_four {M : ℕ} {y : ℝ} (hy : 0 < y) (hyhalf : y ≤ 1 / 2) (x : ℝ) :
    ‖negativeTail M x y‖ ≤ 4 := by
  have hM : y < (M : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  rw [negativeTail_eq_shift hy hM]
  have hs := reciprocal_square_series_bounds (by norm_num : (0 : ℝ) < 1)
  have hb : ‖∑' n : ℕ, (1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - y))) • expMode x (n + M + 1)‖ ≤
      2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
    apply tsum_of_norm_bounded (hs.1.hasSum.mul_left 2)
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmn : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    have hgap : 0 < (n : ℝ) + M + 1 - y := by linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - y))),
      norm_expMode, mul_one]
    rw [mul_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hprod := mul_nonneg hmn (by positivity : 0 ≤ 2 * (n : ℝ) + M + 1)
    have hyprod := mul_nonneg (by positivity : 0 ≤ (n : ℝ) + M + 1) (show 0 ≤ 1 - 2 * y by linarith)
    nlinarith
  have hsum : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by simpa only [one_pow, div_one, one_add_one_eq_two] using hs.2.2
  exact hb.trans (by linarith)


