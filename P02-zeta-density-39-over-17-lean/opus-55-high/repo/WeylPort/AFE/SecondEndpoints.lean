module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.SecondCoeffBounds
import WeylPort.Analytic.RealLaplace

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

section
variable (f g : ℝ → ℝ) (x : ℝ)
include f g x
/-- The source H amplitude is nonnegative for all actual functions. -/
theorem secondH_nonneg : 0 ≤ secondH f g x := by
  unfold secondH
  positivity

/-- The source H₁ amplitude is nonnegative for all actual functions. -/
theorem secondH1_nonneg : 0 ≤ secondH1 f g x := by
  unfold secondH1
  positivity
end

/-- The actual positive oscillatory tail has a uniform bound even at integer endpoints. -/
theorem norm_positiveTail_le_two {y : ℝ} (hy : 0 < y) (x : ℝ) : ‖positiveTail x y‖ ≤ 2 := by
  rw [positiveTail_eq_shift hy]
  pm_5564 hs reciprocal_square_series_bounds
  have hb : ‖∑' n : ℕ, (1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))) • expMode x (n + 1)‖ ≤
      ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
    apply tsum_of_norm_bounded hs.1.hasSum
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))),
      norm_expMode, mul_one]
    apply one_div_le_one_div_of_le (by positivity : 0 < ((n : ℝ) + 1) ^ 2)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  grind

/-- At small positive derivative, the actual negative tail is uniformly bounded for every cutoff and endpoint. -/
theorem norm_negativeTail_le_four {M : ℕ} {y : ℝ} (hy : 0 < y) (hyhalf : y ≤ 1 / 2) (x : ℝ) :
    ‖negativeTail M x y‖ ≤ 4 := by
  have hM : y < (M : ℝ) + 1 := by grind
  rw [negativeTail_eq_shift hy hM]
  pm_5564 hs reciprocal_square_series_bounds
  have hb : ‖∑' n : ℕ, (1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - y))) • expMode x (n + M + 1)‖ ≤
      2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
    apply tsum_of_norm_bounded (hs.1.hasSum.mul_left 2)
    intro n
    pm_14
    pm_1199 hmn M
    have hgap : 0 < (n : ℝ) + M + 1 - y := by linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - y))),
      norm_expMode, mul_one]
    rw [mul_one_div]
    pm_23
    have hprod := mul_nonneg hmn (by positivity : 0 ≤ 2 * (n : ℝ) + M + 1)
    have hyprod := mul_nonneg (by positivity : 0 ≤ (n : ℝ) + M + 1) (show 0 ≤ 1 - 2 * y by linarith)
    nlinarith
  have hsum : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by grind
  grind

end DhimanKadiriQuesadaHerrera2026
