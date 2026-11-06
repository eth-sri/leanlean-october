module
import Mathlib
public import GuthMaynard.NativeSource.GuthMaynard.ExtractSeparated
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

open Complex
open scoped BigOperators

namespace GuthMaynard.NativeMoment

open Filter Asymptotics

/-- The rational localization factor has norm at most one in the closed right half-plane. -/
lemma localizer_norm_le_one (k : ℕ) (H : ℝ) (hH : 0 < H) (w : ℂ)
    (hw : 0 ≤ w.re) : ‖((H : ℂ) / (H + w)) ^ k‖ ≤ 1 := by
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hden : H ≤ ‖(H : ℂ) + w‖ := by
    calc
      H ≤ |H + w.re| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      _ = |((H : ℂ) + w).re| := by simp
      _ ≤ ‖(H : ℂ) + w‖ := abs_re_le_norm _
  bound

/-- Away from the central boundary segment, the rational localizer decays polynomially. -/
lemma localizer_norm_boundary_le (k : ℕ) (H R y : ℝ)
    (hH : 0 < H) (hR : 0 < R) (hy : R ≤ |y|) :
    ‖((H : ℂ) / (H + (y : ℂ) * I)) ^ k‖ ≤ (H / R) ^ k := by
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hden : |y| ≤ ‖(H : ℂ) + (y : ℂ) * I‖ := by
    calc
      |y| = |((H : ℂ) + (y : ℂ) * I).im| := by simp
      _ ≤ ‖(H : ℂ) + (y : ℂ) * I‖ := abs_im_le_norm _
  bound

/-- For a bounded horizontal displacement, the localizer loses less than one quarter. -/
lemma localizer_factor_gt_three_fourths (k : ℕ) (H a : ℝ)
    (hH : 0 < H) (ha : 0 ≤ a) (haOne : a ≤ 1) (hHk : 4 * (k : ℝ) < H) :
    3 / 4 < ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖ := by
  have hHa : 0 < H + a := by linarith
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hnorm : ‖(H : ℂ) + (a : ℂ)‖ = H + a := by
    rw [← ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHa]
  rw [hnorm]
  let r := H / (H + a)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hBernoulli : 1 + (k : ℝ) * (r - 1) ≤ r ^ k := by
    exact one_add_mul_sub_le_pow (by linarith) k
  have hFrac : (k : ℝ) * a / (H + a) < 1 / 4 := by field_simp <;> nlinarith
  have hrSub : r - 1 = -a / (H + a) := by
    dsimp [r]
    field_simp
    ring
  rw [hrSub] at hBernoulli
  grind


