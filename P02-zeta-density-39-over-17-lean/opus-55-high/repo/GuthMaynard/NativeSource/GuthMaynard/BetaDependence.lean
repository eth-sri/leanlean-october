module
public import GuthMaynard.NativeSource.GuthMaynard.ExtractSeparated
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Set
open scoped BigOperators

namespace GuthMaynard.NativeMoment

open Filter Asymptotics PhragmenLindelof

section
variable (k : ℕ)
include k
/-- The rational localization factor has norm at most one in the closed right half-plane. -/
lemma localizer_norm_le_one (H : ℝ) (hH : 0 < H) (w : ℂ)
    (hw : 0 ≤ w.re) : ‖((H : ℂ) / (H + w)) ^ k‖ ≤ 1 := by
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hden : H ≤ ‖(H : ℂ) + w‖ := by
    calc
      H ≤ |H + w.re| := by grind
      _ = |((H : ℂ) + w).re| := by simp
      _ ≤ ‖(H : ℂ) + w‖ := abs_re_le_norm _
  have hratio : H / ‖(H : ℂ) + w‖ ≤ 1 :=
    (div_le_one (hH.trans_le hden)).mpr hden
  exact pow_le_one₀ (by positivity) hratio

/-- Away from the central boundary segment, the rational localizer decays polynomially. -/
lemma localizer_norm_boundary_le (H R y : ℝ)
    (hH : 0 < H) (hR : 0 < R) (hy : R ≤ |y|) :
    ‖((H : ℂ) / (H + (y : ℂ) * I)) ^ k‖ ≤ (H / R) ^ k := by
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hden : |y| ≤ ‖(H : ℂ) + (y : ℂ) * I‖ := by
    calc
      |y| = |((H : ℂ) + (y : ℂ) * I).im| := by simp
      _ ≤ ‖(H : ℂ) + (y : ℂ) * I‖ := abs_im_le_norm _
  have hdenPos : 0 < ‖(H : ℂ) + (y : ℂ) * I‖ :=
    lt_of_lt_of_le (hR.trans_le hy) hden
  have hratio : H / ‖(H : ℂ) + (y : ℂ) * I‖ ≤ H / R := by
    exact div_le_div_of_nonneg_left hH.le hR (hy.trans hden)
  exact pow_le_pow_left₀ (by positivity) hratio k

/-- For a bounded horizontal displacement, the localizer loses less than one quarter. -/
lemma localizer_factor_gt_three_fourths (H a : ℝ)
    (hH : 0 < H) (ha : 0 ≤ a) (haOne : a ≤ 1) (hHk : 4 * (k : ℝ) < H) :
    3 / 4 < ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖ := by
  have hHa : 0 < H + a := by linarith
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hnorm : ‖(H : ℂ) + (a : ℂ)‖ = H + a := by
    rw [← ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHa]
  rw [hnorm]
  let r : ℝ := H / (H + a)
  pm_61 hr0 r
  have hBernoulli : 1 + (k : ℝ) * (r - 1) ≤ r ^ k := by
    exact one_add_mul_sub_le_pow (by linarith) k
  have hFrac : (k : ℝ) * a / (H + a) < 1 / 4 := by
    have hkA : (k : ℝ) * a ≤ k := by
      pm_1199 hk0 k
      nlinarith
    have hDiv : (k : ℝ) * a / (H + a) ≤ (k : ℝ) / H := by
      rw [div_le_div_iff₀ hHa hH]
      pm_1199 hk0 k
      nlinarith [mul_nonneg hk0 ha]
    have hkDiv : (k : ℝ) / H < 1 / 4 := by
      rw [div_lt_iff₀ hH]
      nlinarith
    grind
  have hrSub : r - 1 = -a / (H + a) := by
    dsimp [r]
    field_simp
    ring
  rw [hrSub] at hBernoulli
  have : 3 / 4 < 1 + (k : ℝ) * (-a / (H + a)) := by
    have hrewrite : (k : ℝ) * (-a / (H + a)) = -((k : ℝ) * a / (H + a)) := by
      ring
    rw [hrewrite]
    linarith
  grind
end

end GuthMaynard.NativeMoment
