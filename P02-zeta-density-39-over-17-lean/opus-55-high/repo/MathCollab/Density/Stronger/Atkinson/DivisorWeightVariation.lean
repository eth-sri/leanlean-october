module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorWeightSource
public import MathCollab.Density.Stronger.Atkinson.GammaQuadratic
import WeylPort.Analytic.RealLaplace

public section

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger.Fourth
open scoped Interval ComplexConjugate
namespace MathCollab.Density.Stronger.Atkinson


theorem hasDerivAt_zetaDivisorWeightKernel_real (q : ℂ) {w : ℂ} (hw : w ≠ 0) (v : ℝ) :
    HasDerivAt (fun x : ℝ => zetaDivisorWeightKernel (q + (x : ℂ)) w)
      (-zetaDivisorWeightNumerator (q + (v : ℂ)) w) v := by
  have he := (((hasDerivAt_id v).ofReal_comp.const_add q).neg.mul_const w).cexp
  pm_576

section
variable {B : ℝ} (hB : 0 ≤ B)
include B hB
theorem norm_zetaDivisorWeightKernel_real_sub_le
    {q : ℂ} (hq : |q.im| ≤ B) (h u : ℝ) :
    ‖zetaDivisorWeightKernel (q + (h : ℂ)) (1 + (u : ℂ) * I) -
      zetaDivisorWeightKernel q (1 + (u : ℂ) * I)‖ ≤
      (625 * Real.exp (100 + B ^ 2 / 2)) * Real.exp (-q.re + |h|) *
        zetaDivisorWeightEnvelope u * |h| := by
  pm_4472
  have hw : w ≠ 0 := by
    pm_532 he w
  have hbound (v : ℝ) (hv : v ∈ Icc (-|h|) |h|) :
      ‖-zetaDivisorWeightNumerator (q + (v : ℂ)) w‖ ≤
        (625 * Real.exp (100 + B ^ 2 / 2)) * Real.exp (-q.re + |h|) * zetaDivisorWeightEnvelope u := by
    rw [norm_neg]
    have he := norm_zetaDivisorWeightNumerator_right_le hB
      (q := q + (v : ℂ)) (by simp_all) u
    simp only [add_re, ofReal_re] at he
    apply he.trans
    pm_7002
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v _ => (hasDerivAt_zetaDivisorWeightKernel_real q hw v).hasDerivWithinAt)
    hbound (convex_Icc (-|h|) |h|) (x := 0) (y := h)
    (by grind) ⟨neg_abs_le h, le_abs_self h⟩
  aesop

theorem exists_norm_zetaDivisorWeight_real_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℂ, |q.im| ≤ B → ∀ h : ℝ,
      ‖zetaDivisorWeight (q + (h : ℂ)) - zetaDivisorWeight q‖ ≤
        C * |h| * Real.exp |h| * Real.exp (-q.re) := by
  pm_4367
  intro q hq h
  let e := fun u : ℝ => zetaDivisorWeightKernel (q + (h : ℂ)) (1 + (u : ℂ) * I) -
    zetaDivisorWeightKernel q (1 + (u : ℂ) * I)
  have hi : Integrable e := (integrable_zetaDivisorWeightKernel_right (q + (h : ℂ))).sub
    (integrable_zetaDivisorWeightKernel_right q)
  have heq : zetaDivisorWeight (q + (h : ℂ)) - zetaDivisorWeight q =
      (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, e u := by
    unfold zetaDivisorWeight
    rw [← mul_sub, ← integral_sub (integrable_zetaDivisorWeightKernel_right (q + (h : ℂ)))
      (integrable_zetaDivisorWeightKernel_right q)]
  have hiBound : (∫ u : ℝ, ‖e u‖) ≤ (M * Real.exp (-q.re + |h|) * |h|) * J := by
    have hmajor := (integrable_zetaDivisorWeightEnvelope.const_mul (M * Real.exp (-q.re + |h|) * |h|))
    have hb (u : ℝ) : ‖e u‖ ≤ (M * Real.exp (-q.re + |h|) * |h|) * zetaDivisorWeightEnvelope u := by
      have hm := norm_zetaDivisorWeightKernel_real_sub_le hB hq h u
      dsimp [e, M]
      nlinarith
    simpa only [integral_const_mul] using integral_mono hi.norm hmajor hb
  rw [heq, norm_mul]
  pm_4368
  pm_6648 hiBound
  calc
    _ = (M * J / (2 * Real.pi)) * |h| * Real.exp |h| * Real.exp (-q.re) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := by
      gcongr
      linarith

/-- Reflection controls variation on both sides of the source cutoff.
The same constant works for all real translations and imaginary arguments
in the fixed strip, including zero translation. -/
theorem exists_norm_zetaDivisorWeight_real_sub_min_le :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℂ, |q.im| ≤ B → ∀ h : ℝ,
      ‖zetaDivisorWeight (q + (h : ℂ)) - zetaDivisorWeight q‖ ≤
        (C * |h| * Real.exp |h|) * min (Real.exp (-q.re)) (Real.exp q.re) := by
  pm_1062 C hC hbound exists_norm_zetaDivisorWeight_real_sub_le hB
  intro q hq h
  have hp := hbound q hq h
  have hm := hbound (-q) (by simpa using hq) (-h)
  have heq : zetaDivisorWeight (-q + ((-h : ℝ) : ℂ)) - zetaDivisorWeight (-q) =
      -(zetaDivisorWeight (q + (h : ℂ)) - zetaDivisorWeight q) := by
    have h1 := zetaDivisorWeight_add_neg (q + (h : ℂ))
    have h2 := zetaDivisorWeight_add_neg q
    rw [show -q + ((-h : ℝ) : ℂ) = -(q + (h : ℂ)) by push_cast; ring]
    linear_combination h1 - h2
  rw [heq, norm_neg] at hm
  simp only [abs_neg, neg_re, neg_neg] at hm
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ C * |h| * Real.exp |h|)]
  exact le_min hp hm
end

section
variable {T x : ℝ} (hT : 0 < T)
include T x hT
theorem abs_log_height_shift_le (hx : |x| ≤ T / 2) :
    |Real.log (T + x) - Real.log T| ≤ 2 * |x| / T := by
  have h := abs_log_shift_sub_linear_le hT hx
  have htri := abs_add_le (Real.log (T + x) - Real.log T - x / T) (x / T)
  have habs : |x / T| = |x| / T := by rw [abs_div, abs_of_pos hT]
  have hsq : 2 * x ^ 2 / T ^ 2 ≤ |x| / T := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hT) hT).mpr
    have hp := mul_le_mul_of_nonneg_left hx (abs_nonneg x)
    have hpT := mul_le_mul_of_nonneg_right hp hT.le
    nlinarith [sq_abs x]
  rw [sub_add_cancel, habs] at htri
  calc
    _ ≤ 2 * (|x| / T) := by linarith
    _ = _ := by ring

theorem zetaDivisorWeightArgument_height_shift
    (hx : 0 < T + x) (n : ℕ) :
    zetaDivisorWeightArgument (T + x) n = zetaDivisorWeightArgument T n +
      ((Real.log T - Real.log (T + x) : ℝ) : ℂ) := by
  unfold zetaDivisorWeightArgument zetaGammaLeadingLog
  pm_8225 hx.ne' hT.ne'
  push_cast
  ring
end

theorem exp_zetaDivisorWeightArgument_re {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n) :
    Real.exp (zetaDivisorWeightArgument T n).re = (2 * Real.pi * (n : ℝ)) / T := by
  rw [zetaDivisorWeightArgument_re, Real.exp_sub,
    Real.exp_log (by positivity), Real.exp_log (by positivity)]
  field_simp

/-- The actual source weight varies by the relative height displacement,
with decay on both sides of its cutoff. One constant works for every
positive height, every closed half-height window and all positive indices. -/
theorem exists_norm_source_zetaDivisorWeight_height_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → ∀ x : ℝ, |x| ≤ T / 2 → ∀ n : ℕ, 0 < n →
      ‖zetaDivisorWeight (zetaDivisorWeightArgument (T + x) n) -
        zetaDivisorWeight (zetaDivisorWeightArgument T n)‖ ≤
      C * (|x| / T) * min (T / (2 * Real.pi * (n : ℝ))) ((2 * Real.pi * (n : ℝ)) / T) := by
  pm_1336 hbound exists_norm_zetaDivisorWeight_real_sub_min_le
  refine ⟨2 * C * Real.exp 1, by positivity, ?_⟩
  intro T hT x hx n hn
  have hTx : 0 < T + x := by have := neg_abs_le x; linarith
  let h : ℝ := Real.log T - Real.log (T + x)
  have habs : |h| ≤ 2 * |x| / T := by
    dsimp [h]
    rw [abs_sub_comm]
    exact abs_log_height_shift_le hT hx
  have hsmall : |h| ≤ 1 := habs.trans ((div_le_iff₀ hT).mpr (by linarith))
  have he := hbound (zetaDivisorWeightArgument T n)
    (by rw [zetaDivisorWeightArgument_im, abs_of_pos (by positivity)]) h
  rw [exp_neg_zetaDivisorWeightArgument_re hT hn, exp_zetaDivisorWeightArgument_re hT hn] at he
  rw [zetaDivisorWeightArgument_height_shift hT hTx]
  apply he.trans
  have hm : 0 ≤ min (T / (2 * Real.pi * (n : ℝ))) ((2 * Real.pi * (n : ℝ)) / T) := by positivity
  apply mul_le_mul_of_nonneg_right _ hm
  calc
    _ ≤ C * (2 * |x| / T) * Real.exp 1 := by gcongr
    _ = _ := by ring

end MathCollab.Density.Stronger.Atkinson
