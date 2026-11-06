module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Only the listed proof slices are retained. Mathlib retains Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.GaussianAveraging
public import MathCollab.Density.AbelZetaGrowth
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger
open MathCollab.Density.ZetaGrowth
open scoped Interval
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem exists_zetaMomentCriticalNorm_linear_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, zetaMomentCriticalNorm t ≤ C * (1 + |t|) := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) continuous_zetaMomentCriticalNorm.continuousOn
  let C : ℝ := max 5 (max D 1)
  have hC5 : 5 ≤ C := le_max_left _ _
  have hCD : D ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨C, by linarith, ?_⟩
  pm_8632 t ht
  · have hz0 : 0 ≤ zetaMomentCriticalNorm t := norm_nonneg _
    have h := hD t (abs_le.mp ht)
    rw [Real.norm_of_nonneg hz0] at h
    nlinarith [abs_nonneg t]
  · have hfar : 1 ≤ |t| := (lt_of_not_ge ht).le
    have hζ := norm_riemannZeta_le_five_mul_norm
      (s := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) (by norm_num) (by simp_all)
    have hs : ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ ≤ 1 / 2 + |t| := by
      simpa [Real.norm_eq_abs] using norm_add_le ((1 / 2 : ℝ) : ℂ) ((t : ℂ) * I)
    change zetaMomentCriticalNorm t ≤ _ at hζ
    calc
      _ ≤ 5 * (1 / 2 + |t|) := hζ.trans (mul_le_mul_of_nonneg_left hs (by norm_num))
      _ ≤ C * (1 + |t|) := by nlinarith [abs_nonneg t]

def zetaSquareCenteredGaussian (T G x : ℝ) : ℝ :=
  Real.exp (-x ^ 2) * zetaMomentCriticalNorm (T + G * x) ^ 2

theorem continuous_zetaSquareCenteredGaussian (T G : ℝ) :
    Continuous (zetaSquareCenteredGaussian T G) := by
  unfold zetaSquareCenteredGaussian
  have hz := continuous_zetaMomentCriticalNorm.comp
    (show Continuous (fun x : ℝ => T + G * x) by fun_prop)
  fun_prop (disch := assumption)

theorem zetaSquareCenteredGaussian_nonneg (T G x : ℝ) :
    0 ≤ zetaSquareCenteredGaussian T G x :=
  mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

theorem zetaSquareCenteredGaussian_majorant {C : ℝ}
    (hC : ∀ t : ℝ, zetaMomentCriticalNorm t ≤ C * (1 + |t|))
    (hC0 : 0 ≤ C) (T G x : ℝ) :
    zetaSquareCenteredGaussian T G x ≤
      C ^ 2 * (1 + |T| + |G|) ^ 2 * (Real.exp (-x ^ 2) * (1 + |x|) ^ 2) := by
  have hscale : 1 + |T + G * x| ≤ (1 + |T| + |G|) * (1 + |x|) := by
    have h := abs_add_le T (G * x)
    rw [abs_mul] at h
    nlinarith [abs_nonneg T, abs_nonneg G, abs_nonneg x,
      mul_nonneg (abs_nonneg T) (abs_nonneg x)]
  have hz := (hC (T + G * x)).trans (mul_le_mul_of_nonneg_left hscale hC0)
  have hz0 : 0 ≤ zetaMomentCriticalNorm (T + G * x) := norm_nonneg _
  unfold zetaSquareCenteredGaussian
  calc
    _ ≤ Real.exp (-x ^ 2) * (C * ((1 + |T| + |G|) * (1 + |x|))) ^ 2 := by gcongr
    _ = _ := by ring

theorem integrable_zetaSquareCenteredGaussian (T G : ℝ) :
    Integrable (zetaSquareCenteredGaussian T G) := by
  obtain ⟨C, hC1, hC⟩ := exists_zetaMomentCriticalNorm_linear_bound
  have hGauss : Integrable (fun x : ℝ => Real.exp (-x ^ 2) * (1 + |x|) ^ 2) := by
    simpa using integrable_exp_sub_mul_sq_mul_add_abs_pow (C := 1) 0
      (by norm_num : (0 : ℝ) < 1) 2
  apply (hGauss.const_mul (C ^ 2 * (1 + |T| + |G|) ^ 2)).mono'
    (continuous_zetaSquareCenteredGaussian T G).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (zetaSquareCenteredGaussian_nonneg T G x)]
  exact zetaSquareCenteredGaussian_majorant hC (by linarith) T G x

theorem zetaGaussianWeight_affine (T x : ℝ) {G : ℝ} (hG : G ≠ 0) :
    zetaGaussianWeight T G (T + G * x) = Real.exp (-x ^ 2) := by
  simp [zetaGaussianWeight, hG]

theorem zetaSquareGaussianWindow_eq_centered (T L : ℝ) {G : ℝ} (hG : G ≠ 0) :
    zetaSquareGaussianWindow T G L = G * ∫ x in -L..L, zetaSquareCenteredGaussian T G x := by
  have h := intervalIntegral.smul_integral_comp_add_mul
    (fun t => zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2)
    (a := -L) (b := L) G T
  simp only [smul_eq_mul, zetaGaussianWeight_affine T _ hG] at h
  simpa only [mul_neg, ← sub_eq_add_neg, zetaSquareGaussianWindow,
    zetaSquareCenteredGaussian] using h.symm

def zetaSquareGaussianMean (T G : ℝ) : ℝ := G * ∫ x : ℝ, zetaSquareCenteredGaussian T G x

theorem zetaSquareCenteredGaussian_tail_majorant {C : ℝ}
    (hC : ∀ t : ℝ, zetaMomentCriticalNorm t ≤ C * (1 + |t|)) (hC0 : 0 ≤ C)
    (T G : ℝ) {L x : ℝ} (hL : 0 ≤ L) (hx : L ≤ |x|) :
    zetaSquareCenteredGaussian T G x ≤
      C ^ 2 * (1 + |T| + |G|) ^ 2 * Real.exp (-L ^ 2 / 2) *
        (Real.exp (-x ^ 2 / 2) * (1 + |x|) ^ 2) := by
  pm_8516 hsquare L
  have hGauss : Real.exp (-x ^ 2) ≤ Real.exp (-L ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ C ^ 2 * (1 + |T| + |G|) ^ 2 *
        (Real.exp (-x ^ 2) * (1 + |x|) ^ 2) := zetaSquareCenteredGaussian_majorant hC hC0 T G x
    _ ≤ C ^ 2 * (1 + |T| + |G|) ^ 2 *
        ((Real.exp (-L ^ 2 / 2) * Real.exp (-x ^ 2 / 2)) * (1 + |x|) ^ 2) := by
      gcongr
    _ = _ := by ring

/-- A single constant controls every actual Gaussian tail. -/
theorem exists_zetaSquareGaussian_tail_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T G L : ℝ, 0 < G → 0 ≤ L →
      0 ≤ zetaSquareGaussianMean T G - zetaSquareGaussianWindow T G L ∧
      zetaSquareGaussianMean T G - zetaSquareGaussianWindow T G L ≤
        C * G * (1 + |T| + G) ^ 2 * Real.exp (-L ^ 2 / 2) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_zetaMomentCriticalNorm_linear_bound
  let K : ℝ → ℝ := fun x => Real.exp (-x ^ 2 / 2) * (1 + |x|) ^ 2
  have hK0 : ∀ x, 0 ≤ K x := by intro x; dsimp [K]; positivity
  have hK : Integrable K := by
    convert integrable_exp_sub_mul_sq_mul_add_abs_pow (C := 1) 0
      (by norm_num : (0 : ℝ) < 1 / 2) 2 using 1
    funext x
    dsimp [K]
    congr 2
    ring
  refine ⟨C₀ ^ 2 * ∫ x : ℝ, K x, mul_nonneg (sq_nonneg _) (integral_nonneg hK0), ?_⟩
  intro T G L hG hL
  have hsplit : zetaSquareGaussianMean T G - zetaSquareGaussianWindow T G L =
      G * ∫ x in (Ioc (-L) L)ᶜ, zetaSquareCenteredGaussian T G x := by
    rw [zetaSquareGaussianWindow_eq_centered T L hG.ne', zetaSquareGaussianMean,
      intervalIntegral.integral_of_le (by linarith)]
    rw [← mul_sub, ← setIntegral_compl measurableSet_Ioc (integrable_zetaSquareCenteredGaussian T G)]
  rw [hsplit]
  refine ⟨mul_nonneg hG.le (integral_nonneg (zetaSquareCenteredGaussian_nonneg T G)), ?_⟩
  have hi : (∫ x in (Ioc (-L) L)ᶜ, zetaSquareCenteredGaussian T G x) ≤
      C₀ ^ 2 * (1 + |T| + G) ^ 2 * Real.exp (-L ^ 2 / 2) * ∫ x : ℝ, K x := by
    calc
      _ ≤ ∫ x in (Ioc (-L) L)ᶜ,
          (C₀ ^ 2 * (1 + |T| + G) ^ 2 * Real.exp (-L ^ 2 / 2)) * K x := by
        apply integral_mono_ae (integrable_zetaSquareCenteredGaussian T G).integrableOn
          (hK.const_mul _).integrableOn
        pm_426 hx' L
        simpa only [abs_of_pos hG, K] using
          zetaSquareCenteredGaussian_tail_majorant hbound (by linarith) T G hL hx'
      _ = (C₀ ^ 2 * (1 + |T| + G) ^ 2 * Real.exp (-L ^ 2 / 2)) *
          ∫ x in (Ioc (-L) L)ᶜ, K x := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_le_integral hK
        (Eventually.of_forall hK0)) (by positivity)
  calc
    _ ≤ G * (C₀ ^ 2 * (1 + |T| + G) ^ 2 * Real.exp (-L ^ 2 / 2) * ∫ x : ℝ, K x) :=
      mul_le_mul_of_nonneg_left hi hG.le
    _ = _ := by ring

/-- The source logarithmic window has a uniform arbitrarily small tail,
with the width factor `G` retained and one threshold before all widths. -/
theorem exists_zetaSquareGaussian_log_tail_bound (A : ℝ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T G : ℝ, T₀ ≤ T → 0 < G → G ≤ T →
      0 ≤ zetaSquareGaussianMean T G - zetaSquareGaussianWindow T G (Real.log T) ∧
      zetaSquareGaussianMean T G - zetaSquareGaussianWindow T G (Real.log T) ≤ G * T ^ (-A) := by
  obtain ⟨C, hC0, htail⟩ := exists_zetaSquareGaussian_tail_bound
  let T₀ := max 1 (max (9 * C) (Real.exp (2 * (A + 3))))
  pm_4889
  intro T G hT₀ hG hGT
  pm_306 hT1 hT₀ hT
  have hTC : 9 * C ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT₀)
  have hTexp : Real.exp (2 * (A + 3)) ≤ T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hT₀)
  have hlog0 := Real.log_nonneg hT1
  have hlog : 2 * (A + 3) ≤ Real.log T := by
    pm_7851
  have hexp : Real.exp (-(Real.log T) ^ 2 / 2) ≤ T ^ (-(A + 3)) := by
    pm_7720 hlog
  obtain ⟨hlower, hupper⟩ := htail T G (Real.log T) hG hlog0
  refine ⟨hlower, hupper.trans ?_⟩
  rw [abs_of_pos hT]
  calc
    _ ≤ C * G * (3 * T) ^ 2 * Real.exp (-(Real.log T) ^ 2 / 2) := by gcongr; linarith
    _ = (9 * C) * G * T ^ 2 * Real.exp (-(Real.log T) ^ 2 / 2) := by ring
    _ ≤ T * G * T ^ 2 * Real.exp (-(Real.log T) ^ 2 / 2) := by gcongr
    _ = G * T ^ 3 * Real.exp (-(Real.log T) ^ 2 / 2) := by ring
    _ ≤ G * T ^ 3 * T ^ (-(A + 3)) := by gcongr
    _ = G * T ^ (-A) := by
      rw [mul_assoc, ← Real.rpow_natCast T 3, ← Real.rpow_add hT]
      congr 2
      norm_num

end MathCollab.Density.Stronger.Atkinson
