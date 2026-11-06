module
/-
Selected exact two-pole Gamma-zeta-square shifts adapted from Scott McColm,
PointMeanMellinShift.lean and PointMeanContourBasic.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See ../../../../../third_party/twelfth/POINT_MEAN_SHIFT_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
All residues, horizontal limits, vertical integrability and the actual
smoothed divisor identity are proved imports, not theorem hypotheses.
-/
public import MathCollab.Density.Stronger.PointMean.MovingPole
public import MathCollab.Density.Stronger.PointMean.DivisorMellin
public import MathCollab.Density.Stronger.PointMean.MellinHorizontal
public import MathCollab.Density.Stronger.PointMean.MellinVertical
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Set MeasureTheory Filter Topology
open MathCollab.Density.Contour
open scoped Interval
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

def VerticalIntegral (f : ℂ → ℂ) (a : ℝ) : ℂ :=
  I • ∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I)

def VerticalIntegral' (f : ℂ → ℂ) (a : ℝ) : ℂ :=
  (1 / (2 * Real.pi * I) : ℂ) • VerticalIntegral f a

theorem pintz2023_RectangleIntegral'_eq_edges
    (f : ℂ → ℂ) (a b R : ℝ) :
    RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I) =
      HIntegral' f a b (-R) - HIntegral' f a b R +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-R)..R, f ((b : ℂ) + (u : ℂ) * I)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-R)..R, f ((a : ℂ) + (u : ℂ) * I)) := by
  unfold RectangleIntegral' RectangleIntegral HIntegral' HIntegral VIntegral
  simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im, smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring
private theorem tendsto_rectangleIntegral'_vertical_sub
    {f : ℂ → ℂ} {a b : ℝ}
    (hBottom : Tendsto (fun R : ℝ => HIntegral' f a b (-R)) atTop (nhds 0))
    (hTop : Tendsto (fun R : ℝ => HIntegral' f a b R) atTop (nhds 0))
    (hIntA : Integrable (fun u : ℝ => f ((a : ℂ) + (u : ℂ) * I)))
    (hIntB : Integrable (fun u : ℝ => f ((b : ℂ) + (u : ℂ) * I))) :
    Tendsto (fun R : ℝ =>
      RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I)) atTop
      (nhds (VerticalIntegral' f b - VerticalIntegral' f a)) := by pm_4440

private theorem verticalIntegral'_sub_eq_of_eventual_rectangle
    {f : ℂ → ℂ} {a b : ℝ} {A : ℂ}
    (hBottom : Tendsto (fun R : ℝ => HIntegral' f a b (-R)) atTop (nhds 0))
    (hTop : Tendsto (fun R : ℝ => HIntegral' f a b R) atTop (nhds 0))
    (hIntA : Integrable (fun u : ℝ => f ((a : ℂ) + (u : ℂ) * I)))
    (hIntB : Integrable (fun u : ℝ => f ((b : ℂ) + (u : ℂ) * I)))
    (hFinite : ∀ᶠ R : ℝ in atTop,
      RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I) = A) :
    VerticalIntegral' f b - VerticalIntegral' f a = A := by pm_4441 tendsto_rectangleIntegral'_vertical_sub

noncomputable def heathBrownIntermediateLine (delta : ℝ) : ℝ :=
  (1 / 2 - delta) / 2

theorem heathBrown_intermediateLine_pos
    {delta : ℝ} (hdeltaUpper : delta ≤ 1 / 4) :
    0 < heathBrownIntermediateLine delta := by
  unfold heathBrownIntermediateLine
  linarith

theorem heathBrown_intermediateLine_le_quarter
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    heathBrownIntermediateLine delta ≤ 1 / 4 := by
  unfold heathBrownIntermediateLine
  linarith

section
variable {s : ℂ} {delta : ℝ} (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 4) (hsRe : s.re = 1 / 2 + delta)
include s delta hdelta hdeltaUpper hsRe
theorem heathBrown_movingPole_vertical_shift :
    VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) 2 -
        VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s)
          (heathBrownIntermediateLine delta) =
      heathBrownMovingPoleResidue s := by
  pm_4442
  have hpc : (heathBrownMovingPole s).re < 2 := by rw [hpRe]; linarith
  pm_6753
  pm_1340 hBottom tendsto_heathBrownMellin_HIntegral'_neg_zero
  pm_1340 hTop tendsto_heathBrownMellin_HIntegral'_zero
  pm_4443
  have hIntTwo : Integrable (fun u : ℝ =>
      f (((2 : ℝ) : ℂ) + (u : ℂ) * I)) := by
    apply integrable_heathBrownZetaSquareMellinIntegrand_right
    rw [hsRe]
    linarith
  have hFinite : ∀ᶠ R : ℝ in atTop,
      RectangleIntegral' f
        ((d : ℂ) - (R : ℂ) * I) (((2 : ℝ) : ℂ) + (R : ℂ) * I) =
          heathBrownMovingPoleResidue s := by
    filter_upwards [eventually_gt_atTop
      (max 0 |(heathBrownMovingPole s).im|)] with R hR
    apply heathBrown_movingPole_finite_rectangle hd hdp hpc
    pm_7443 le_max_left
    pm_7443 le_max_right
  simpa only [f, d] using verticalIntegral'_sub_eq_of_eventual_rectangle
    hBottom hTop hIntD hIntTwo hFinite

theorem heathBrown_gammaPole_vertical_shift :
    VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s)
        (heathBrownIntermediateLine delta) -
      VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) =
        riemannZeta s ^ 2 := by
  pm_4442
  pm_6753
  pm_971 hBottom tendsto_heathBrownMellin_HIntegral'_neg_zero
  pm_971 hTop tendsto_heathBrownMellin_HIntegral'_zero
  have hIntMinus : Integrable (fun u : ℝ =>
      f (((-delta : ℝ) : ℂ) + (u : ℂ) * I)) := by
    apply integrable_heathBrownZetaSquareMellinIntegrand_minus
      (s := s) hdelta hdeltaUpper
    · rw [hsRe]
      norm_num
    · rw [hsRe]
      linarith
  pm_4443
  have hFinite : ∀ᶠ R : ℝ in atTop,
      RectangleIntegral' f
        (((-delta : ℝ) : ℂ) - (R : ℂ) * I)
        ((d : ℂ) + (R : ℂ) * I) = riemannZeta s ^ 2 := by
    pm_414 eventually_gt_atTop R hR
    rw [show (((-delta : ℝ) : ℂ)) = (-delta : ℂ) by norm_num]
    exact heathBrown_gammaPole_finite_rectangle
      (s := s) hdelta (by linarith) hd hdp hR
  simpa only [f, d] using verticalIntegral'_sub_eq_of_eventual_rectangle
    hBottom hTop hIntMinus hIntD hFinite

/-- Exact completed form of the two residue shifts. -/
theorem heathBrown_twoPole_vertical_shift :
    VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) 2 -
      VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) =
        heathBrownMovingPoleResidue s + riemannZeta s ^ 2 := by
  have hMoving := heathBrown_movingPole_vertical_shift
    hdelta hdeltaUpper hsRe
  have hGamma := heathBrown_gammaPole_vertical_shift
    hdelta hdeltaUpper hsRe
  linear_combination hMoving + hGamma
end

theorem heathBrownSmoothedDivisorSeries_eq_rightVertical
    {s : ℂ} (hs : 0 < s.re) :
    heathBrownSmoothedDivisorSeries s =
      VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) 2 := by
  rw [heathBrown_smoothed_divisor_eq_right_mellin hs]
  unfold VerticalIntegral' VerticalIntegral heathBrownDivisorMellinIntegrand
  simp [heathBrownZetaSquareMellinIntegrand, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  simp only [mul_comm I]
  ring

/-- Heath--Brown's exact zeta-square identity before estimating the retained
critical-line contour and the two harmless terms. -/
theorem heathBrown_zetaSquare_eq_smoothed_sub_residue_sub_leftVertical
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4)
    (hsRe : s.re = 1 / 2 + delta) :
    riemannZeta s ^ 2 =
      heathBrownSmoothedDivisorSeries s - heathBrownMovingPoleResidue s -
        VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) := by
  have hShift := heathBrown_twoPole_vertical_shift
    hdelta hdeltaUpper hsRe
  have hRight := heathBrownSmoothedDivisorSeries_eq_rightVertical
    (s := s) (by rw [hsRe]; linarith)
  rw [← hRight] at hShift
  calc
    riemannZeta s ^ 2 =
        (heathBrownSmoothedDivisorSeries s -
          VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta)) -
            heathBrownMovingPoleResidue s := by
      rw [hShift]
      ring
    _ = heathBrownSmoothedDivisorSeries s - heathBrownMovingPoleResidue s -
        VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) := by
      ring

end MathCollab.Density.Stronger.PointMean
