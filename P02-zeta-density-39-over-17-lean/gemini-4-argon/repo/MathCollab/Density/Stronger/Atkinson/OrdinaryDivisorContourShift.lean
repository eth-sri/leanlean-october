module
/-
Native modulus-one adaptation of selected McColm divisor Voronoi residues,
source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright (c) 2026 S. McColm. See repository-root third_party/twelfth/LICENSE-MIT-0.
Mathlib ZetaAsymp and existing rectangle sources retain Apache-2.0 attribution.
No periodic Estermann or upstream project is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiContourBounds
public import MathCollab.Density.Stronger.Atkinson.OrdinaryDivisorMellin
public import MathCollab.Density.Stronger.Atkinson.VoronoiMinusTransport

@[expose] public section

open Complex Set MeasureTheory Filter Topology MathCollab.Density.Contour MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- Actual q=1 contour shift, with both vertical integrals and both edges proved. -/
theorem DFIVoronoiTestFunction.ordinaryDivisor_vertical_shift
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    VerticalIntegral' (ordinaryDivisorMellinIntegrand g) (3/2) -
      VerticalIntegral' (ordinaryDivisorMellinIntegrand g) (-1/2) =
        ordinaryDivisorVoronoiMain g := by
  obtain ⟨htop,hbottom⟩ := hg.ordinaryDivisor_horizontal_limits
  apply verticalIntegral'_sub_eq_of_eventual_rectangle hbottom htop
    (hg.integrable_ordinaryDivisorMellin_vertical (by norm_num) (by norm_num) (by norm_num))
    (hg.integrable_ordinaryDivisorMellin_vertical (by norm_num) (by norm_num) (by norm_num))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  apply hg.ordinaryDivisor_finiteRectangle
  · norm_num
  · simpa using (show -R ≤ R by linarith)
  · rw [rectangle_mem_nhds_iff]
    norm_num only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im,
      mul_re, mul_im, I_re, I_im, mul_zero, zero_mul, sub_zero, zero_sub,
      add_zero, zero_add, mul_one, one_re, one_im]
    rw [Set.uIoo_of_lt (by norm_num : -(1/2 : ℝ) < 3/2),
      Set.uIoo_of_lt (by linarith : -R < R)]
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by simpa using neg_lt_zero.mpr hR, by simpa using hR⟩⟩

/-- Exact native ordinary-divisor Mellin-Barnes formula before the functional equation. -/
theorem DFIVoronoiTestFunction.ordinaryDivisorSum_eq_main_add_left
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    (∑' n : ℕ, divisorWeight n * g n) = ordinaryDivisorVoronoiMain g +
      VerticalIntegral' (ordinaryDivisorMellinIntegrand g) (-1/2) := by
  have hr : (∑' n : ℕ, divisorWeight n * g n) =
      VerticalIntegral' (ordinaryDivisorMellinIntegrand g) (3/2) := by
    rw [verticalIntegral'_eq_realIntegral]
    exact hg.ordinaryDivisorSum_eq_zetaSquareMellinIntegral (by norm_num)
  rw [hr]
  linear_combination hg.ordinaryDivisor_vertical_shift

/-- Exact native FE split, retaining both original Mellin multipliers. -/
theorem DFIVoronoiTestFunction.ordinaryDivisorSum_eq_main_add_reflected
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    (∑' n : ℕ, divisorWeight n * g n) = ordinaryDivisorVoronoiMain g +
      VerticalIntegral' (fun z : ℂ =>
        (dfiVoronoiMinusMultiplier 1 z + dfiVoronoiPlusMultiplier 1 z) *
          riemannZeta (1-z)^2 * mellin g z) (-1/2) := by
  rw [hg.ordinaryDivisorSum_eq_main_add_left]
  congr 1
  rw [verticalIntegral'_eq_realIntegral, verticalIntegral'_eq_realIntegral]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  unfold ordinaryDivisorMellinIntegrand
  rw [riemannZeta_sq_eq_voronoiMultipliers (by norm_num)
    (by intro h; have := congrArg Complex.re h; norm_num at this)]

