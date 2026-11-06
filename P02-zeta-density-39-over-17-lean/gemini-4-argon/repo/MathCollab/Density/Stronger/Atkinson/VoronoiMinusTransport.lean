module
/-
Canonical minus contour transport for the literal DFI Bessel multiplier.
Target and selected rectangle-limit proof pattern: Scott McColm,
DFIEquation29.lean and PointMeanMellinShift.lean, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, copyright 2026, MIT-0.
The existing PNT+ rectangle infrastructure retains Apache-2.0 attribution.
The final physical identity has no convergence or contour-identity premise.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiMinusConvergence
public import MathCollab.Density.Stronger.Atkinson.BesselTransformBridge

@[expose] public section

open Complex Set MeasureTheory Filter Topology MathCollab.Density.Contour MathCollab.Density.Stronger.PointMean
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem DFIVoronoiTestFunction.minusIntegrand_finite_rectangle (q : ℕ) [NeZero q]
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {n : ℕ} (hn : 0<n)
    (H : ℝ) :
    RectangleIntegral' (dfiVoronoiMinusIntegrand q g n)
      ((-(1/2) : ℂ)-(H:ℂ)*I) ((13/16 : ℂ)+(H:ℂ)*I) = 0 := by
  have hh : HolomorphicOn (dfiVoronoiMinusIntegrand q g n) {z : ℂ | z.re < 1} := by
    intro z hz
    exact (differentiableAt_dfiVoronoiMinusIntegrand q hg hn hz).differentiableWithinAt
  have hr := hh.vanishesOnRectangle (z := (-(1/2) : ℂ)-(H:ℂ)*I)
    (w := (13/16 : ℂ)+(H:ℂ)*I) (by
      intro z hz
      have hzre := hz.1
      change z.re ∈ Set.uIcc _ _ at hzre
      norm_num at hzre
      change z.re < 1
      linarith [hzre.2])
  simp only [RectangleIntegral', hr, smul_zero]

theorem DFIVoronoiTestFunction.minusTransform_eq_thirteenSixteenths
    (q : ℕ) [NeZero q] {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {n : ℕ} (hn : 0<n) :
    dfiVoronoiMinusTransform q (mellin g) n =
      PointMean.VerticalIntegral' (dfiVoronoiMinusIntegrand q g n) (13/16) := by
  obtain ⟨htop,hbottom⟩ := hg.minusIntegrand_horizontal_limits q hn
  have ha := hg.integrable_minusIntegrand_vertical q hn
    (σ := -(1/2 : ℝ)) (by norm_num) (by norm_num)
  have hb := hg.integrable_minusIntegrand_vertical q hn
    (σ := (13/16 : ℝ)) (by norm_num) (by norm_num)
  have h := verticalIntegral'_sub_eq_of_eventual_rectangle hbottom htop ha hb
    (A := 0) (Eventually.of_forall fun H => by
      simpa using hg.minusIntegrand_finite_rectangle q hn H)
  exact (sub_eq_zero.mp h).symm

/-- Canonical Mellin--Barnes minus transform equals the literal Schläfli Y₀
transform. All line integrability and horizontal decay are discharged. -/
theorem dfiVoronoiMinusTransform_mellin_eq_bessel (q n : ℕ) [NeZero q]
    (hn : 0<n) {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    dfiVoronoiMinusTransform q (mellin g) n = dfiVoronoiMinusBesselTransform q g n := by
  rw [hg.minusTransform_eq_thirteenSixteenths q hn]
  exact verticalIntegral_dfiVoronoiMinus_mellin_thirteenSixteenths_eq_bessel q n hn hg

