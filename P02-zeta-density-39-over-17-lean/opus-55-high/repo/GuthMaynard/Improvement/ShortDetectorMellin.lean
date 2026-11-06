module
/-
Right-contour extension reusing the audited DetectorMellin proof, whose termwise
Mellin argument is adapted from McColm TypeIICoverage, commit
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be, MIT. Original sources unchanged.
-/
public import MathCollab.Density.DetectorMellin
import WeylPort.Analytic.RealLaplace

@[expose] public section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped ArithmeticFunction.Moebius Topology
noncomputable section
namespace GuthMaynard.Improvement

def short_detectorPSeries : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ (-(9 / 8 : ℝ))

theorem short_summable_detectorPSeries :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(9 / 8 : ℝ))) := by
  exact Real.summable_nat_rpow.mpr (by norm_num)

theorem short_norm_mollifier_LSeries_le_cutoff_pSeries {z : ℂ} {X : ℝ}
    (hz : 9 / 8 ≤ z.re) :
    ‖LSeries (mollifierDirichletCoeff X) z‖ ≤
      (⌊X⌋₊ : ℝ) * short_detectorPSeries := by
  pm_4308
  have hTerm (n : ℕ) : ‖LSeries.term f z n‖ ≤
      (⌊X⌋₊ : ℝ) * (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
    pm_4961
    · have hnPos : (0 : ℝ) < n := by positivity
      have hnOne : (1 : ℝ) ≤ n := by aesop
      have hDen : (n : ℝ) ^ (9 / 8 : ℝ) ≤ (n : ℝ) ^ z.re :=
        Real.rpow_le_rpow_of_exponent_le hnOne hz
      pm_4307
      have hRight : (⌊X⌋₊ : ℝ) / (n : ℝ) ^ z.re ≤
          (⌊X⌋₊ : ℝ) / (n : ℝ) ^ (9 / 8 : ℝ) := by
        pm_7850
      grind
  calc
    ‖LSeries f z‖ ≤ ∑' n : ℕ, ‖LSeries.term f z n‖ :=
      norm_tsum_le_tsum_norm hNorm
    _ ≤ ∑' n : ℕ, (⌊X⌋₊ : ℝ) *
        (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
      pm_8291 short_summable_detectorPSeries.mul_left
    _ = (⌊X⌋₊ : ℝ) * short_detectorPSeries := by
      rw [short_detectorPSeries, tsum_mul_left]

set_option maxHeartbeats 800000 in
/-- The Mellin transform of the smoothed detector is genuinely integrable on
the right line `Re s = 1/2`, uniformly for the zero-density range `Re ρ ≥ 9/13`. -/
theorem short_verticalIntegrable_mellin_smoothedDetector {ρ : ℂ} {X : ℝ}
    (hρ : 9 / 13 ≤ ρ.re) :
    VerticalIntegrable (mellin (smoothedDetector ρ X)) (1 / 2 : ℝ) := by pf_33 short_detectorPSeries 9 8 short_norm_mollifier_LSeries_le_cutoff_pSeries

section
variable {ρ : ℂ}
include ρ
set_option maxHeartbeats 800000 in
/-- Absolute convergence in the Mellin variable on `Re s = 1/2`.  The key
summability exponent is `Re ρ + 1/2 > 1`; this is exactly why the detector
works uniformly in the repaired zero-density range `Re ρ ≥ 9/13`. -/
theorem short_mellinConvergent_smoothedDetector {X : ℝ}
    (hρ : 9 / 13 ≤ ρ.re) :
    MellinConvergent (smoothedDetector ρ X) ((1 / 2 : ℝ) : ℂ) := by pm_4309

/-- Exact inversion for an arbitrary positive smoothing variable. -/
theorem short_smoothedDetector_eq_mellinInv {X x : ℝ}
    (hx : 0 < x) (hρ : 9/13 ≤ ρ.re) :
    smoothedDetector ρ X x = mellinInv (1/2 : ℝ)
      (fun s => Complex.Gamma s * LSeries (mollifierDirichletCoeff X) (ρ+s)) x := by pm_4310 short_mellinConvergent_smoothedDetector short_verticalIntegrable_mellin_smoothedDetector

theorem short_smoothedDetector_eq_rightContour {X Y : ℝ}
    (hY : 0 < Y) (hρ : 9/13 ≤ ρ.re) :
    smoothedDetector ρ X (1/Y) =
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ u : ℝ,
        detectorKernel ρ X Y (((1/2 : ℝ) : ℂ)+(u : ℂ)*I)) := by pm_4311 short_smoothedDetector_eq_mellinInv
end

end GuthMaynard.Improvement
