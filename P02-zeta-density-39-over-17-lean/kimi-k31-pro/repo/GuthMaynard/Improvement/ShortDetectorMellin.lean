module
public import MathCollab.Density.DetectorMellin

@[expose] public section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped ArithmeticFunction.Moebius BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

def short_detectorPSeries : ℝ := detectorPSeries

theorem short_summable_detectorPSeries :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(9 / 8 : ℝ))) :=
  summable_detectorPSeries

theorem short_norm_mollifier_LSeries_le_cutoff_pSeries {z : ℂ} {X : ℝ}
    (hz : 9 / 8 ≤ z.re) :
    ‖LSeries (mollifierDirichletCoeff X) z‖ ≤
      (⌊X⌋₊ : ℝ) * short_detectorPSeries :=
  norm_mollifier_LSeries_le_cutoff_pSeries hz

theorem short_verticalIntegrable_mellin_smoothedDetector {ρ : ℂ} {X : ℝ}
    (hρ : 9 / 13 ≤ ρ.re) :
    VerticalIntegrable (mellin (smoothedDetector ρ X)) (1 / 2 : ℝ) :=
  verticalIntegrable_mellin_smoothedDetector hρ

theorem short_mellinConvergent_smoothedDetector {ρ : ℂ} {X : ℝ}
    (hρ : 9 / 13 ≤ ρ.re) :
    MellinConvergent (smoothedDetector ρ X) ((1 / 2 : ℝ) : ℂ) :=
  mellinConvergent_smoothedDetector hρ

theorem short_smoothedDetector_eq_mellinInv {ρ : ℂ} {X x : ℝ}
    (hx : 0 < x) (hρ : 9/13 ≤ ρ.re) :
    smoothedDetector ρ X x = mellinInv (1/2 : ℝ)
      (fun s => Complex.Gamma s * LSeries (mollifierDirichletCoeff X) (ρ+s)) x :=
  smoothedDetector_eq_mellinInv hx hρ

theorem short_smoothedDetector_eq_rightContour {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hρ : 9/13 ≤ ρ.re) :
    smoothedDetector ρ X (1/Y) =
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ u : ℝ,
        detectorKernel ρ X Y (((1/2 : ℝ) : ℂ)+(u : ℂ)*I)) :=
  smoothedDetector_eq_rightContour hY hρ

end GuthMaynard.Improvement
