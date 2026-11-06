module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierGrowth
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsPhysicalGreen

/-! # The actual rectangular cutoff generator errors, without coefficient derivatives -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory

/- Literal position, second velocity and cross velocity errors of the rectangular cutoff. -/
def barrierRectError (a : ℝ → ℝ → ℝ) (f : Z → ℝ) (Y R : ℝ) (z : Z) : ℝ :=
  z.2 * (deriv barrierCutoff ((z.1 - Y) / R ^ 3) / R ^ 3) *
    barrierCutoff (z.2 / R) * f z +
  a z.1 z.2 * barrierCutoff ((z.1 - Y) / R ^ 3) *
    (deriv (deriv barrierCutoff) (z.2 / R) / R ^ 2) * f z +
  2 * a z.1 z.2 * barrierCutoff ((z.1 - Y) / R ^ 3) *
    (deriv barrierCutoff (z.2 / R) / R) * deriv (fun v => f (z.1, v)) z.2

/- Centering the position cutoff changes no derivative scale. -/
theorem barrier_position_cutoff_deriv (Y R x : ℝ) :
    deriv (fun X => barrierCutoff ((X - Y) / R ^ 3)) x =
      deriv barrierCutoff ((x - Y) / R ^ 3) / R ^ 3 := by
  have hc := (barrierCutoff_contDiff.differentiable (by simp) ((x - Y) / R ^ 3)).hasDerivAt
  simpa only [one_div, div_eq_mul_inv, Function.comp_def, id_eq, one_mul] using (hc.comp x (((hasDerivAt_id x).sub_const Y).div_const (R ^ 3))).deriv

/- The literal error is exactly the generator product rule for a joint C² physical test. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
