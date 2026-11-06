module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsEstimates
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-! # Anisotropic cutoff scales

A position cutoff uses radius R³ and a velocity cutoff radius R. Their actual
first and second derivatives provide the R⁻³, R⁻¹ and R⁻² Green error scales.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic

/-- Rescale a scalar cutoff by its physical radius. -/
def scaledScalarCutoff (chi : ℝ → ℝ) (R : ℝ) : ℝ → ℝ := fun s => chi (s/R)

variable (chi : ℝ → ℝ)

/-- Scalar rescaling preserves C² regularity. -/
theorem scaledScalarCutoff_contDiff  (hchi : ContDiff ℝ 2 chi)
    (R : ℝ) : ContDiff ℝ 2 (scaledScalarCutoff chi R) :=
  hchi.comp (contDiff_id.div_const R)

/-- The first derivative has the exact inverse-radius factor. -/
theorem scaledScalarCutoff_deriv  (hchi : ContDiff ℝ 2 chi)
    (R s : ℝ) :
    deriv (scaledScalarCutoff chi R) s = deriv chi (s/R)/R := by
  have hc := (hchi.differentiable (by norm_num) (s/R)).hasDerivAt
  have hs := (hasDerivAt_id s).div_const R
  change deriv (chi ∘ (fun t => t/R)) s = _
  simpa only [id_eq, one_div, div_eq_mul_inv, one_mul] using (hc.comp s hs).deriv

/-- The second derivative has the exact inverse-square radius factor. -/
theorem scaledScalarCutoff_second_deriv  (hchi : ContDiff ℝ 2 chi)
    {R : ℝ} (hR : R ≠ 0) (s : ℝ) :
    deriv (deriv (scaledScalarCutoff chi R)) s = deriv (deriv chi) (s/R)/R^2 := by
  have he : deriv (scaledScalarCutoff chi R) = fun t => deriv chi (t/R)/R := by
    funext t
    exact scaledScalarCutoff_deriv chi hchi R t
  have hc := (hchi.differentiable_deriv_two (s/R)).hasDerivAt
  have hs := (hasDerivAt_id s).div_const R
  have hd : deriv (fun t => deriv chi (t/R)/R) s =
      (deriv (deriv chi) (s/R)*(1/R))/R := by
    simpa only [Function.comp_def, id_eq] using ((hc.comp s hs).div_const R).deriv
  grind

/-- Uniform first-derivative bounds acquire one inverse-radius factor. -/
theorem scaledScalarCutoff_deriv_bound  (hchi : ContDiff ℝ 2 chi)
    {R : ℝ} (hR : 0 < R) (C : ℝ) (hC : ∀ s, |deriv chi s| ≤ C) (s : ℝ) :
    |deriv (scaledScalarCutoff chi R) s| ≤ C/R := by
  rw [scaledScalarCutoff_deriv chi hchi, abs_div, abs_of_pos hR]
  exact div_le_div_of_nonneg_right (hC _) hR.le

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
