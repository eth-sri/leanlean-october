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

variable (chi : ℝ → ℝ)

/-- Rescale a scalar cutoff by its physical radius. -/
def scaledScalarCutoff  (R : ℝ) : ℝ → ℝ := fun s => chi (s/R)

variable (hchi : ContDiff ℝ 2 chi)

include hchi in
/-- Scalar rescaling preserves C² regularity. -/
theorem scaledScalarCutoff_contDiff
    (R : ℝ) : ContDiff ℝ 2 (scaledScalarCutoff chi R) :=
  hchi.comp (contDiff_id.div_const R)

include hchi in
/-- The first derivative has the exact inverse-radius factor. -/
theorem scaledScalarCutoff_deriv
    (R s : ℝ) :
    deriv (scaledScalarCutoff chi R) s = deriv chi (s/R)/R := by


  change deriv (chi ∘ (fun t => t/R)) s = _
  simpa only [div_eq_mul_inv, id_eq, one_mul] using (((hchi.differentiable (by norm_num) (s/R)).hasDerivAt).comp s ((hasDerivAt_id s).div_const R)).deriv

variable {R : ℝ}

include hchi
/-- The second derivative has the exact inverse-square radius factor. -/
theorem scaledScalarCutoff_second_deriv
     (hR : R ≠ 0) (s : ℝ) :
    deriv (deriv (scaledScalarCutoff chi R)) s = deriv (deriv chi) (s/R)/R^2 := by
  let sharedTerm_959b16fbea := ((fun t => deriv chi (t / R) / R))
  have he : deriv (scaledScalarCutoff chi R) = sharedTerm_959b16fbea := by
    funext t
    exact scaledScalarCutoff_deriv chi hchi R t
  rw [he]


  have hd : deriv sharedTerm_959b16fbea s =
      (deriv (deriv chi) (s/R)*(1/R))/R := by
    simpa only [Function.comp_def, id_eq] using ((((hchi.differentiable_deriv_two (s/R)).hasDerivAt).comp s ((hasDerivAt_id s).div_const R)).div_const R).deriv
  rw [hd]
  field_simp

/-- Uniform first-derivative bounds acquire one inverse-radius factor. -/
theorem scaledScalarCutoff_deriv_bound
     (hR : 0 < R) (C : ℝ) (hC : ∀ s, |deriv chi s| ≤ C) (s : ℝ) :
    |deriv (scaledScalarCutoff chi R) s| ≤ C/R := by
  rw [scaledScalarCutoff_deriv chi hchi, abs_div, abs_of_pos hR]
  exact div_le_div_of_nonneg_right (hC _) hR.le

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
