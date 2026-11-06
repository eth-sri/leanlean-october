module
public import Mathlib

@[expose] public section

/-! Exact Fourier/Poisson identities for the unequal-scale reduction.
Quantitative tails and divisor-counting estimates are separate obligations.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped FourierTransform

namespace GuthMaynard.Improvement

def phase (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem fourier_eq_phase_integral (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ x, phase (-ξ * x) * f x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show -2 * Real.pi * x * ξ = 2 * Real.pi * (-ξ * x) by ring]
  rfl

def scaledModulated (ψ : ℝ → ℂ) (R α : ℝ) (x : ℝ) : ℂ :=
  ψ (x / R) * phase (α * x)

/-- Exact scale and modulation calculation; no asymptotic loss. -/
theorem fourier_scaledModulated (ψ : ℝ → ℂ) {R : ℝ} (hR : 0 < R) (α ξ : ℝ) :
    𝓕 (scaledModulated ψ R α) ξ = R • 𝓕 ψ (R * (ξ - α)) := by
  rw [fourier_eq_phase_integral, fourier_eq_phase_integral]
  have hid : (fun x => phase (-ξ * x) * scaledModulated ψ R α x) =
      (fun x => phase (-(R * (ξ - α)) * (x / R)) * ψ (x / R)) := by
    funext x
    dsimp only [scaledModulated]
    calc
      phase (-ξ * x) * (ψ (x / R) * phase (α * x)) =
          (phase (-ξ * x) * phase (α * x)) * ψ (x / R) := by ring
      _ = phase (-ξ * x + α * x) * ψ (x / R) := by rw [phase_add]
      _ = phase (-(R * (ξ - α)) * (x / R)) * ψ (x / R) := by
        congr 2
        field_simp
        ring
  rw [hid]
  simpa only [abs_of_pos hR] using
    Measure.integral_comp_div (fun x => phase (-(R * (ξ - α)) * x) * ψ x) R

/-- Fourier phase multiplication preserves integrability. -/
theorem integrable_phase_mul {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x => phase (-ξ * x) * f x) := by
  apply hf.bdd_mul (c := 1)
  · have hc : Continuous (fun x : ℝ => phase (-ξ * x)) := by
      dsimp [phase]
      fun_prop
    exact hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      simp only [phase, Complex.norm_exp_ofReal_mul_I, le_refl])

theorem fourier_constant_mul (f : ℝ → ℂ) (c : ℂ) (ξ : ℝ) :
    𝓕 (fun x => c * f x) ξ = c * 𝓕 f ξ := by
  simp only [fourier_eq_phase_integral, mul_left_comm (phase (-ξ * _)) c]
  exact integral_const_mul _ _

