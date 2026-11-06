module
public import GuthMaynard.Improvement.Smoothing

@[expose] public section

/-! Exact restricted-mass and L2 bounds for every positive smoothing width.
Smoothness/Fourier decay and the published affine theorem are not asserted.
-/
noncomputable section
open MeasureTheory

namespace GuthMaynard.Improvement

def scaledKernel (φ : ℝ → ℝ) (δ x : ℝ) : ℝ := δ⁻¹ * φ (x / δ)

section
variable {φ : ℝ → ℝ}
include φ

theorem scaledKernel_measurable  (hφ : Measurable φ) (δ : ℝ) :
    Measurable (scaledKernel φ δ) :=
  measurable_const.mul (hφ.comp (measurable_id.div_const δ))

theorem scaledKernel_integrable  {δ : ℝ} (hφ : Integrable φ) (hδ : 0 < δ) :
    Integrable (scaledKernel φ δ) := (hφ.comp_div hδ.ne').const_mul δ⁻¹

theorem scaledKernel_nonneg  {δ : ℝ}
    (hφ : ∀ x, 0 ≤ φ x) (hδ : 0 < δ) (x : ℝ) : 0 ≤ scaledKernel φ δ x :=
  mul_nonneg (inv_nonneg.mpr hδ.le) (hφ _)

theorem scaledKernel_mass  {δ : ℝ} (hδ : 0 < δ)
    (hmass : ∫ x, φ x = 1) : (∫ x, scaledKernel φ δ x) = 1 := by
  simp only [scaledKernel, integral_const_mul, Measure.integral_comp_div,
    abs_of_pos hδ, smul_eq_mul, hmass, mul_one, inv_mul_cancel₀ hδ.ne']

theorem scaledKernel_bound  {δ B : ℝ}
    (hδ : 0 < δ) (hB : ∀ x, ‖φ x‖ ≤ B) (x : ℝ) :
    ‖scaledKernel φ δ x‖ ≤ δ⁻¹ * B := by
  simp only [scaledKernel, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
  exact mul_le_mul_of_nonneg_left (hB (x / δ)) (inv_nonneg.mpr hδ.le)
end



