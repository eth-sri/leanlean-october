/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.RealSecondDifference
public import DOZZ.Hypergeom.Planar.TaylorParentScaling
public import DOZZ.Hypergeom.Planar.RieszNormalization
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A dominated discrete-Laplacian limit for the corrected Taylor parent integral. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ.Proofs

/-- The four-direction discrete Laplacian, divided by the squared step. -/
noncomputable def planarDiscreteLaplacian (F : ℂ → ℝ) (t : ℝ) (z : ℂ) : ℝ :=
  (F (z + (t : ℂ)) + F (z - (t : ℂ)) + F (z + (t : ℂ) * Complex.I) +
    F (z - (t : ℂ) * Complex.I) - 4 * F z) / t ^ 2

/-- Integration in the spatial variable commutes with the discrete Laplacian. -/
theorem integral_planarDiscreteLaplacian (F : ℂ → ℂ → ℝ) (hF : ∀ z, Integrable (F z))
    (t : ℝ) (z : ℂ) :
    (∫ u, planarDiscreteLaplacian (fun w => F w u) t z) =
      planarDiscreteLaplacian (fun w => ∫ u, F w u) t z := by
  let f₁ := F (z + (t : ℂ))
  let f₂ := F (z - (t : ℂ))
  let f₃ := F (z + (t : ℂ) * Complex.I)
  let f₄ := F (z - (t : ℂ) * Complex.I)
  have h₁ : Integrable f₁ := hF _
  have h₂ : Integrable f₂ := hF _
  have h₃ : Integrable f₃ := hF _
  have h₄ : Integrable f₄ := hF _
  change (∫ u, ((f₁ + f₂ + f₃ + f₄) u - 4 * F z u) / t ^ 2) = _
  rw [integral_div, integral_sub (((h₁.add h₂).add h₃).add h₄) ((hF z).const_mul 4)]
  have e₁ := integral_add ((h₁.add h₂).add h₃) h₄
  have e₂ := integral_add (h₁.add h₂) h₃
  simp only [Pi.add_apply] at e₁ e₂ ⊢
  rw [e₁, e₂, integral_add h₁ h₂, integral_const_mul]
  rfl

/-- The Taylor-subtracted kernel has the same discrete Laplacian as the original power. -/
noncomputable def planarTaylorDiscreteQuotient (k β : ℝ) (t : ℝ) (u : ℂ) : ℝ :=
  planarDiscreteLaplacian (fun z => DOZZ.planarTaylorRemainder k β z u) t 1

section
variable (k β : ℝ)

/-- Away from the fixed denominator singularity, the Taylor counterterms cancel from the
discrete Laplacian and leave the positive radial kernel. -/
theorem planarTaylorDiscreteQuotient_eq_kernel (t : ℝ) (u : ℂ) :
    planarTaylorDiscreteQuotient k β t u =
      ‖u‖ ^ (-β) * normPowerDiscreteLaplacian k t (u - 1) := by
  unfold planarTaylorDiscreteQuotient planarDiscreteLaplacian DOZZ.planarTaylorRemainder normPowerDiscreteLaplacian
  simp only [sub_add_eq_sub_sub, sub_sub_eq_add_sub, add_sub_right_comm u, add_div, sub_div,
    star_add, star_sub, Complex.add_re, Complex.sub_re, Real.rpow_neg (norm_nonneg u)]
  ring

/-- The pointwise limit of the corrected parent quotient is the positive Riesz kernel. -/
theorem planarTaylorDiscreteQuotient_tendsto (u : ℂ) (hu : u ≠ 1) :
    Tendsto (fun t : ℝ => planarTaylorDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
  simpa only [planarTaylorDiscreteQuotient_eq_kernel, mul_left_comm] using
    (norm_rpow_discrete_laplacian_tendsto k (u - 1) (sub_ne_zero.mpr hu)).const_mul (‖u‖ ^ (-β))

section
variable (hk : 0 < k) (hβ : k < β)
include hk hβ

/-- A uniform Riesz-kernel majorant for the discrete quotients, away from the null collision. -/
theorem planarTaylorDiscreteQuotient_norm_le (hk₂ : β < 2)
    (u : ℂ) (t : ℝ) (hu : u ≠ 1) (ht : t ≠ 0) :
    ‖planarTaylorDiscreteQuotient k β t u‖ ≤
      2 * radialCenteredConstant k * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)) := by
  have hw : 0 ≤ ‖u‖ ^ (-β) := by positivity
  rw [planarTaylorDiscreteQuotient_eq_kernel, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (norm_rpow_discrete_laplacian_le k hk (hβ.trans hk₂)
    (u - 1) t (sub_ne_zero.mpr hu) ht) hw

/-- Dominated convergence identifies the limiting integral of the Taylor discrete quotient with
the positive Riesz convolution multiplied by `k^2`. -/
theorem planarTaylorDiscreteQuotient_integral_tendsto (hβ₂ : β < 2) :
    Tendsto (fun t : ℝ => ∫ u : ℂ, planarTaylorDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ u : ℂ, k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
  refine tendsto_integral_of_riesz_majorant k β (2 * radialCenteredConstant k) hk hβ hβ₂ _ _
    (fun t => ?_) (fun t u ht hu => planarTaylorDiscreteQuotient_norm_le k β hk hβ hβ₂ u t hu ht)
    (planarTaylorDiscreteQuotient_tendsto k β)
  change Measurable (fun u => planarTaylorDiscreteQuotient k β t u)
  simp_rw [planarTaylorDiscreteQuotient_eq_kernel, normPowerDiscreteLaplacian]
  fun_prop

end

end

end DOZZ.Proofs
