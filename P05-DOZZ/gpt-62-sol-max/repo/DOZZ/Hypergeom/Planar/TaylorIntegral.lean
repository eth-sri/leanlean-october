/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarTaylorRemainder
public import DOZZ.Statements.Hypergeom.PlanarGaussConstant
public import DOZZ.Hypergeom.Planar.TaylorDiscreteLaplacian
public import DOZZ.Hypergeom.Planar.TaylorNormalization
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The positive Riesz convolution and scaling determine the corrected Taylor integral. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- A homogeneous parent with the given Riesz Laplacian has the Gauss coefficient. -/
theorem planarGaussConstant_of_discreteLaplacian (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (F : ℂ → ℝ)
    (hscale : ∀ z, F z = ‖z‖ ^ (2 + k - β) * F 1)
    (hlim : Tendsto (fun t => planarDiscreteLaplacian F t 1) (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ u : ℂ, k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))))) :
    (F 1 : ℂ) = DOZZ.planarGaussConstant k β := by
  let α : ℝ := 2 + k - β
  have hα : 0 < α := by dsimp [α]; linarith
  have he (t : ℝ) : planarDiscreteLaplacian F t 1 =
      F 1 * normPowerDiscreteLaplacian α t 1 := by
    unfold planarDiscreteLaplacian normPowerDiscreteLaplacian
    rw [hscale (1 + (t : ℂ)), hscale (1 - (t : ℂ)),
      hscale (1 + (t : ℂ) * Complex.I), hscale (1 - (t : ℂ) * Complex.I)]
    simp only [α, norm_one, Real.one_rpow]
    ring
  have hDL : Tendsto (fun t => planarDiscreteLaplacian F t 1) (𝓝[≠] (0 : ℝ))
      (𝓝 (F 1 * α ^ 2)) := by
    simp_rw [he]
    simpa using (norm_rpow_discrete_laplacian_tendsto α 1 (by norm_num)).const_mul (F 1)
  have hc := tendsto_nhds_unique hlim hDL
  rw [integral_const_mul] at hc
  have hRiesz := positive_riesz_convolution_integral k β hk hβ hβ₂ 1 (by norm_num)
  simp only [norm_one, Real.one_rpow, mul_one] at hRiesz
  rw [hRiesz] at hc
  have hA : F 1 = (k / 2) ^ 2 / (α / 2) ^ 2 * planarRieszConstant k β := by
    field_simp [hα.ne']
    linear_combination -hc
  rw [hA]
  exact positive_riesz_coefficient_eq_planarGaussConstant k β hk hβ hβ₂

/-- The coefficient of the corrected Taylor parent, recovered from its dominated discrete
Laplacian. -/
theorem planarTaylor_constant_from_discrete_laplacian (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) :
    ((∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u : ℝ) : ℂ) =
      DOZZ.planarGaussConstant k β := by
  apply planarGaussConstant_of_discreteLaplacian k β hk hβ hβ₂
    (fun z => ∫ u, DOZZ.planarTaylorRemainder k β z u)
    (planarTaylorRemainder_integral_scale_norm k β hk hβ hβ₂)
  have h (t : ℝ) := integral_planarDiscreteLaplacian (DOZZ.planarTaylorRemainder k β)
    (integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin) t 1
  simp_rw [← h]
  exact planarTaylorDiscreteQuotient_integral_tendsto k β hk hβ hβ₂

/-- Proof of the corrected Taylor integral statement `DOZZ.planar_taylor_integral`. -/
theorem planar_taylor_integral (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) :
    ∀ z : ℂ, Integrable (DOZZ.planarTaylorRemainder k β z) volume ∧
      ((∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u) : ℂ) =
        (‖z‖ ^ (2 + k - β) : ℝ) * DOZZ.planarGaussConstant k β := by
  have hInt := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin
  have hA := planarTaylor_constant_from_discrete_laplacian k β hk hβ hβ₂ hβlin
  have hscale := planarTaylorRemainder_integral_scale_norm k β hk hβ hβ₂
  intro z
  refine ⟨hInt z, ?_⟩
  rw [integral_complex_ofReal, hscale z, Complex.ofReal_mul, hA]

end DOZZ.Proofs
