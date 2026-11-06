/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.DifferenceScale
public import DOZZ.Hypergeom.Planar.TaylorDiscreteLaplacian
public import DOZZ.Hypergeom.Planar.RieszConvolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A dominated discrete-Laplacian limit for the difference parent integral. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- The four-direction discrete Laplacian of the first-order-subtracted difference kernel. -/
noncomputable def planarDifferenceDiscreteQuotient (k β : ℝ) (t : ℝ) (u : ℂ) : ℝ :=
  (DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u +
    DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u +
    DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u +
    DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u -
    4 * DOZZ.planarDifferenceKernel k β 1 u) / t ^ 2



/-- Integrating the difference quotient gives the corresponding quotient of parent integrals. -/
theorem integral_planarDifferenceDiscreteQuotient k β (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβtail : k + 1 < β) (t : ℝ) :
    (∫ u : ℂ, planarDifferenceDiscreteQuotient k β t u) =
      ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u) +
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u) -
        4 * (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u)) / t ^ 2 := by
  let f₁ := DOZZ.planarDifferenceKernel k β (1 + (t : ℂ))
  let f₂ := DOZZ.planarDifferenceKernel k β (1 - (t : ℂ))
  let f₃ := DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I)
  let f₄ := DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I)
  let f₀ := DOZZ.planarDifferenceKernel k β 1
  have hf₁ : Integrable f₁ volume := by simpa [f₁] using (integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail (1 + (t : ℂ)))
  have hf₂ : Integrable f₂ volume := by simpa [f₂] using (integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail (1 - (t : ℂ)))
  have hf₃ : Integrable f₃ volume := by simpa [f₃] using (integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail (1 + (t : ℂ) * Complex.I))
  have hf₄ : Integrable f₄ volume := by simpa [f₄] using (integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail (1 - (t : ℝ) * Complex.I))
  let N : ℂ → ℝ := fun u => f₁ u + f₂ u + f₃ u + f₄ u - 4 * f₀ u
  have hsum : (∫ u : ℂ, N u) =
      (∫ u : ℂ, f₁ u) + (∫ u : ℂ, f₂ u) + (∫ u : ℂ, f₃ u) +
        (∫ u : ℂ, f₄ u) - 4 * (∫ u : ℂ, f₀ u) := by
    have h₁₂₃ : (∫ u : ℂ, (f₁ u + f₂ u) + f₃ u) =
        ((∫ u : ℂ, f₁ u) + (∫ u : ℂ, f₂ u)) + (∫ u : ℂ, f₃ u) := by
      calc
        _ = (∫ u : ℂ, f₁ u + f₂ u) + (∫ u : ℂ, f₃ u) := by
          simpa only [Pi.add_apply] using integral_add (hf₁.add hf₂) hf₃
        _ = _ := by rw [(integral_add hf₁ hf₂)]
    have h₁₂₃₄ : (∫ u : ℂ, ((f₁ u + f₂ u) + f₃ u) + f₄ u) =
        (((∫ u : ℂ, f₁ u) + (∫ u : ℂ, f₂ u)) + (∫ u : ℂ, f₃ u)) +
          (∫ u : ℂ, f₄ u) := by
      calc
        _ = (∫ u : ℂ, (f₁ u + f₂ u) + f₃ u) + (∫ u : ℂ, f₄ u) := by
          simpa only [Pi.add_apply] using integral_add ((hf₁.add hf₂).add hf₃) hf₄
        _ = _ := by rw [h₁₂₃]
    calc
      (∫ u : ℂ, N u) =
          (∫ u : ℂ, ((f₁ u + f₂ u) + f₃ u) + f₄ u - 4 * f₀ u) := by
            apply congrArg (fun f : ℂ → ℝ => ∫ u : ℂ, f u)
            funext u
            dsimp [N]
      _ = (∫ u : ℂ, ((f₁ u + f₂ u) + f₃ u) + f₄ u) -
          (∫ u : ℂ, 4 * f₀ u) := integral_sub
            (((hf₁.add hf₂).add hf₃).add hf₄) ((show Integrable f₀ volume by simpa [f₀] using (integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail 1)).const_mul 4)
      _ = _ := by rw [h₁₂₃₄, integral_const_mul]
  rw [(show (fun u => planarDifferenceDiscreteQuotient k β t u) = fun u => (t ^ 2)⁻¹ * N u by funext u; simp [planarDifferenceDiscreteQuotient, N, f₁, f₂, f₃, f₄, f₀, div_eq_mul_inv, mul_comm]), integral_const_mul, hsum]
  simp only [div_eq_mul_inv]
  ring




/-- Dominated convergence identifies the limiting integral with the positive Riesz convolution. -/
theorem planarDifferenceDiscreteQuotient_integral_tendsto (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβtail : k + 1 < β) :
    Tendsto (fun t : ℝ => ∫ u : ℂ, planarDifferenceDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ u : ℂ, k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
  have planarDifferenceDiscreteQuotient_eq_taylor t (ht : t ≠ 0) u : planarDifferenceDiscreteQuotient k β t u = planarTaylorDiscreteQuotient k β t u := by
    have planarDifferenceDiscreteQuotient_eq_kernel u : planarDifferenceDiscreteQuotient k β t u = ‖u‖ ^ (-β) * normPowerDiscreteLaplacian k t (u - 1) := by
      rw [planarDifferenceDiscreteQuotient, (show DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u + DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u + DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u + DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u - 4 * DOZZ.planarDifferenceKernel k β 1 u = (‖u - (1 + (t : ℂ))‖ ^ k + ‖u - (1 - (t : ℂ))‖ ^ k + ‖u - (1 + (t : ℂ) * Complex.I)‖ ^ k + ‖u - (1 - (t : ℝ) * Complex.I)‖ ^ k - 4 * ‖u - 1‖ ^ k) / ‖u‖ ^ β by simp only [DOZZ.planarDifferenceKernel]; ring), (show u - (1 + (t : ℂ)) = (u - 1) - (t : ℂ) by ring), (show u - (1 - (t : ℂ)) = (u - 1) + (t : ℂ) by ring), (show u - (1 + (t : ℂ) * Complex.I) = (u - 1) - (t : ℂ) * Complex.I by ring), (show u - (1 - (t : ℝ) * Complex.I) = (u - 1) + (t : ℝ) * Complex.I by ring), Real.rpow_neg (norm_nonneg u)]
      simp only [normPowerDiscreteLaplacian]
      field_simp [show t ^ 2 ≠ 0 by exact pow_ne_zero 2 ht]
      ring
    rw [planarDifferenceDiscreteQuotient_eq_kernel,
      planarTaylorDiscreteQuotient_eq_kernel]
  have planarDifferenceDiscreteQuotient_tendsto u (hu : u ≠ 1) := (planarTaylorDiscreteQuotient_tendsto k β u hu).congr' (show (fun t : ℝ => planarDifferenceDiscreteQuotient k β t u) =ᶠ[𝓝[≠] (0 : ℝ)] fun t => planarTaylorDiscreteQuotient k β t u by filter_upwards [(show ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), t ≠ 0 by filter_upwards [self_mem_nhdsWithin] with t ht; simpa using ht)] with t ht; exact planarDifferenceDiscreteQuotient_eq_taylor t ht u).symm
  have integrable_planarDifferenceDiscreteQuotient t : Integrable (planarDifferenceDiscreteQuotient k β t) volume := by
    change Integrable (fun u : ℂ =>
      (DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u +
        DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u +
        DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u +
        DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u -
        4 * DOZZ.planarDifferenceKernel k β 1 u) / t ^ 2)
    simpa [div_eq_mul_inv, mul_comm] using ((show Integrable (fun u => DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u + DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u + DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u + DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u - 4 * DOZZ.planarDifferenceKernel k β 1 u) volume by exact ((((integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail (1 + (t : ℂ))).add (integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail (1 - (t : ℂ)))).add (integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail (1 + (t : ℂ) * Complex.I))).add (integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail (1 - (t : ℝ) * Complex.I))).sub ((integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail 1).const_mul 4))).const_mul ((t ^ 2)⁻¹)
  let K := 2 * (2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
    (1 / 4 : ℝ) ^ (k / 2 - 2)))) + 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
  let bound : ℂ → ℝ := fun u => K * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ∀ᵐ u ∂volume, ‖planarDifferenceDiscreteQuotient k β t u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
    rw [planarDifferenceDiscreteQuotient_eq_taylor t ht0 u]
    simpa [bound, K] using
      planarTaylorDiscreteQuotient_norm_le k β hk hβ hβ₂ u t hu ht0
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
    (by filter_upwards [] with t; exact (integrable_planarDifferenceDiscreteQuotient t).aestronglyMeasurable) hbound (by simpa [bound, K, mul_assoc] using (positive_riesz_convolution_integrable k β hk hβ hβ₂ 1 (by norm_num)).const_mul K) (by filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu; exact planarDifferenceDiscreteQuotient_tendsto u hu)

end DOZZ.Proofs
