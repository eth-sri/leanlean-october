/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.TaylorFiniteDifference
public import DOZZ.Hypergeom.Planar.TaylorParentScaling
public import DOZZ.Hypergeom.Planar.RieszNormalization
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A dominated discrete-Laplacian limit for the corrected Taylor parent integral. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ.Proofs

/-- The four-direction discrete Laplacian of the corrected Taylor integral kernel, divided by
the squared step. -/
noncomputable def planarTaylorDiscreteQuotient (k β : ℝ) (t : ℝ) (u : ℂ) : ℝ :=
  (DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u +
    DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u +
    DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u +
    DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u -
    4 * DOZZ.planarTaylorRemainder k β 1 u) / t ^ 2

private noncomputable def planarTaylorLinearCounterterm (u z : ℂ) : ℝ :=
  (z / u + star z / star u).re

private noncomputable def planarTaylorNumerator (k : ℝ) (z u : ℂ) : ℝ :=
  ‖u - z‖ ^ k - ‖u‖ ^ k +
    (k / 2) * ‖u‖ ^ k * planarTaylorLinearCounterterm u z

/-- Four-direction second-difference quotient of the radial power. -/
noncomputable def normPowerDiscreteLaplacian (k t : ℝ) (x : ℂ) : ℝ :=
  (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k +
    ‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
    4 * ‖x‖ ^ k) / t ^ 2

private theorem planarTaylorLinearCounterterm_add u z w :
    planarTaylorLinearCounterterm u (z + w) =
      planarTaylorLinearCounterterm u z + planarTaylorLinearCounterterm u w := by
  simp only [planarTaylorLinearCounterterm, add_div, star_add, Complex.add_re]
  ring




/-- Integrating the discrete quotient gives the same quotient of parent integrals. -/
theorem integral_planarTaylorDiscreteQuotient k β (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) (t : ℝ) :
    (∫ u : ℂ, planarTaylorDiscreteQuotient k β t u) =
      ((∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u) -
        4 * (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u)) / t ^ 2 := by
  let N : ℂ → ℝ := fun u =>
    DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u +
      DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u +
      DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u +
      DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u -
      4 * DOZZ.planarTaylorRemainder k β 1 u
  let f₁ := DOZZ.planarTaylorRemainder k β (1 + (t : ℂ))
  let f₂ := DOZZ.planarTaylorRemainder k β (1 - (t : ℂ))
  let f₃ := DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I)
  let f₄ := DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I)
  let f₀ := DOZZ.planarTaylorRemainder k β 1
  have hf₁ : Integrable f₁ volume := by simpa [f₁] using (integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin (1 + (t : ℂ)))
  have hf₂ : Integrable f₂ volume := by simpa [f₂] using (integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin (1 - (t : ℂ)))
  have hf₃ : Integrable f₃ volume := by simpa [f₃] using (integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin (1 + (t : ℂ) * Complex.I))
  have hf₄ : Integrable f₄ volume := by simpa [f₄] using (integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin (1 - (t : ℂ) * Complex.I))
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
  have hsum : (∫ u : ℂ, N u) =
      (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u) -
        4 * (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u) := by
    calc
      (∫ u : ℂ, N u) =
          (∫ u : ℂ, ((f₁ u + f₂ u) + f₃ u) + f₄ u - 4 * f₀ u) := by rw [(show N = fun u => ((f₁ u + f₂ u) + f₃ u) + f₄ u - 4 * f₀ u by funext u; dsimp [N, f₁, f₂, f₃, f₄, f₀])]
      _ = (∫ u : ℂ, ((f₁ u + f₂ u) + f₃ u) + f₄ u) -
          (∫ u : ℂ, 4 * f₀ u) := integral_sub
            (((hf₁.add hf₂).add hf₃).add hf₄) ((show Integrable f₀ volume by simpa [f₀] using (integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin 1)).const_mul 4)
      _ = _ := by rw [h₁₂₃₄, integral_const_mul]
  rw [(show (fun u => planarTaylorDiscreteQuotient k β t u) = fun u => (t ^ 2)⁻¹ * N u by funext u; exact div_eq_inv_mul _ _), integral_const_mul, hsum]
  simp [div_eq_mul_inv, mul_comm]

/-- Away from the fixed denominator singularity, the Taylor counterterms cancel from the
discrete Laplacian and leave the positive radial kernel. -/
theorem planarTaylorDiscreteQuotient_eq_kernel (k β : ℝ) t u :
    planarTaylorDiscreteQuotient k β t u =
      ‖u‖ ^ (-β) * normPowerDiscreteLaplacian k t (u - 1) := by
  have planarTaylorLinearCounterterm_four_shifts : planarTaylorLinearCounterterm u (1 + (t : ℂ)) + planarTaylorLinearCounterterm u (1 - (t : ℂ)) + planarTaylorLinearCounterterm u (1 + (t : ℂ) * Complex.I) + planarTaylorLinearCounterterm u (1 - (t : ℂ) * Complex.I) - 4 * planarTaylorLinearCounterterm u 1 = 0 := by
    calc
      _ = (planarTaylorLinearCounterterm u (1 + (t : ℂ)) +
            planarTaylorLinearCounterterm u (1 - (t : ℂ))) +
          (planarTaylorLinearCounterterm u (1 + (t : ℂ) * Complex.I) +
            planarTaylorLinearCounterterm u (1 - (t : ℂ) * Complex.I)) -
          4 * planarTaylorLinearCounterterm u 1 := by ring
      _ = planarTaylorLinearCounterterm u
            ((1 : ℂ) + (t : ℂ) + (1 - (t : ℂ))) +
          planarTaylorLinearCounterterm u
            ((1 : ℂ) + (t : ℂ) * Complex.I + (1 - (t : ℂ) * Complex.I)) -
          4 * planarTaylorLinearCounterterm u 1 := by
            rw [← planarTaylorLinearCounterterm_add, ← planarTaylorLinearCounterterm_add]
      _ = planarTaylorLinearCounterterm u 2 + planarTaylorLinearCounterterm u 2 -
          4 * planarTaylorLinearCounterterm u 1 := by rw [(show (1 : ℂ) + (t : ℂ) + (1 - (t : ℂ)) = 2 by ring), (show (1 : ℂ) + (t : ℂ) * Complex.I + (1 - (t : ℂ) * Complex.I) = 2 by ring)]
      _ = 0 := by
        rw [(show (2 : ℂ) = 1 + 1 by norm_num), planarTaylorLinearCounterterm_add]
        ring
  have hR z : DOZZ.planarTaylorRemainder k β z u =
      planarTaylorNumerator k z u / ‖u‖ ^ β := by
    simp [DOZZ.planarTaylorRemainder, planarTaylorNumerator,
      planarTaylorLinearCounterterm]
  rw [planarTaylorDiscreteQuotient, hR, hR, hR, hR, hR, (show (planarTaylorNumerator k (1 + (t : ℂ)) u / ‖u‖ ^ β + planarTaylorNumerator k (1 - (t : ℂ)) u / ‖u‖ ^ β + planarTaylorNumerator k (1 + (t : ℂ) * Complex.I) u / ‖u‖ ^ β + planarTaylorNumerator k (1 - (t : ℂ) * Complex.I) u / ‖u‖ ^ β - 4 * (planarTaylorNumerator k 1 u / ‖u‖ ^ β)) = (planarTaylorNumerator k (1 + (t : ℂ)) u + planarTaylorNumerator k (1 - (t : ℂ)) u + planarTaylorNumerator k (1 + (t : ℂ) * Complex.I) u + planarTaylorNumerator k (1 - (t : ℂ) * Complex.I) u - 4 * planarTaylorNumerator k 1 u) / ‖u‖ ^ β by ring), (show planarTaylorNumerator k (1 + (t : ℂ)) u + planarTaylorNumerator k (1 - (t : ℂ)) u + planarTaylorNumerator k (1 + (t : ℂ) * Complex.I) u + planarTaylorNumerator k (1 - (t : ℂ) * Complex.I) u - 4 * planarTaylorNumerator k 1 u = (‖u - (1 + (t : ℂ))‖ ^ k + ‖u - (1 - (t : ℂ))‖ ^ k + ‖u - (1 + (t : ℂ) * Complex.I)‖ ^ k + ‖u - (1 - (t : ℂ) * Complex.I)‖ ^ k - 4 * ‖u - 1‖ ^ k) by simp only [planarTaylorNumerator]; linear_combination (k / 2 * ‖u‖ ^ k) * (planarTaylorLinearCounterterm_four_shifts))]
  rw [(show u - (1 + (t : ℂ)) = (u - 1) - (t : ℂ) by ring), (show u - (1 - (t : ℂ)) = (u - 1) + (t : ℂ) by ring), (show u - (1 + (t : ℂ) * Complex.I) = (u - 1) - (t : ℂ) * Complex.I by ring), (show u - (1 - (t : ℂ) * Complex.I) = (u - 1) + (t : ℂ) * Complex.I by ring), Real.rpow_neg (norm_nonneg u) β]
  simp only [normPowerDiscreteLaplacian]
  ring

/-- The pointwise limit of the corrected parent quotient is the positive Riesz kernel. -/
theorem planarTaylorDiscreteQuotient_tendsto (k β : ℝ) u (hu : u ≠ 1) :
    Tendsto (fun t : ℝ => planarTaylorDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
  let w := ‖u‖ ^ (-β)
  simpa [w, mul_assoc, mul_left_comm, mul_comm] using ((tendsto_const_nhds.mul (norm_rpow_discrete_laplacian_tendsto k (u - 1) (sub_ne_zero.mpr hu))).congr' (show (fun t => planarTaylorDiscreteQuotient k β t u) =ᶠ[𝓝[≠] (0 : ℝ)] fun t => w * normPowerDiscreteLaplacian k t (u - 1) by filter_upwards [] with t; exact planarTaylorDiscreteQuotient_eq_kernel k β t u).symm)

/-- A uniform Riesz-kernel majorant for the discrete quotients, away from the null collision. -/
theorem planarTaylorDiscreteQuotient_norm_le (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hk₂ : β < 2)
    u t (hu : u ≠ 1) (ht : t ≠ 0) :
    ‖planarTaylorDiscreteQuotient k β t u‖ ≤
      (2 * (2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
        (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
        2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))) *
        (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)) := by
  let C := 2 * (2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
    (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
    2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
  have hw : 0 ≤ ‖u‖ ^ (-β) := Real.rpow_nonneg (norm_nonneg u) _
  rw [(planarTaylorDiscreteQuotient_eq_kernel k β t u), Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  change ‖u‖ ^ (-β) * |normPowerDiscreteLaplacian k t (u - 1)| ≤
    C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
  calc
    _ ≤ ‖u‖ ^ (-β) * (C * ‖u - 1‖ ^ (k - 2)) :=
      mul_le_mul_of_nonneg_left (by simpa [C, normPowerDiscreteLaplacian] using (norm_rpow_discrete_laplacian_le k hk (by linarith [hβ, hk₂]) (u - 1) t (sub_ne_zero.mpr hu) ht)) hw
    _ = C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)) := by ring

/-- Dominated convergence identifies the limiting integral of the Taylor discrete quotient with
the positive Riesz convolution multiplied by `k^2`. -/
theorem planarTaylorDiscreteQuotient_integral_tendsto (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) :
    Tendsto (fun t : ℝ => ∫ u : ℂ, planarTaylorDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ u : ℂ, k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
  have integrable_planarTaylorDiscreteQuotient t : Integrable (planarTaylorDiscreteQuotient k β t) volume := by
    change Integrable (fun u : ℂ =>
      (DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u +
        DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u +
        DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u +
        DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u -
        4 * DOZZ.planarTaylorRemainder k β 1 u) / t ^ 2)
    exact ((show Integrable (fun u => DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u + DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u + DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u + DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u - 4 * DOZZ.planarTaylorRemainder k β 1 u) volume by exact ((((integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin (1 + (t : ℂ))).add (integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin (1 - (t : ℂ)))).add (integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin (1 + (t : ℂ) * Complex.I))).add (integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin (1 - (t : ℂ) * Complex.I))).sub ((integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin 1).const_mul 4))).div_const (t ^ 2)
  let K := 2 * (2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
    (1 / 4 : ℝ) ^ (k / 2 - 2)))) + 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
  let bound : ℂ → ℝ := fun u => K * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
    (by filter_upwards [] with t; exact (integrable_planarTaylorDiscreteQuotient t).aestronglyMeasurable) (by filter_upwards [self_mem_nhdsWithin] with t ht; filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu; simpa [bound, K] using planarTaylorDiscreteQuotient_norm_le k β hk hβ hβ₂ u t hu (by simpa using ht)) (by simpa [bound, K, mul_assoc] using (positive_riesz_convolution_integrable k β hk hβ hβ₂ 1 (by norm_num)).const_mul K) (by filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu; exact planarTaylorDiscreteQuotient_tendsto k β u hu)

end DOZZ.Proofs
