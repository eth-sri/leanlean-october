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
noncomputable def normPowerDiscreteLaplacian (k : ℝ) (t : ℝ) (x : ℂ) : ℝ :=
  (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k +
    ‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
    4 * ‖x‖ ^ k) / t ^ 2

private theorem planarTaylorLinearCounterterm_four_shifts (u : ℂ) (t : ℝ) :
    planarTaylorLinearCounterterm u (1 + (t : ℂ)) +
        planarTaylorLinearCounterterm u (1 - (t : ℂ)) +
        planarTaylorLinearCounterterm u (1 + (t : ℂ) * Complex.I) +
        planarTaylorLinearCounterterm u (1 - (t : ℂ) * Complex.I) -
        4 * planarTaylorLinearCounterterm u 1 = 0 := by
  simp [planarTaylorLinearCounterterm, add_div, sub_div] <;> ring_nf <;> simp

variable (k β : ℝ) (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1)


include k β hk hβ hβ₂ hβlin in
/-- The discrete quotient is integrable for every step. -/
theorem integrable_planarTaylorDiscreteQuotient  (t : ℝ) :
    Integrable (planarTaylorDiscreteQuotient k β t) volume := by
  have hi := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin
  unfold planarTaylorDiscreteQuotient
  fun_prop

include k β hk hβ hβ₂ hβlin in
/-- Integrating the discrete quotient gives the same quotient of parent integrals. -/
theorem integral_planarTaylorDiscreteQuotient  (t : ℝ) :
    (∫ u : ℂ, planarTaylorDiscreteQuotient k β t u) =
      ((∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u) -
        4 * (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u)) / t ^ 2 := by
  have hi := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin
  simp (disch := fun_prop) only [planarTaylorDiscreteQuotient,
    integral_div, integral_sub, integral_add, integral_const_mul]

/-- Away from the fixed denominator singularity, the Taylor counterterms cancel from the
discrete Laplacian and leave the positive radial kernel. -/
theorem planarTaylorDiscreteQuotient_eq_kernel (k β : ℝ) (t : ℝ) (u : ℂ) :
    planarTaylorDiscreteQuotient k β t u =
      ‖u‖ ^ (-β) * normPowerDiscreteLaplacian k t (u - 1) := by
  have hcounter := planarTaylorLinearCounterterm_four_shifts u t
  have hnum :
      planarTaylorNumerator k (1 + (t : ℂ)) u +
        planarTaylorNumerator k (1 - (t : ℂ)) u +
        planarTaylorNumerator k (1 + (t : ℂ) * Complex.I) u +
        planarTaylorNumerator k (1 - (t : ℂ) * Complex.I) u -
        4 * planarTaylorNumerator k 1 u =
        (‖u - (1 + (t : ℂ))‖ ^ k + ‖u - (1 - (t : ℂ))‖ ^ k +
          ‖u - (1 + (t : ℂ) * Complex.I)‖ ^ k +
          ‖u - (1 - (t : ℂ) * Complex.I)‖ ^ k - 4 * ‖u - 1‖ ^ k) := by
    simp only [planarTaylorNumerator]
    linear_combination (k / 2 * ‖u‖ ^ k) * hcounter
  have hR (z : ℂ) : DOZZ.planarTaylorRemainder k β z u =
      planarTaylorNumerator k z u / ‖u‖ ^ β := by
    simp [DOZZ.planarTaylorRemainder, planarTaylorNumerator,
      planarTaylorLinearCounterterm]
  have hcombine :
      (planarTaylorNumerator k (1 + (t : ℂ)) u / ‖u‖ ^ β +
        planarTaylorNumerator k (1 - (t : ℂ)) u / ‖u‖ ^ β +
        planarTaylorNumerator k (1 + (t : ℂ) * Complex.I) u / ‖u‖ ^ β +
        planarTaylorNumerator k (1 - (t : ℂ) * Complex.I) u / ‖u‖ ^ β -
        4 * (planarTaylorNumerator k 1 u / ‖u‖ ^ β)) =
      (planarTaylorNumerator k (1 + (t : ℂ)) u +
        planarTaylorNumerator k (1 - (t : ℂ)) u +
        planarTaylorNumerator k (1 + (t : ℂ) * Complex.I) u +
        planarTaylorNumerator k (1 - (t : ℂ) * Complex.I) u -
        4 * planarTaylorNumerator k 1 u) / ‖u‖ ^ β := by ring
  rw [planarTaylorDiscreteQuotient, hR, hR, hR, hR, hR, hcombine, hnum]
  have h₁ : u - (1 + (t : ℂ)) = (u - 1) - (t : ℂ) := by ring
  have h₂ : u - (1 - (t : ℂ)) = (u - 1) + (t : ℂ) := by ring
  have h₃ : u - (1 + (t : ℂ) * Complex.I) =
      (u - 1) - (t : ℂ) * Complex.I := by ring
  have h₄ : u - (1 - (t : ℂ) * Complex.I) =
      (u - 1) + (t : ℂ) * Complex.I := by ring
  rw [h₁, h₂, h₃, h₄]
  rw [Real.rpow_neg (norm_nonneg u) β]
  simp only [normPowerDiscreteLaplacian]
  ring

/-- The pointwise limit of the corrected parent quotient is the positive Riesz kernel. -/
theorem planarTaylorDiscreteQuotient_tendsto (k β : ℝ) (u : ℂ) (hu : u ≠ 1) :
    Tendsto (fun t : ℝ => planarTaylorDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
  have hx : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  let w  := ‖u‖ ^ (-β)
  have hLap := norm_rpow_discrete_laplacian_tendsto k (u - 1) hx
  have hmul : Tendsto (fun t : ℝ => w * normPowerDiscreteLaplacian k t (u - 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 (w * (k ^ 2 * ‖u - 1‖ ^ (k - 2)))) :=
    tendsto_const_nhds.mul hLap
  have hEq : (fun t : ℝ => planarTaylorDiscreteQuotient k β t u) =ᶠ[𝓝[≠] (0 : ℝ)]
      fun t => w * normPowerDiscreteLaplacian k t (u - 1) := by
    filter_upwards [] with t
    exact planarTaylorDiscreteQuotient_eq_kernel k β t u
  have hlim := hmul.congr' hEq.symm
  simpa [w, mul_assoc, mul_left_comm, mul_comm] using hlim

/-- A uniform Riesz-kernel majorant for the discrete quotients, away from the null collision. -/
theorem planarTaylorDiscreteQuotient_norm_le (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hk₂ : β < 2)
    (u : ℂ) (t : ℝ) (hu : u ≠ 1) (ht : t ≠ 0) :
    ‖planarTaylorDiscreteQuotient k β t u‖ ≤
      (2 * (2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
        (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
        2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))) *
        (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)) := by
  let C  := 2 * (2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
    (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
    2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
  have hx : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hLap := norm_rpow_discrete_laplacian_le k hk (by linarith [hβ, hk₂])
    (u - 1) t hx ht
  have hw : 0 ≤ ‖u‖ ^ (-β) := Real.rpow_nonneg (norm_nonneg u) _
  have hkernel := planarTaylorDiscreteQuotient_eq_kernel k β t u
  rw [hkernel, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  change ‖u‖ ^ (-β) * |normPowerDiscreteLaplacian k t (u - 1)| ≤
    C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
  calc
    _ ≤ ‖u‖ ^ (-β) * (C * ‖u - 1‖ ^ (k - 2)) :=
      mul_le_mul_of_nonneg_left (by simpa [C, normPowerDiscreteLaplacian] using hLap) hw
    _ = C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)) := by ring

include k β hk hβ hβ₂ hβlin in
/-- Dominated convergence identifies the limiting integral of the Taylor discrete quotient with
the positive Riesz convolution multiplied by `k^2`. -/
theorem planarTaylorDiscreteQuotient_integral_tendsto  :
    Tendsto (fun t : ℝ => ∫ u : ℂ, planarTaylorDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ u : ℂ, k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
  let K  := 2 * (2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
    (1 / 4 : ℝ) ^ (k / 2 - 2)))) + 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
  let bound : ℂ → ℝ := fun u => K * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
  have hK : 0 ≤ K := by
    dsimp [K]
    have hk₂ : 0 < 1 - k / 2 := by linarith [hβ, hβ₂]
    positivity
  have hRiesz := positive_riesz_convolution_integrable k β hk hβ hβ₂ 1 (by norm_num)
  have hboundInt : Integrable bound volume := by
    simpa [bound, K, mul_assoc] using hRiesz.const_mul K
  have hmeas : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      AEStronglyMeasurable (planarTaylorDiscreteQuotient k β t) volume := by
    filter_upwards [] with t
    exact (integrable_planarTaylorDiscreteQuotient k β hk hβ hβ₂ hβlin t).aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ∀ᵐ u ∂volume, ‖planarTaylorDiscreteQuotient k β t u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
    simpa [bound, K] using
      planarTaylorDiscreteQuotient_norm_le k β hk hβ hβ₂ u t hu ht0
  have hlim : ∀ᵐ u ∂volume, Tendsto
      (fun t : ℝ => planarTaylorDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
    filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
    exact planarTaylorDiscreteQuotient_tendsto k β u hu
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
    hmeas hbound hboundInt hlim

end DOZZ.Proofs
