/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarGaussConstant
public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel
public import DOZZ.Hypergeom.Planar.DifferenceDiscreteLaplacian
public import DOZZ.Hypergeom.Planar.TaylorNormalization
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The KRV difference integral follows from scaling and its Riesz discrete Laplacian. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs


/-- Proof of the difference-integral statement `DOZZ.planar_difference_integral`. -/
theorem planar_difference_integral k β (hk : 0 < k)
    (hβ : k + 1 < β) (hβ₂ : β < 2) :
    ∀ z : ℂ, Integrable (DOZZ.planarDifferenceKernel k β z) volume ∧
      ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) : ℂ) =
        (‖z‖ ^ (2 + k - β) : ℝ) * DOZZ.planarGaussConstant k β := by
  have planarDifference_constant_from_discrete_laplacian (hβ : k < β) (hβ₂ : β < 2) (hβtail : k + 1 < β) : ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u : ℝ) : ℂ) = DOZZ.planarGaussConstant k β := by
    let α : ℝ := 2 + k - β
    let A := ∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u
    let l := 𝓝[≠] (0 : ℝ)
    let P : ℝ → ℝ := fun t =>
      ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u) +
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u) -
        4 * A) / t ^ 2
    have hα : 0 < α := by dsimp [α]; linarith
    have hscale z :
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) = ‖z‖ ^ α * A := by
      simpa [α, A] using
        planarDifferenceKernel_integral_scale_norm k β hk hβ hβ₂ z
    have hParentEq : P =ᶠ[l]
        fun t => A * normPowerDiscreteLaplacian α t 1 := by
      filter_upwards [] with t
      change ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 + (t : ℂ) * Complex.I) u) +
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β (1 - (t : ℝ) * Complex.I) u) -
        4 * A) / t ^ 2 = _
      rw [(hscale (1 + (t : ℂ))), (hscale (1 - (t : ℂ))), (hscale (1 + (t : ℂ) * Complex.I)), (hscale (1 - (t : ℝ) * Complex.I))]
      simp only [normPowerDiscreteLaplacian, norm_one, Real.one_rpow]
      ring
    have hRad := norm_rpow_discrete_laplacian_tendsto α 1 (by norm_num)
    have hDct := planarDifferenceDiscreteQuotient_integral_tendsto
      k β hk hβ hβ₂ hβtail
    have hQEq :
        (fun t => ∫ u : ℂ, planarDifferenceDiscreteQuotient k β t u) =ᶠ[l] P := by
      filter_upwards [] with t
      simpa [P, A] using
        integral_planarDifferenceDiscreteQuotient k β hk hβ hβ₂ hβtail t
    have hRiesz := positive_riesz_convolution_integral k β hk hβ hβ₂ 1 (by norm_num)
    let G := Real.pi *
      (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) * Real.Gamma ((β - k) / 2) /
        (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
          Real.Gamma (1 + (k - β) / 2)))
    have hRealCoeff : k ^ 2 * G = α ^ 2 * A := by
      simpa [(show (∫ u : ℂ, ‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)) = G by simpa [G, norm_one, Real.one_rpow] using hRiesz)] using (tendsto_nhds_unique (show Tendsto P l (𝓝 (k ^ 2 * (∫ u : ℂ, ‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) by simpa only [MeasureTheory.integral_const_mul] using (hDct.congr' hQEq)) (by simpa [norm_one, Real.one_rpow, mul_assoc, mul_left_comm, mul_comm] using ((tendsto_const_nhds.mul hRad : Tendsto (fun t => A * normPowerDiscreteLaplacian α t 1) l (𝓝 (A * (α ^ 2 * ‖(1 : ℂ)‖ ^ (α - 2))))).congr' hParentEq.symm)))
    have hαsq := pow_ne_zero 2 hα.ne'
    have hA : A = (k ^ 2 / α ^ 2) * G := by
      calc
        A = α ^ 2 * A / α ^ 2 := by field_simp [hαsq]
        _ = k ^ 2 * G / α ^ 2 := by rw [hRealCoeff]
        _ = (k ^ 2 / α ^ 2) * G := by ring
    calc
      (A : ℂ) = (((k ^ 2 / α ^ 2) * G : ℝ) : ℂ) := congrArg Complex.ofReal hA
      _ = ((((k / 2) ^ 2 / (α / 2) ^ 2) * G : ℝ) : ℂ) := by rw [(show k ^ 2 / α ^ 2 = (k / 2) ^ 2 / (α / 2) ^ 2 by field_simp [hαsq])]
      _ = DOZZ.planarGaussConstant k β := by
        dsimp [G, α]
        simpa [mul_assoc, mul_left_comm, mul_comm] using (positive_riesz_coefficient_eq_planarGaussConstant k β hk hβ hβ₂)
  intro z
  refine ⟨(integrable_planarDifferenceKernel k β hk (by linarith) hβ₂ hβ) z, ?_⟩
  rw [integral_complex_ofReal]
  calc
    ((∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u : ℝ) : ℂ) =
        ((‖z‖ ^ (2 + k - β) *
          (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) : ℝ) : ℂ) :=
            congrArg Complex.ofReal ((planarDifferenceKernel_integral_scale_norm k β hk (by linarith) hβ₂) z)
    _ = Complex.ofReal (‖z‖ ^ (2 + k - β)) *
        Complex.ofReal (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by
          rw [Complex.ofReal_mul]
    _ = Complex.ofReal (‖z‖ ^ (2 + k - β)) * DOZZ.planarGaussConstant k β := by rw [(planarDifference_constant_from_discrete_laplacian (by linarith) hβ₂ hβ)]

end DOZZ.Proofs
