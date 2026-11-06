/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarGaussConstant
public import DOZZ.Statements.Hypergeom.PlanarMixedKernel
public import DOZZ.Hypergeom.Planar.DerivativeIntegrable
public import DOZZ.Hypergeom.Planar.RieszConvolution

/-! Normalize the Riesz convolution constant to the planar constant `DOZZ.planarGaussConstant`. -/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace DOZZ.Proofs

private theorem lFun_real_argument (x : ℝ) :
    DOZZ.lFun (x : ℝ) =
      ((Real.Gamma x / Real.Gamma (1 - x) : ℝ) : ℂ) := by
  change Complex.Gamma x / Complex.Gamma _ = _
  have harg : 1 - x = ((1 - x : ℝ) : ℂ) := by
    norm_cast
  rw [harg, Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_div]
section
variable (k β : ℝ)
section
variable (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2)
include hk hβ hβ₂

/-- The Riesz convolution coefficient, after the mixed derivative, is the constant
`planarGaussConstant` (erratum K8, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem positive_riesz_coefficient_eq_planarGaussConstant :
    ((
      ((k / 2) ^ 2 / ((2 + k - β) / 2) ^ 2) * Real.pi *
        (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
          Real.Gamma ((β - k) / 2) /
            (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
              Real.Gamma (1 + (k - β) / 2)))
      : ℝ) : ℂ) =
      DOZZ.planarGaussConstant k β := by
  have hC := lFun_real_argument (2 - β / 2 + k / 2)
  rw [DOZZ.planarGaussConstant, (lFun_real_argument _), (lFun_real_argument _), hC]
  norm_cast
  have hb : 0 < k / 2 := by linarith
  have hd : 0 < (β - k) / 2 := by linarith
  have hq : 0 < (2 + k - β) / 2 := by linarith
  have hb₁ : 0 < 1 - k / 2 := by linarith
  have ha : 0 < β / 2 := by linarith
  have ha₁ : 0 < 1 - β / 2 := by linarith
  have hgB : Real.Gamma (1 + k / 2) = (k / 2) * Real.Gamma (k / 2) := by
    rw [show 1 + k / 2 = k / 2 + 1 by ring]
    exact Real.Gamma_add_one hb.ne'
  have hgNegB : Real.Gamma (1 - k / 2) = (-k / 2) * Real.Gamma (-k / 2) := by
    have h := Real.Gamma_add_one (by linarith : -k / 2 ≠ 0)
    convert h using 1
    ring_nf
  have hgNegB' : Real.Gamma (-k / 2) =
      Real.Gamma (1 - k / 2) / (-k / 2) := by
    calc
      Real.Gamma _ = ((-k / 2) * Real.Gamma (-k / 2)) / (-k / 2) := by
        field_simp [ne_of_gt hb]
      _ = Real.Gamma (1 - k / 2) / (-k / 2) := by simp_all
  have hgQ : Real.Gamma (1 + (2 + k - β) / 2) =
      ((2 + k - β) / 2) * Real.Gamma ((2 + k - β) / 2) := by
    rw [show 1 + (2 + k - β) / 2 = (2 + k - β) / 2 + 1 by ring]
    exact Real.Gamma_add_one hq.ne'
  have hgNegQ : Real.Gamma ((β - k) / 2) =
      (-((2 + k - β) / 2)) * Real.Gamma (-((2 + k - β) / 2)) := by
    have h := Real.Gamma_add_one (by linarith : -((2 + k - β) / 2) ≠ 0)
    convert h using 1
    ring_nf
  have hgNegQ' : Real.Gamma (-((2 + k - β) / 2)) =
      Real.Gamma ((β - k) / 2) / (-((2 + k - β) / 2)) := by
    calc
      Real.Gamma _ =
          ((-((2 + k - β) / 2)) * Real.Gamma _) /
            (-((2 + k - β) / 2)) := by
        field_simp [ne_of_gt (show 0 < 2 + k - β by linarith)]
      _ = Real.Gamma _ / (-((2 + k - β) / 2)) := by tauto
  rw [show 1 - (2 - β / 2 + k / 2) = -((2 + k - β) / 2) by ring,
    show 1 + (k - β) / 2 = (2 + k - β) / 2 by ring,
    show 2 - β / 2 + k / 2 = 1 + (2 + k - β) / 2 by ring,
    show 1 - -k / 2 = 1 + k / 2 by ring,
    hgB, hgNegB', hgQ, hgNegQ']
  field_simp [
    ne_of_gt (Real.Gamma_pos_of_pos ha),
    ne_of_gt (Real.Gamma_pos_of_pos ha₁),
    ne_of_gt (Real.Gamma_pos_of_pos hb),
    ne_of_gt (Real.Gamma_pos_of_pos hb₁),
    ne_of_gt (Real.Gamma_pos_of_pos hd),
    ne_of_gt (Real.Gamma_pos_of_pos hq)]

/-- The mixed-kernel integral is the positive Riesz convolution, with its constant normalized to the
coefficient `planarGaussConstant` (erratum K8, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem planar_mixed_integral :
    ∀ z : ℂ, z ≠ 0 → Integrable (DOZZ.planarMixedKernel k β z) volume ∧
      (((k / 2) ^ 2 * (∫ u : ℂ, DOZZ.planarMixedKernel k β z u)) : ℝ) =
        (((2 + k - β) / 2) ^ 2 * ‖z‖ ^ (k - β) : ℝ) *
          DOZZ.planarGaussConstant k β := by
  intro z hz
  have hInt := positive_riesz_convolution_integrable k β hk hβ hβ₂ z hz
  have heq : (fun u : ℂ => DOZZ.planarMixedKernel k β z u) =ᵐ[volume]
      (fun u => ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2)) := by
    filter_upwards [Measure.ae_ne volume 0] with u hu
    change ‖u - z‖ ^ (k - 2) / ‖u‖ ^ β = _
    rw [div_eq_mul_inv, Real.rpow_neg (norm_nonneg u)]
    ring
  have hkernelInt : Integrable (DOZZ.planarMixedKernel k β z) volume := by
    rwa [integrable_congr heq]
  have hconv : (∫ u : ℂ, DOZZ.planarMixedKernel k β z u) =
      Real.pi * (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
        Real.Gamma ((β - k) / 2) /
          (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
            Real.Gamma (1 + (k - β) / 2))) * ‖z‖ ^ (k - β) := by
    calc
      _ = ∫ u : ℂ, ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2) := integral_congr_ae heq
      _ = _ := (positive_riesz_convolution_integral k β hk hβ hβ₂ z hz)
  let q := (2 + k - β) / 2
  let C := Real.pi * (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
    Real.Gamma ((β - k) / 2) /
      (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
        Real.Gamma (1 + (k - β) / 2)))
  let N := ‖z‖ ^ (k - β)
  have hq : 0 < q := by grind
  have hC : (((k / 2) ^ 2 / q ^ 2 * C : ℝ) : ℂ) = DOZZ.planarGaussConstant k β := by
    calc
      _ = ((((k / 2) ^ 2 / ((2 + k - β) / 2) ^ 2) * Real.pi *
          (Real.Gamma _ * Real.Gamma _ *
            Real.Gamma _ /
              (Real.Gamma _ * Real.Gamma _ *
                Real.Gamma _)) : ℝ) : ℂ) := by
            apply congrArg Complex.ofReal
            ring
      _ = DOZZ.planarGaussConstant k β :=
            positive_riesz_coefficient_eq_planarGaussConstant k β hk hβ hβ₂
  have halg : (k / 2) ^ 2 * C * N = (q ^ 2 * N) * ((k / 2) ^ 2 / q ^ 2 * C) := by
    field_simp [ne_of_gt hq]
  refine ⟨hkernelInt, ?_⟩
  change Complex.ofReal ((k / 2) ^ 2 * (∫ u : ℂ, DOZZ.planarMixedKernel k β z u)) =
    Complex.ofReal _ * DOZZ.planarGaussConstant k β
  calc
    _ = Complex.ofReal ((k / 2) ^ 2 * C * N) := by
      rw [hconv]
      exact congrArg Complex.ofReal (by linarith)
    _ = ((q ^ 2 * N : ℝ) : ℂ) * ((k / 2) ^ 2 / q ^ 2 * C : ℝ) := by
      rw [← Complex.ofReal_mul]
      exact congrArg Complex.ofReal halg
    _ = _ := by tauto

end

end

end DOZZ.Proofs
