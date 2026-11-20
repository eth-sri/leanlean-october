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
  change Complex.Gamma (x : ℂ) / Complex.Gamma (1 - (x : ℂ)) = _
  have harg : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by
    norm_cast
  rw [harg, Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_div]

/-- The Riesz coefficient normalized by the powers in the mixed derivative. -/
noncomputable def planarRieszCoefficientReal (k β : ℝ) : ℝ :=
  (k / 2) ^ 2 / ((2 + k - β) / 2) ^ 2 * planarRieszConstant k β

private theorem gamma_neg_eq {x : ℝ} (hx : x ≠ 0) :
    Real.Gamma (-x) = Real.Gamma (1 - x) / (-x) := by
  rw [sub_eq_add_neg, add_comm, Real.Gamma_add_one (neg_ne_zero.mpr hx), mul_div_cancel_left₀ _ (neg_ne_zero.mpr hx)]

/-- The Riesz convolution coefficient, after the mixed derivative, is the constant
`planarGaussConstant` (erratum K8, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem positive_riesz_coefficient_eq_planarGaussConstant (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) :
    (planarRieszCoefficientReal k β : ℂ) = DOZZ.planarGaussConstant k β := by
  rw [DOZZ.planarGaussConstant, lFun_real_argument, lFun_real_argument, lFun_real_argument]
  norm_cast
  let q := (2 + k - β) / 2
  have hq : 0 < q := by dsimp [q]; linarith
  have hb : 0 < k / 2 := by positivity
  rw [planarRieszCoefficientReal, planarRieszConstant,
    show 1 + (k - β) / 2 = q by dsimp [q]; ring,
    show (β - k) / 2 = 1 - q by dsimp [q]; ring,
    show 2 - β / 2 + k / 2 = q + 1 by dsimp [q]; ring,
    show 1 - (q + 1) = -q by ring,
    show -k / 2 = -(k / 2) by ring,
    show 1 - -(k / 2) = k / 2 + 1 by ring,
    Real.Gamma_add_one hq.ne', Real.Gamma_add_one hb.ne',
    gamma_neg_eq hq.ne', gamma_neg_eq hb.ne']
  change (k / 2) ^ 2 / q ^ 2 * _ = _
  have hΓ (x : ℝ) (hx : 0 < x) : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  field_simp [hq.ne', hb.ne', hΓ q hq, hΓ (k / 2) hb,
    hΓ (β / 2) (by linarith), hΓ (1 - β / 2) (by linarith),
    hΓ (1 - k / 2) (by linarith), hΓ (1 - q) (by dsimp [q]; linarith)]

/-- The mixed-kernel integral is the positive Riesz convolution, with its constant normalized to the
coefficient `planarGaussConstant` (erratum K8, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem planar_mixed_integral (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) :
    ∀ z : ℂ, z ≠ 0 → Integrable (DOZZ.planarMixedKernel k β z) volume ∧
      (((k / 2) ^ 2 * (∫ u : ℂ, DOZZ.planarMixedKernel k β z u)) : ℝ) =
        (((2 + k - β) / 2) ^ 2 * ‖z‖ ^ (k - β) : ℝ) *
          DOZZ.planarGaussConstant k β := by
  intro z hz
  have heq (u : ℂ) : DOZZ.planarMixedKernel k β z u = ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2) := by
    simp [DOZZ.planarMixedKernel, div_eq_mul_inv, Real.rpow_neg (norm_nonneg u), mul_comm]
  refine ⟨(positive_riesz_convolution_integrable k β hk hβ hβ₂ z hz).congr
    (.of_forall (fun u => (heq u).symm)), ?_⟩
  rw [integral_congr_ae (.of_forall heq), positive_riesz_convolution_integral k β hk hβ hβ₂ z hz,
    ← positive_riesz_coefficient_eq_planarGaussConstant k β hk hβ hβ₂, ← Complex.ofReal_mul]
  congr 1
  unfold planarRieszCoefficientReal
  field_simp [show (2 + k - β) ≠ 0 by linarith]

end DOZZ.Proofs
