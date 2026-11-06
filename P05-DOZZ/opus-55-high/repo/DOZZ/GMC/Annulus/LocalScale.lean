/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.WeightedShell
public import DOZZ.GMC.Moments.SubunitSet

/-!
# Exact local ball scaling and its finite subunit bounds

The affine law on the logarithmic unit chart is an identity at every real order. The
reference moment is retained as an extended value; only actual moment estimates permit
replacing it by a finite constant. The proved subunit input already supplies sharp upper
bounds, with the true Gaussian exponent, uniformly in charge and moment order.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (z : ℂ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R) (hR1 : R < 1) (hzr : ‖z‖ + r < 1) (p : ℝ)
include hX hγ hγ2 hM hr hR hrR hR1 hzr

/-- Exact scaling expressed using the radius itself, with the Gaussian exponent
`gmcScaleExponent`. -/
theorem gmc_local_ball_moment_scale
    :
    gmcMassMoment P M (Metric.ball z r) p =
      ENNReal.ofReal ((r / R) ^ gmcScaleExponent γ p) *
        gmcMassMoment P M (Metric.ball 0 R) p := by
  have he : r / R * R = r := div_mul_cancel₀ _ hR.ne'
  have h := gmc_affine_openBall_moment_scale P X hX γ hγ hγ2 M hM
    (div_pos hr hR)
    ((div_le_one hR).mpr hrR) hR hR1 (by linarith) p
  rwa [he, ← gmcScaleExponent_eq_polynomial γ p hγ.ne'] at h

/-- The ratio law keeps the true radius exponent and puts reference radius dependence in a
strictly positive finite scalar. -/
theorem gmc_local_ball_moment_radius_factor
    :
    gmcMassMoment P M (Metric.ball z r) p =
      ENNReal.ofReal (R ^ (-gmcScaleExponent γ p)) *
        ENNReal.ofReal (r ^ gmcScaleExponent γ p) *
        gmcMassMoment P M (Metric.ball 0 R) p := by
  rw [gmc_local_ball_moment_scale P X hX γ hγ hγ2 M hM z hr hR hrR hR1 hzr p]
  have hf : (r / R) ^ gmcScaleExponent γ p =
      R ^ (-gmcScaleExponent γ p) * r ^ gmcScaleExponent γ p := by
    rw [div_eq_mul_inv, Real.mul_rpow hr.le (inv_pos.mpr hR).le,
      Real.inv_rpow hR.le, ← Real.rpow_neg hR.le]
    linarith
  rw [hf, ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]

/-- Local scaling preserves infinite moments as well as finite ones. -/
theorem gmc_local_ball_moment_finite_iff
    :
    gmcMassMoment P M (Metric.ball z r) p < ⊤ ↔
      gmcMassMoment P M (Metric.ball 0 R) p < ⊤ := by
  have he : r / R * R = r := div_mul_cancel₀ _ hR.ne'
  simpa only [he] using gmc_affine_openBall_moment_finite_iff P X hX γ hγ hγ2 M hM
    (div_pos hr hR)
    ((div_le_one hR).mpr hrR) hR hR1 (by linarith) p

end
section
variable (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include hX hγ hγ2 hM

/-- The exact local ball moment is independent of its center while its translated disk stays
inside the unit logarithmic chart. This is equality of actual GMC moments at every real order. -/
theorem gmc_local_ball_moment_center_eq
    (z w : ℂ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (hR1 : R < 1) (hzr : ‖z‖ + r < 1) (hwr : ‖w‖ + r < 1) (p : ℝ) :
    gmcMassMoment P M (Metric.ball z r) p = gmcMassMoment P M (Metric.ball w r) p := by
  rw [gmc_local_ball_moment_scale P X hX γ hγ hγ2 M hM z hr hR hrR hR1 hzr p,
    gmc_local_ball_moment_scale P X hX γ hγ hγ2 M hM w hr hR hrR hR1 hwr p]

/-- On the exact local chart, a positive finite reference moment is equivalent to the full
two-sided scaling estimate at that order. Finiteness of the reference moment is one side of the
equivalence, not an assumption, at every order including the inverse ones. -/
theorem gmc_local_twoSided_ball_scaling_iff
    (R p : ℝ) (hR : 0 < R) (hR1 : R < 1) :
    (0 < gmcMassMoment P M (Metric.ball 0 R) p ∧
        gmcMassMoment P M (Metric.ball 0 R) p < ⊤) ↔
      ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ R → ‖z‖ + r < 1 →
        ENNReal.ofReal (C⁻¹ * r ^ gmcScaleExponent γ p) ≤
            gmcMassMoment P M (Metric.ball z r) p ∧
          gmcMassMoment P M (Metric.ball z r) p ≤
            ENNReal.ofReal (C * r ^ gmcScaleExponent γ p) := by
  let B := gmcMassMoment P M (Metric.ball 0 R) p
  let ξ := gmcScaleExponent γ p
  constructor
  · rintro ⟨hBp, hBf⟩
    have hBreal : 0 < B.toReal := ENNReal.toReal_pos hBp.ne' hBf.ne
    let D := R ^ (-ξ) * B.toReal
    have hD : 0 < D := by positivity
    let C := max D D⁻¹
    have hC : 0 < C := by positivity
    have hDC : D ≤ C := le_max_left ..
    have hCD : C⁻¹ ≤ D := by
      grind
    refine ⟨C, hC, ?_⟩
    intro z r hr hrR hzr
    have he : gmcMassMoment P M (Metric.ball z r) p = ENNReal.ofReal (D * r ^ ξ) := by
      rw [gmc_local_ball_moment_radius_factor P X hX γ hγ hγ2 M hM z hr hR hrR hR1 hzr p]
      have hB : B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hBf.ne).symm
      change ENNReal.ofReal (R ^ (-ξ)) * ENNReal.ofReal (r ^ ξ) * B = _
      rw [hB, ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hR.le _)
          (Real.rpow_nonneg hr.le _))]
      grind
    rw [he]
    exact ⟨ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCD
        (Real.rpow_nonneg hr.le ξ)),
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hDC
        (Real.rpow_nonneg hr.le ξ))⟩
  · rintro ⟨C, hC, hBound⟩
    have hb := hBound 0 R hR le_rfl (by simp_all)
    have hpref :=
      ENNReal.ofReal_pos.mpr (mul_pos (inv_pos.mpr hC) (Real.rpow_pos_of_pos hR ξ))
    exact ⟨hpref.trans_le hb.1, hb.2.trans_lt ENNReal.ofReal_lt_top⟩

end

end

end DOZZ.Proofs
