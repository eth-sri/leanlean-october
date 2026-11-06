module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm

/-!
# Componentwise parabolic Morrey-norm scaling

This module records restricted `L^(d + 1)` scaling for the four selected
smooth scalar fields under positive parabolic affine pullback.  The primary
statements retain the inverse-Jacobian factor in `ENNReal`; real-valued
presentations are available only together with an explicit finiteness result.

There is deliberately no scaling statement for the full selected smooth jet:
its value, first-velocity, and second-order components have different factors.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

/-- The inverse-Jacobian `L^(d + 1)` factor of positive parabolic pullback. -/
def parabolicELpNormPullbackMeasureFactor (d : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((r ^ (d + 2))⁻¹) ^
    (1 / parabolicExponent d).toReal

private theorem parabolicELpNormPullbackMeasureFactor_ne_top (d : ℕ) (r : ℝ) :
    parabolicELpNormPullbackMeasureFactor d r ≠ ⊤ := by
  unfold parabolicELpNormPullbackMeasureFactor
  exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top

private theorem parabolicELpNormOn_pullbackScalar_unamplified
    {d } (t₀ : ℝ) (v₀ : PDE.Vec d) {r } (hr : 0 < r)
    (q : TimeVelocity d → ℝ) (s : Set (TimeVelocity d)) :
    parabolicELpNormOn d (pullbackScalar q t₀ v₀ r) s =
      parabolicELpNormPullbackMeasureFactor d r *
        parabolicELpNormOn d q (parabolicAffine t₀ v₀ r '' s) := by
  have hrpow := pow_ne_zero 2 hr.ne'
  have henorm_ne_zero : ‖r ^ 2‖ₑ ≠ 0 := enorm_ne_zero.mpr hrpow
  have hraw := parabolicELpNormOn_pullback_raw t₀ v₀ hr ((r ^ 2)⁻¹ • q) s
  have hleft :
      (fun z ↦ r ^ 2 * (((r ^ 2)⁻¹ • q) (parabolicAffine t₀ v₀ r z))) =
        pullbackScalar q t₀ v₀ r := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, pullbackScalar_apply]
    rw [← mul_assoc, mul_inv_cancel₀ hrpow, one_mul]
  have hsource :
      parabolicELpNormOn d ((r ^ 2)⁻¹ • q) (parabolicAffine t₀ v₀ r '' s) =
        ‖(r ^ 2)⁻¹‖ₑ *
          parabolicELpNormOn d q (parabolicAffine t₀ v₀ r '' s) := by
    unfold parabolicELpNormOn
    exact eLpNorm_const_smul _ _ _ _
  rw [hleft, hsource, enorm_inv hrpow] at hraw
  calc
    parabolicELpNormOn d (pullbackScalar q t₀ v₀ r) s =
        ‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r *
          (‖r ^ 2‖ₑ⁻¹ *
            parabolicELpNormOn d q (parabolicAffine t₀ v₀ r '' s)) := by
      simpa only [parabolicELpNormPullbackMeasureFactor] using hraw
    _ = (‖r ^ 2‖ₑ * ‖r ^ 2‖ₑ⁻¹) *
          (parabolicELpNormPullbackMeasureFactor d r *
            parabolicELpNormOn d q (parabolicAffine t₀ v₀ r '' s)) := by
      ac_rfl
    _ = parabolicELpNormPullbackMeasureFactor d r *
          parabolicELpNormOn d q (parabolicAffine t₀ v₀ r '' s) := by
      rw [ENNReal.mul_inv_cancel henorm_ne_zero enorm_ne_top, one_mul]

private theorem parabolicELpNormOn_const_mul_pullbackScalar
    {d } (t₀ : ℝ) (v₀ : PDE.Vec d) {r } (hr : 0 < r)
    (a : ℝ) (q : TimeVelocity d → ℝ) (s : Set (TimeVelocity d)) :
    parabolicELpNormOn d
        (fun z ↦ a * q (parabolicAffine t₀ v₀ r z)) s =
      (‖a‖ₑ * parabolicELpNormPullbackMeasureFactor d r) *
        parabolicELpNormOn d q (parabolicAffine t₀ v₀ r '' s) := by
  change eLpNorm (a • pullbackScalar q t₀ v₀ r) (parabolicExponent d)
    (volume.restrict s) = _
  rw [eLpNorm_const_smul]
  change ‖a‖ₑ * parabolicELpNormOn d (pullbackScalar q t₀ v₀ r) s = _
  rw [parabolicELpNormOn_pullbackScalar_unamplified t₀ v₀ hr q s]
  ac_rfl

/-- Restricted ENNReal norm scaling for the unamplified scalar pullback. -/
theorem parabolicELpNormOn_pullbackScalar
    {d } (t₀ : ℝ) (v₀ : PDE.Vec d) {r } (hr : 0 < r)
    (q : TimeVelocity d → ℝ) (s : Set (TimeVelocity d)) :
    parabolicELpNormOn d (pullbackScalar q t₀ v₀ r) s =
      parabolicELpNormPullbackMeasureFactor d r *
        parabolicELpNormOn d q (parabolicAffine t₀ v₀ r '' s) :=
  parabolicELpNormOn_pullbackScalar_unamplified t₀ v₀ hr q s

/-- Restricted ENNReal norm scaling for the time derivative. -/
theorem parabolicELpNormOn_timeDerivative_pullbackScalar
    {d } (t₀ : ℝ) (v₀ : PDE.Vec d) {r } (hr : 0 < r)
    (q : TimeVelocity d → ℝ) (hq : ContDiff ℝ 2 q)
    (s : Set (TimeVelocity d)) :
    parabolicELpNormOn d (timeDerivative (pullbackScalar q t₀ v₀ r)) s =
      (‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r) *
        parabolicELpNormOn d (timeDerivative q)
          (parabolicAffine t₀ v₀ r '' s) := by
  have htime : timeDerivative (pullbackScalar q t₀ v₀ r) =
      fun z ↦ r ^ 2 * timeDerivative q (parabolicAffine t₀ v₀ r z) := by
    funext z
    exact timeDerivative_pullbackScalar
      (q := q) (z := z) (t₀ := t₀) (v₀ := v₀) (r := r) hq.contDiffAt
  rw [htime]
  exact parabolicELpNormOn_const_mul_pullbackScalar t₀ v₀ hr (r ^ 2)
    (timeDerivative q) s

/-- Restricted ENNReal norm scaling for one ordered velocity-Hessian component. -/
theorem parabolicELpNormOn_velocityHessian_pullbackScalar
    {d } (t₀ : ℝ) (v₀ : PDE.Vec d) {r } (hr : 0 < r)
    (q : TimeVelocity d → ℝ) (hq : ContDiff ℝ 2 q)
    (s : Set (TimeVelocity d)) (i j : Fin d) :
    parabolicELpNormOn d
        (fun z ↦ velocityHessian (pullbackScalar q t₀ v₀ r) z i j) s =
      (‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r) *
        parabolicELpNormOn d (fun z ↦ velocityHessian q z i j)
          (parabolicAffine t₀ v₀ r '' s) := by
  have hhessian :
      (fun z ↦ velocityHessian (pullbackScalar q t₀ v₀ r) z i j) =
        fun z ↦ r ^ 2 * velocityHessian q (parabolicAffine t₀ v₀ r z) i j := by
    funext z
    simpa [smul_eq_mul] using (congrFun (congrFun (velocityHessian_pullbackScalar (q := q) (z := z) (t₀ := t₀) (v₀ := v₀) (r := r) hq.contDiffAt) i) j)
  rw [hhessian]
  exact parabolicELpNormOn_const_mul_pullbackScalar t₀ v₀ hr (r ^ 2)
    (fun z ↦ velocityHessian q z i j) s

/-- Finite real extraction of unamplified scalar pullback scaling. -/
theorem parabolicLpNormOn_pullbackScalar_finite
    {d } (t₀ : ℝ) (v₀ : PDE.Vec d) {r } (hr : 0 < r)
    (q : TimeVelocity d → ℝ) (s )
    (hfin : parabolicELpNormOn d q (parabolicAffine t₀ v₀ r '' s) ≠ ⊤) :
    parabolicELpNormOn d (pullbackScalar q t₀ v₀ r) s ≠ ⊤ ∧
      parabolicLpNormOn d (pullbackScalar q t₀ v₀ r) s =
        (parabolicELpNormPullbackMeasureFactor d r).toReal *
          parabolicLpNormOn d q (parabolicAffine t₀ v₀ r '' s) := by
  have hscale := parabolicELpNormOn_pullbackScalar t₀ v₀ hr q s
  constructor
  · rw [hscale]
    exact ENNReal.mul_ne_top (parabolicELpNormPullbackMeasureFactor_ne_top d r) hfin
  · unfold parabolicLpNormOn
    rw [hscale, ENNReal.toReal_mul]

/-- Finite real extraction of time-derivative pullback scaling. -/
theorem parabolicLpNormOn_timeDerivative_pullbackScalar_finite
    {d } (t₀ : ℝ) (v₀ : PDE.Vec d) {r } (hr : 0 < r)
    (q : TimeVelocity d → ℝ) (hq : ContDiff ℝ 2 q)
    (s )
    (hfin : parabolicELpNormOn d (timeDerivative q)
      (parabolicAffine t₀ v₀ r '' s) ≠ ⊤) :
    parabolicELpNormOn d (timeDerivative (pullbackScalar q t₀ v₀ r)) s ≠ ⊤ ∧
      parabolicLpNormOn d (timeDerivative (pullbackScalar q t₀ v₀ r)) s =
        (‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r).toReal *
          parabolicLpNormOn d (timeDerivative q)
            (parabolicAffine t₀ v₀ r '' s) := by
  have hscale := parabolicELpNormOn_timeDerivative_pullbackScalar t₀ v₀ hr q hq s
  constructor
  · rw [hscale]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top enorm_ne_top (parabolicELpNormPullbackMeasureFactor_ne_top d r)) hfin
  · unfold parabolicLpNormOn
    rw [hscale, ENNReal.toReal_mul]

/-- Finite real extraction of ordered velocity-Hessian pullback scaling. -/
theorem parabolicLpNormOn_velocityHessian_pullbackScalar_finite
    {d } (t₀ : ℝ) (v₀ : PDE.Vec d) {r } (hr : 0 < r)
    (q : TimeVelocity d → ℝ) (hq : ContDiff ℝ 2 q)
    (s ) (i j : Fin d)
    (hfin : parabolicELpNormOn d (fun z ↦ velocityHessian q z i j)
      (parabolicAffine t₀ v₀ r '' s) ≠ ⊤) :
    parabolicELpNormOn d
        (fun z ↦ velocityHessian (pullbackScalar q t₀ v₀ r) z i j) s ≠ ⊤ ∧
      parabolicLpNormOn d
        (fun z ↦ velocityHessian (pullbackScalar q t₀ v₀ r) z i j) s =
        (‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r).toReal *
          parabolicLpNormOn d (fun z ↦ velocityHessian q z i j)
            (parabolicAffine t₀ v₀ r '' s) := by
  have hscale := parabolicELpNormOn_velocityHessian_pullbackScalar t₀ v₀ hr q hq s i j
  constructor
  · rw [hscale]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top enorm_ne_top (parabolicELpNormPullbackMeasureFactor_ne_top d r)) hfin
  · unfold parabolicLpNormOn
    rw [hscale, ENNReal.toReal_mul]

end HypoellipticAleksandrov.Parabolic
