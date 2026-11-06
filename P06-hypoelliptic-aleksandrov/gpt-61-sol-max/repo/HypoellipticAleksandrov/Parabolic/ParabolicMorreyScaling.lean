module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm
import Batteries.Tactic.Alias



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

variable (d : ℕ) (r : ℝ)

/-- The inverse-Jacobian `L^(d + 1)` factor of positive parabolic pullback. -/
def parabolicELpNormPullbackMeasureFactor  : ℝ≥0∞ :=
  ENNReal.ofReal ((r ^ (d + 2))⁻¹) ^
    (1 / parabolicExponent d).toReal

private theorem parabolicELpNormPullbackMeasureFactor_ne_top  :
    parabolicELpNormPullbackMeasureFactor d r ≠ ⊤ := by
  simp_all [parabolicELpNormPullbackMeasureFactor]

variable {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d) {r : ℝ} (hr : 0 < r)

include hr in
private theorem parabolicELpNormOn_pullbackScalar_unamplified

    (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (s : HypoellipticAleksandrov.Parabolic.Region d) :
    parabolicELpNormOn d (pullbackScalar q t₀ v₀ r) s =
      parabolicELpNormPullbackMeasureFactor d r *
        parabolicELpNormOn d q (parabolicAffine t₀ v₀ r '' s) := by
  let sharedTerm_31fd5a70dc := (parabolicELpNormOn d q (parabolicAffine t₀ v₀ r '' s))
  have hrpow  := pow_ne_zero 2 hr.ne'

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
          sharedTerm_31fd5a70dc := by
    unfold parabolicELpNormOn
    exact eLpNorm_const_smul _ _ _ _
  rw [hleft, hsource, enorm_inv hrpow] at hraw
  calc
    parabolicELpNormOn d (pullbackScalar q t₀ v₀ r) s =
        ‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r *
          (‖r ^ 2‖ₑ⁻¹ *
            sharedTerm_31fd5a70dc) := hraw
    _ = (‖r ^ 2‖ₑ * ‖r ^ 2‖ₑ⁻¹) *
          (parabolicELpNormPullbackMeasureFactor d r *
            sharedTerm_31fd5a70dc) := by
      ac_rfl
    _ = parabolicELpNormPullbackMeasureFactor d r *
          sharedTerm_31fd5a70dc := by
      rw [ENNReal.mul_inv_cancel (enorm_ne_zero.mpr hrpow) enorm_ne_top, one_mul]

include hr in
private theorem parabolicELpNormOn_const_mul_pullbackScalar

    (a : ℝ) (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (s : HypoellipticAleksandrov.Parabolic.Region d) :
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

variable (q : HypoellipticAleksandrov.Parabolic.ScalarField d)

/-- Restricted ENNReal norm scaling for the unamplified scalar pullback. -/
alias parabolicELpNormOn_pullbackScalar := _root_.HypoellipticAleksandrov.Parabolic.parabolicELpNormOn_pullbackScalar_unamplified


section
variable (hq : ContDiff ℝ 2 q) (s : HypoellipticAleksandrov.Parabolic.Region d)

include hr hq
/-- Restricted ENNReal norm scaling for the time derivative. -/
theorem parabolicELpNormOn_timeDerivative_pullbackScalar

      :
    parabolicELpNormOn d (timeDerivative (pullbackScalar q t₀ v₀ r)) s =
      (‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r) *
        parabolicELpNormOn d (timeDerivative q)
          (parabolicAffine t₀ v₀ r '' s) := by
  have htime : timeDerivative (pullbackScalar q t₀ v₀ r) =
      fun z ↦ r ^ 2 * timeDerivative q (parabolicAffine t₀ v₀ r z) := by
    funext z
    exact timeDerivative_pullbackScalar
           hq.contDiffAt
  rw [htime]
  exact parabolicELpNormOn_const_mul_pullbackScalar t₀ v₀ hr (r ^ 2)
    _ s

/-- Restricted ENNReal norm scaling for one ordered velocity-Hessian component. -/
theorem parabolicELpNormOn_velocityHessian_pullbackScalar

      (i j : Fin d) :
    parabolicELpNormOn d
        (fun z ↦ velocityHessian (pullbackScalar q t₀ v₀ r) z i j) s =
      (‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r) *
        parabolicELpNormOn d (fun z ↦ velocityHessian q z i j)
          (parabolicAffine t₀ v₀ r '' s) := (Eq.mpr
  (id
    (congrArg
      (fun _a =>
        parabolicELpNormOn d _a s =
          ‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r *
            parabolicELpNormOn d (fun z => velocityHessian q z i j) (parabolicAffine t₀ v₀ r '' s))
      (funext fun z => congrFun (congrFun (velocityHessian_pullbackScalar (ContDiff.contDiffAt hq)) i) j)))
  (parabolicELpNormOn_const_mul_pullbackScalar t₀ v₀ hr (r ^ 2) (fun z => velocityHessian q z i j) s))
end


include hr in
/-- Finite real extraction of unamplified scalar pullback scaling. -/
theorem parabolicLpNormOn_pullbackScalar_finite

     (s : HypoellipticAleksandrov.Parabolic.Region d)
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

variable (hq : ContDiff ℝ 2 q) (s : HypoellipticAleksandrov.Parabolic.Region d)

include hr hq
/-- Finite real extraction of time-derivative pullback scaling. -/
theorem parabolicLpNormOn_timeDerivative_pullbackScalar_finite


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

      (i j : Fin d)
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
