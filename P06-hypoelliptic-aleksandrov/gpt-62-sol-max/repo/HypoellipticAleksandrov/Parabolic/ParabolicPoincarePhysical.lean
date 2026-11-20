module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincare
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyScaling
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyProjection
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyReferenceCollarCutoff

/-!
# Physical parabolic Morrey Poincare estimate

This module transports the unit forward-box Poincare inequality to
positive-radius physical forward boxes by parabolic affine scaling.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped BigOperators ENNReal

private theorem parabolicELpNormPullbackMeasureFactor_pos
    (d : Nat) {r : Real} (hr : 0 < r) :
    0 < parabolicELpNormPullbackMeasureFactor d r := by
  unfold parabolicELpNormPullbackMeasureFactor
  apply ENNReal.rpow_pos
  · positivity
  · exact ENNReal.ofReal_ne_top

/-- Scale-normalized smooth parabolic Poincare inequality on every positive-radius
forward physical box, modulo the transported velocity-affine moment projection. -/
theorem exists_parabolicMorreyBoxAffinePoincareConst (d : Nat)
    (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (t₀ : Real) (v₀ : PDE.Vec d) (r : Real), 0 < r ->
      ∀ u : TimeVelocity d -> Real, ContDiff Real 2 u ->
        (r ^ 2)⁻¹ *
          parabolicLpNormOn d
            (fun z => u z -
              parabolicMorreyBoxAffineProjection t₀ v₀ r u z)
            (parabolicBox 1 r t₀ v₀) <=
          C *
            (parabolicLpNormOn d (timeDerivative u)
                (parabolicBox 1 r t₀ v₀) +
              ∑ i : Fin d, ∑ j : Fin d,
                parabolicLpNormOn d
                  (fun z => velocityHessian u z i j)
                  (parabolicBox 1 r t₀ v₀)) := by
  obtain ⟨C, hCpos, hC⟩ := exists_parabolicMorreyUnitAffinePoincareConst d hd
  refine ⟨C, hCpos, ?_⟩
  intro t₀ v₀ r hr u hu
  let uhat : TimeVelocity d -> Real := pullbackScalar u t₀ v₀ r
  let w : TimeVelocity d -> Real := fun z =>
    u z - parabolicMorreyBoxAffineProjection t₀ v₀ r u z
  let what : TimeVelocity d -> Real := fun z =>
    uhat z - parabolicMorreyUnitAffineProjection uhat z
  let factor : ENNReal := parabolicELpNormPullbackMeasureFactor d r
  let F : Real := factor.toReal
  let box : Set (TimeVelocity d) := parabolicBox 1 r t₀ v₀
  have huHat : ContDiff Real 2 uhat := by
    exact hu.comp (contDiff_parabolicAffine t₀ v₀ r)
  have hpullResidual : pullbackScalar w t₀ v₀ r = what := by
    funext z
    simp only [w, what, uhat, pullbackScalar_apply]
    rw [parabolicMorreyBoxAffineProjection_parabolicAffine t₀ v₀ hr]
  have hboxImage : parabolicAffine t₀ v₀ r '' parabolicMorreyUnitBox d = box := by
    exact parabolicAffine_image_parabolicMorreyUnitBox t₀ v₀ hr
  have hF : 0 < F := ENNReal.toReal_pos (parabolicELpNormPullbackMeasureFactor_pos d hr).ne'
    (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)
  have hscale {f g : TimeVelocity d → ℝ} {a : ENNReal}
      (he : parabolicELpNormOn d f (parabolicMorreyUnitBox d) =
        a * parabolicELpNormOn d g (parabolicAffine t₀ v₀ r '' parabolicMorreyUnitBox d)) :
      parabolicLpNormOn d f (parabolicMorreyUnitBox d) = a.toReal * parabolicLpNormOn d g box := by
    rw [parabolicLpNormOn, he, ENNReal.toReal_mul, hboxImage]
    rfl
  have hw := hscale (parabolicELpNormOn_pullbackScalar_unamplified t₀ v₀ hr w _)
  rw [hpullResidual] at hw
  have hf : (‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r).toReal = r ^ 2 * F := by
    rw [ENNReal.toReal_mul, Real.enorm_of_nonneg (sq_nonneg r), ENNReal.toReal_ofReal (sq_nonneg r)]
  have ht := hscale (parabolicELpNormOn_timeDerivative_pullbackScalar t₀ v₀ hr u hu (parabolicMorreyUnitBox d))
  have hh (i j : Fin d) := hscale
    (parabolicELpNormOn_velocityHessian_pullbackScalar t₀ v₀ hr u hu (parabolicMorreyUnitBox d) i j)
  have hunit := hC uhat huHat
  change parabolicLpNormOn d what (parabolicMorreyUnitBox d) ≤ _ at hunit
  change parabolicLpNormOn d (timeDerivative uhat) _ = _ at ht
  have hh' (i j : Fin d) : parabolicLpNormOn d (fun z => velocityHessian uhat z i j)
      (parabolicMorreyUnitBox d) = r ^ 2 * F *
        parabolicLpNormOn d (fun z => velocityHessian u z i j) box := by
    simpa only [hf] using hh i j
  rw [hw, ht, hf] at hunit
  simp_rw [hh', ← Finset.mul_sum, ← mul_add] at hunit
  apply le_of_mul_le_mul_left (a := r ^ 2 * F) ?_ (mul_pos (sq_pos_of_pos hr) hF)
  calc
    _ = F * parabolicLpNormOn d w box := by field_simp; rfl
    _ ≤ _ := hunit
    _ = _ := by ring

end HypoellipticAleksandrov.Parabolic
