module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxResidualMean
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNestedProjection
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicForwardBox

/-!
# One dyadic parabolic Morrey step

This module combines the physical smooth Poincare estimate with the
nested-projection and open dyadic-forward-box APIs for one parent/child pair.
It deliberately proves neither a chain estimate nor a representative result.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped BigOperators ENNReal

private theorem dyadic_step_factor
    {d : Nat} {r C_P : Real} (hr : 0 < r) (R : Real) :
    (1 + 3 * (d : Real)) *
        (r / (r / 2)) ^ (((d : Real) + 2) / ((d : Real) + 1)) *
        (C_P * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
          r ^ parabolicMorreyExponent d * R) =
      ((1 + 3 * (d : Real)) * (2 : Real) ^ (2 / ((d : Real) + 1)) * C_P) *
        r ^ parabolicMorreyExponent d * R := by
  have hratio : r / (r / 2) = 2 := by field_simp [hr.ne']
  have hexp : ((d : Real) + 2) / ((d : Real) + 1) +
      (-(d : Real) / ((d : Real) + 1)) = 2 / ((d : Real) + 1) := by ring
  have hpow := Real.rpow_add (by norm_num : (0 : ℝ) < 2)
    (((d : Real) + 2) / ((d : Real) + 1)) (-(d : Real) / ((d : Real) + 1))
  rw [hexp] at hpow
  rw [hratio, hpow]
  ring

section
variable {d n : Nat} (C_P : Real)
  (hC_P : ∀ (t : Real) (v : PDE.Vec d) (r : Real), 0 < r -> ∀ u : TimeVelocity d -> Real, ContDiff Real 2 u -> (r ^ 2)⁻¹ * parabolicLpNormOn d (fun z => u z - parabolicMorreyBoxAffineProjection t v r u z) (parabolicBox 1 r t v) <= C_P * (parabolicLpNormOn d (timeDerivative u) (parabolicBox 1 r t v) + ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d (fun z => velocityHessian u z i j) (parabolicBox 1 r t v)))
  (index : ParabolicDyadicIndex d n) (child : ParabolicDyadicChild d) (u : TimeVelocity d -> Real)
  (hu : ContDiff Real 2 u)
include hC_P hu

private theorem dyadic_child_affine_bound :
    |parabolicMorreyBoxAverage
        (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).baseTime
        (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).center
        (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius u -
      parabolicMorreyBoxAffineProjection
        (parabolicDyadicSourceBox index).baseTime
        (parabolicDyadicSourceBox index).center
        (parabolicDyadicSourceBox index).radius u
        ((parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).baseTime,
         (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).center)| +
      (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius *
        ∑ i : Fin d,
          |parabolicMorreyBoxVelocitySlope
              (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).baseTime
              (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).center
              (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius u i -
            parabolicMorreyBoxVelocitySlope
              (parabolicDyadicSourceBox index).baseTime
              (parabolicDyadicSourceBox index).center
              (parabolicDyadicSourceBox index).radius u i| <=
      ((1 + 3 * (d : Real)) * (2 : Real) ^ (2 / ((d : Real) + 1)) * C_P) *
        (parabolicDyadicSourceBox index).radius ^ parabolicMorreyExponent d *
        (parabolicLpNormOn d (timeDerivative u) (parabolicBox 1
            (parabolicDyadicSourceBox index).radius
            (parabolicDyadicSourceBox index).baseTime
            (parabolicDyadicSourceBox index).center) +
          ∑ i : Fin d, ∑ j : Fin d,
            parabolicLpNormOn d (fun z => velocityHessian u z i j)
              (parabolicBox 1 (parabolicDyadicSourceBox index).radius
                (parabolicDyadicSourceBox index).baseTime
                (parabolicDyadicSourceBox index).center)) := by
  let qP := parabolicDyadicSourceBox index
  let qC := parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)
  let QP : Set (TimeVelocity d) := parabolicBox 1 qP.radius qP.baseTime qP.center
  let QC : Set (TimeVelocity d) := parabolicBox 1 qC.radius qC.baseTime qC.center
  let R : Real := parabolicLpNormOn d (timeDerivative u) QP +
    ∑ i : Fin d, ∑ j : Fin d,
      parabolicLpNormOn d (fun z => velocityHessian u z i j) QP
  have hqP : 0 < qP.radius := parabolicDyadicSourceBox_radius_pos index
  have hqC : 0 < qC.radius := parabolicDyadicSourceBox_radius_pos
    (parabolicDyadicChildIndex index child)
  have hsub : QC ⊆ QP := parabolicDyadicForwardBox_child_subset index child
  have hhalf : qC.radius = qP.radius / 2 :=
    parabolicDyadicSourceBox_radius_childIndex index child
  have hres := parabolicMorreyBoxAffineResidual_memLp qP.baseTime qP.center hqP u hu
  have hmean := parabolicMorreyBoxAffineResidual_mean_bound C_P qP.baseTime qP.center hqP u
    (hC_P qP.baseTime qP.center qP.radius hqP u hu) hres
  have hnested := parabolicMorreyNestedProjection_discrepancy_le_largeResidual
    qP.baseTime qP.center hqP qC.baseTime qC.center hqC hsub u hres
  have h := mul_le_mul_of_nonneg_left hmean (by positivity : 0 ≤
    (1 + 3 * (d : Real)) * (qP.radius / qC.radius) ^ (((d : Real) + 2) / ((d : Real) + 1)))
  refine hnested.trans (h.trans_eq ?_)
  rw [hhalf]
  exact dyadic_step_factor hqP R

private theorem dyadic_child_projection_bound
    (z : TimeVelocity d)
    (hz : z ∈ parabolicBox 1
      (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius
      (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).baseTime
      (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).center) :
    |parabolicMorreyBoxAffineProjection
        (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).baseTime
        (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).center
        (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius u z -
      parabolicMorreyBoxAffineProjection
        (parabolicDyadicSourceBox index).baseTime
        (parabolicDyadicSourceBox index).center
        (parabolicDyadicSourceBox index).radius u z| <=
      ((1 + 3 * (d : Real)) * (2 : Real) ^ (2 / ((d : Real) + 1)) * C_P) *
        (parabolicDyadicSourceBox index).radius ^ parabolicMorreyExponent d *
        (parabolicLpNormOn d (timeDerivative u) (parabolicBox 1
            (parabolicDyadicSourceBox index).radius
            (parabolicDyadicSourceBox index).baseTime
            (parabolicDyadicSourceBox index).center) +
          ∑ i : Fin d, ∑ j : Fin d,
            parabolicLpNormOn d (fun w => velocityHessian u w i j)
              (parabolicBox 1 (parabolicDyadicSourceBox index).radius
                (parabolicDyadicSourceBox index).baseTime
                (parabolicDyadicSourceBox index).center)) := by
  let qP := parabolicDyadicSourceBox index
  let qC := parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)
  let QP : Set (TimeVelocity d) := parabolicBox 1 qP.radius qP.baseTime qP.center
  let QC : Set (TimeVelocity d) := parabolicBox 1 qC.radius qC.baseTime qC.center
  let R : Real := parabolicLpNormOn d (timeDerivative u) QP +
    ∑ i : Fin d, ∑ j : Fin d,
      parabolicLpNormOn d (fun w => velocityHessian u w i j) QP
  have hqP : 0 < qP.radius := parabolicDyadicSourceBox_radius_pos index
  have hqC : 0 < qC.radius := parabolicDyadicSourceBox_radius_pos
    (parabolicDyadicChildIndex index child)
  have hsub : QC ⊆ QP := parabolicDyadicForwardBox_child_subset index child
  have hhalf : qC.radius = qP.radius / 2 :=
    parabolicDyadicSourceBox_radius_childIndex index child
  have hres := parabolicMorreyBoxAffineResidual_memLp qP.baseTime qP.center hqP u hu
  have hmean := parabolicMorreyBoxAffineResidual_mean_bound C_P qP.baseTime qP.center hqP u
    (hC_P qP.baseTime qP.center qP.radius hqP u hu) hres
  have hnested := parabolicMorreyNestedProjection_abs_sub_le_largeResidual
    qP.baseTime qP.center hqP qC.baseTime qC.center hqC hsub u z (by
      simpa only [qC] using hz) hres
  have h := mul_le_mul_of_nonneg_left hmean (by positivity : 0 ≤
    (1 + 3 * (d : Real)) * (qP.radius / qC.radius) ^ (((d : Real) + 2) / ((d : Real) + 1)))
  refine hnested.trans (h.trans_eq ?_)
  rw [hhalf]
  exact dyadic_step_factor hqP R

end

section
variable (d : Nat) (hd : 1 <= d)
include hd

/-- One dyadic child/parent moment-jet discrepancy for an actual smooth
function, with a dimension-only constant. -/
theorem exists_parabolicMorreyDyadicChildAffineJetConst :
    ∃ C : Real, 0 < C ∧
      ∀ (n : Nat) (index : ParabolicDyadicIndex d n)
        (child : ParabolicDyadicChild d) (u : TimeVelocity d -> Real),
        ContDiff Real 2 u ->
        |parabolicMorreyBoxAverage
            (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).baseTime
            (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).center
            (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius u -
          parabolicMorreyBoxAffineProjection
            (parabolicDyadicSourceBox index).baseTime
            (parabolicDyadicSourceBox index).center
            (parabolicDyadicSourceBox index).radius u
            ((parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).baseTime,
             (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).center)| +
          (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius *
            ∑ i : Fin d,
              |parabolicMorreyBoxVelocitySlope
                  (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).baseTime
                  (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).center
                  (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius u i -
                parabolicMorreyBoxVelocitySlope
                  (parabolicDyadicSourceBox index).baseTime
                  (parabolicDyadicSourceBox index).center
                  (parabolicDyadicSourceBox index).radius u i| <=
          C * (parabolicDyadicSourceBox index).radius ^ parabolicMorreyExponent d *
            (parabolicLpNormOn d (timeDerivative u) (parabolicBox 1
                (parabolicDyadicSourceBox index).radius
                (parabolicDyadicSourceBox index).baseTime
                (parabolicDyadicSourceBox index).center) +
              ∑ i : Fin d, ∑ j : Fin d,
                parabolicLpNormOn d (fun z => velocityHessian u z i j)
                  (parabolicBox 1 (parabolicDyadicSourceBox index).radius
                    (parabolicDyadicSourceBox index).baseTime
                    (parabolicDyadicSourceBox index).center)) := by
  obtain ⟨C_P, hC_P_pos, hC_P⟩ := exists_parabolicMorreyBoxAffinePoincareConst d hd
  refine ⟨(1 + 3 * (d : Real)) * (2 : Real) ^ (2 / ((d : Real) + 1)) * C_P,
    by positivity, ?_⟩
  intro n index child u hu
  exact dyadic_child_affine_bound C_P hC_P index child u hu

/-- Pointwise-on-the-open-child-box form of the one-step projection estimate. -/
theorem exists_parabolicMorreyDyadicChildProjectionConst :
    ∃ C : Real, 0 < C ∧
      ∀ (n : Nat) (index : ParabolicDyadicIndex d n)
        (child : ParabolicDyadicChild d) (u : TimeVelocity d -> Real),
        ContDiff Real 2 u ->
        ∀ z : TimeVelocity d,
          z ∈ parabolicBox 1
              (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius
              (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).baseTime
              (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).center ->
          |parabolicMorreyBoxAffineProjection
              (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).baseTime
              (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).center
              (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius u z -
            parabolicMorreyBoxAffineProjection
              (parabolicDyadicSourceBox index).baseTime
              (parabolicDyadicSourceBox index).center
              (parabolicDyadicSourceBox index).radius u z| <=
            C * (parabolicDyadicSourceBox index).radius ^ parabolicMorreyExponent d *
              (parabolicLpNormOn d (timeDerivative u) (parabolicBox 1
                  (parabolicDyadicSourceBox index).radius
                  (parabolicDyadicSourceBox index).baseTime
                  (parabolicDyadicSourceBox index).center) +
                ∑ i : Fin d, ∑ j : Fin d,
                  parabolicLpNormOn d (fun w => velocityHessian u w i j)
                    (parabolicBox 1 (parabolicDyadicSourceBox index).radius
                      (parabolicDyadicSourceBox index).baseTime
                      (parabolicDyadicSourceBox index).center)) := by
  obtain ⟨C_P, hC_P_pos, hC_P⟩ := exists_parabolicMorreyBoxAffinePoincareConst d hd
  refine ⟨(1 + 3 * (d : Real)) * (2 : Real) ^ (2 / ((d : Real) + 1)) * C_P,
    by positivity, ?_⟩
  intro n index child u hu z hz
  exact dyadic_child_projection_bound C_P hC_P index child u hu z hz

end

end HypoellipticAleksandrov.Parabolic
