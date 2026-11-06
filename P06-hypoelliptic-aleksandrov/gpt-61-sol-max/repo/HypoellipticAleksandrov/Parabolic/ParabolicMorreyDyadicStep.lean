module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincarePhysical
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNestedProjection
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicForwardBox

/-!
# One dyadic parabolic Morrey step

This module combines the physical smooth Poincare estimate with the
nested-projection and open dyadic-forward-box APIs for one parent/child pair.
It deliberately proves neither a chain estimate nor a representative result.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped BigOperators

variable {d : Nat}

variable (t : Real) (v : PDE.Vec d)

private theorem continuous_parabolicMorreyBoxAffineProjection
      (r : Real) (u : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    Continuous (parabolicMorreyBoxAffineProjection t v r u) := by
  unfold parabolicMorreyBoxAffineProjection
  apply Continuous.add continuous_const
  apply continuous_finset_sum
  intro i _
  exact continuous_const.mul ((continuous_apply i).comp continuous_snd |>.sub
    continuous_const)

private theorem smooth_parent_residual_memLp
      {r : Real} (hr : 0 < r)
    (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (hu : ContDiff Real 2 u) :
    MemLp (fun z => u z - parabolicMorreyBoxAffineProjection t v r u z)
      (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t v)) := ((memLp_parabolicNormalizedVolumeOn_parabolicBox_iff t v hr fun z =>
      u z - parabolicMorreyBoxAffineProjection t v r u z).mpr
  (memLp_parabolicNormalizedVolumeOn_of_memLp
    (ENNReal.toReal_pos_iff.mp (volume_parabolicMorreyUnitBox_toReal_pos d)).left
    (Continuous.memLp_parabolicMorreyUnitBox
      (Continuous.comp (Continuous.sub (ContDiff.continuous hu) (continuous_parabolicMorreyBoxAffineProjection t v r u))
        (ContDiff.continuous (contDiff_parabolicAffine t v r))))))

private theorem dyadic_parent_normalization_factor
     {r : Real} (hr : 0 < r) :
    ((2 : Real) ^ d * r ^ (d + 2))⁻¹ ^ (1 / ((d : Real) + 1)) * r ^ 2 =
      (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
        r ^ parabolicMorreyExponent d := by
  have htwo : (0 : Real) < 2 := by norm_num
  have hdenom : (d : Real) + 1 ≠ 0 := by positivity
  rw [Real.inv_rpow (mul_nonneg (pow_nonneg htwo.le _) (pow_nonneg hr.le _)),
    Real.mul_rpow (pow_nonneg htwo.le _) (pow_nonneg hr.le _), mul_inv_rev,
    ← Real.rpow_natCast 2 d, ← Real.rpow_natCast r (d + 2),
    ← Real.rpow_mul hr.le, ← Real.rpow_mul htwo.le,
    ← Real.rpow_neg hr.le, ← Real.rpow_neg htwo.le,
    ← Real.rpow_natCast r 2]
  rw [show (r ^ (-(↑(d + 2) * (1 / ((d : Real) + 1)))) *
      2 ^ (-(↑d * (1 / ((d : Real) + 1))))) * r ^ ((2 : Nat) : Real) =
      2 ^ (-(↑d * (1 / ((d : Real) + 1)))) *
        (r ^ (-(↑(d + 2) * (1 / ((d : Real) + 1)))) *
          r ^ ((2 : Nat) : Real)) by ring,
    ← Real.rpow_add hr]
  unfold parabolicMorreyExponent
  congr 1
  · field_simp [hdenom]
  · congr 1
    push_cast
    field_simp [hdenom]
    ring

private theorem smooth_parent_residual_mean_bound
     (C : Real) (t : Real) (v : PDE.Vec d) {r : Real} (hr : 0 < r)
    (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (_hu : ContDiff Real 2 u)
    (hP : (r ^ 2)⁻¹ *
      parabolicLpNormOn d
        (fun z => u z - parabolicMorreyBoxAffineProjection t v r u z)
        (parabolicBox 1 r t v) <=
      C * (parabolicLpNormOn d (timeDerivative u) (parabolicBox 1 r t v) +
        ∑ i : Fin d, ∑ j : Fin d,
          parabolicLpNormOn d (fun z => velocityHessian u z i j)
            (parabolicBox 1 r t v)))
    (hres : MemLp (fun z => u z - parabolicMorreyBoxAffineProjection t v r u z)
      (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t v))) :
    parabolicLpMeanNormOn d
        (fun z => u z - parabolicMorreyBoxAffineProjection t v r u z)
        _ hres <=
      C * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
        r ^ parabolicMorreyExponent d *
        (parabolicLpNormOn d (timeDerivative u) (parabolicBox 1 r t v) +
          ∑ i : Fin d, ∑ j : Fin d,
            parabolicLpNormOn d (fun z => velocityHessian u z i j)
              (parabolicBox 1 r t v)) := by
  let sharedTerm_e10724eba2 := (((2 : Real) ^ d * r ^ (d + 2))⁻¹ ^ (1 / ((d : Real) + 1)))
  let f  := fun z =>
    u z - parabolicMorreyBoxAffineProjection t v r u z
  let Q  := parabolicBox 1 r t v
  let A : Real := parabolicLpNormOn d (timeDerivative u) Q +
    ∑ i : Fin d, ∑ j : Fin d,
      parabolicLpNormOn d (fun z => velocityHessian u z i j) Q
  have hraw := memLp_restrict_of_memLp_parabolicNormalizedVolumeOn
    (volume_parabolicMorreyBox_pos t v hr)
    (volume_parabolicMorreyBox_lt_top t v hr) hres

  change parabolicLpMeanNormOn d f Q hres <=
    C * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
      r ^ parabolicMorreyExponent d * A
  rw [parabolicLpMeanNormOn_eq_volume_toReal_inv_rpow_mul_parabolicLpNormOn
    (volume_parabolicMorreyBox_pos t v hr)
    (volume_parabolicMorreyBox_lt_top t v hr) f hraw hres,
    volume_parabolicMorreyBox_toReal t v hr]
  refine (mul_le_mul_of_nonneg_left ((by
      calc
        parabolicLpNormOn d f Q = r ^ 2 * ((r ^ 2)⁻¹ * parabolicLpNormOn d f Q) := by
          field_simp [hr.ne']
        _ <= r ^ 2 * (C * A) := mul_le_mul_of_nonneg_left (hP) (sq_nonneg r)))
    (Real.rpow_nonneg (inv_nonneg.mpr
      (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hr.le _))) _)).trans_eq ?_
  have hp : (1 / parabolicExponent d).toReal = 1 / ((d : Real) + 1) := by
    unfold parabolicExponent
    have hcast : (d : ENNReal) + 1 = ((d + 1 : Nat) : ENNReal) := by norm_num
    rw [hcast, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
    norm_num
  rw [hp]
  change sharedTerm_e10724eba2 *
      (r ^ 2 * (C * A)) = _
  rw [show sharedTerm_e10724eba2 *
      (r ^ 2 * (C * A)) =
      (sharedTerm_e10724eba2 * r ^ 2) *
        C * A by ring,
    dyadic_parent_normalization_factor hr]
  ring

private theorem dyadic_step_factor
     {r C_P : Real} (hr : 0 < r) :
    (1 + 3 * (d : Real)) *
        (r / (r / 2)) ^ (((d : Real) + 2) / ((d : Real) + 1)) *
        (C_P * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
          r ^ parabolicMorreyExponent d) =
      ((1 + 3 * (d : Real)) * (2 : Real) ^ (2 / ((d : Real) + 1)) * C_P) *
        r ^ parabolicMorreyExponent d := by

  have hdenom : (d : Real) + 1 ≠ 0 := by positivity
  have hratio : r / (r / 2) = 2 := by field_simp [hr.ne']
  rw [hratio]
  have hexp : ((d : Real) + 2) / ((d : Real) + 1) +
      (-(d : Real) / ((d : Real) + 1)) = 2 / ((d : Real) + 1) := by
    field_simp [hdenom]
    ring
  have hpow : (2 : Real) ^ (((d : Real) + 2) / ((d : Real) + 1)) *
      2 ^ (-(d : Real) / ((d : Real) + 1)) =
      2 ^ (((d : Real) + 2) / ((d : Real) + 1) +
        (-(d : Real) / ((d : Real) + 1))) := by
    rw [← Real.rpow_add (by norm_num)]
  rw [hexp] at hpow
  calc
    (1 + 3 * (d : Real)) * 2 ^ (((d : Real) + 2) / ((d : Real) + 1)) *
        (C_P * 2 ^ (-(d : Real) / ((d : Real) + 1)) *
          r ^ parabolicMorreyExponent d) =
      (1 + 3 * (d : Real)) *
        (2 ^ (((d : Real) + 2) / ((d : Real) + 1)) *
          2 ^ (-(d : Real) / ((d : Real) + 1))) * C_P *
          r ^ parabolicMorreyExponent d := by ring
    _ = _ := by rw [hpow]

section
variable {d n : Nat} (C_P : Real) (hC_P : ∀ (t : Real) (v : PDE.Vec d) (r : Real), 0 < r -> ∀ u : HypoellipticAleksandrov.Parabolic.ScalarField d, ContDiff Real 2 u -> (r ^ 2)⁻¹ * parabolicLpNormOn d (fun z => u z - parabolicMorreyBoxAffineProjection t v r u z) (parabolicBox 1 r t v) <= C_P * (parabolicLpNormOn d (timeDerivative u) (parabolicBox 1 r t v) + ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d (fun z => velocityHessian u z i j) (parabolicBox 1 r t v))) (index : ParabolicDyadicIndex d n) (child : ParabolicDyadicChild d) (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (hu : ContDiff Real 2 u)

include hC_P hu
private theorem dyadic_child_affine_bound
     :
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
  let sharedTerm_57aa0634fb := ((((d : Real) + 2) / ((d : Real) + 1)))
  let sharedTerm_e3886d30bd := (C_P * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)))
  let sharedTerm_2f053a7f91 := (1 + 3 * (d : Real))
  let qP := parabolicDyadicSourceBox index
  let qC := parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)
  let QP  := parabolicBox 1 qP.radius qP.baseTime qP.center

  let R : Real := parabolicLpNormOn d (timeDerivative u) QP +
    ∑ i : Fin d, ∑ j : Fin d,
      parabolicLpNormOn d (fun z => velocityHessian u z i j) QP
  have hqP  := parabolicDyadicSourceBox_radius_pos index
  have hqC  := parabolicDyadicSourceBox_radius_pos
    (parabolicDyadicChildIndex index child)


  have hres := smooth_parent_residual_memLp qP.baseTime qP.center hqP u hu
  have hmean := smooth_parent_residual_mean_bound C_P qP.baseTime qP.center hqP u hu
    (hC_P qP.baseTime qP.center qP.radius hqP u hu) hres
  have hnested := parabolicMorreyNestedProjection_discrepancy_le_largeResidual
    qP.baseTime qP.center hqP qC.baseTime qC.center hqC (parabolicDyadicForwardBox_child_subset index child) u hres
  change _ <= ((sharedTerm_2f053a7f91) * (2 : Real) ^ (2 / ((d : Real) + 1)) * C_P) *
    qP.radius ^ parabolicMorreyExponent d * R
  calc
    _ <= (sharedTerm_2f053a7f91) *
        (qP.radius / qC.radius) ^ sharedTerm_57aa0634fb *
        parabolicLpMeanNormOn d
          (fun z => u z - parabolicMorreyBoxAffineProjection
            qP.baseTime qP.center qP.radius u z) QP hres := hnested
    _ <= (sharedTerm_2f053a7f91) *
        (qP.radius / qC.radius) ^ sharedTerm_57aa0634fb *
        (sharedTerm_e3886d30bd *
          qP.radius ^ parabolicMorreyExponent d * R) := by
      gcongr
    _ = _ := by
      rw [(parabolicDyadicSourceBox_radius_childIndex index child)]
      calc
        (sharedTerm_2f053a7f91) *
            (qP.radius / (qP.radius / 2)) ^ sharedTerm_57aa0634fb *
            (sharedTerm_e3886d30bd *
              qP.radius ^ parabolicMorreyExponent d * R) =
          ((sharedTerm_2f053a7f91) *
            (qP.radius / (qP.radius / 2)) ^ sharedTerm_57aa0634fb *
            (sharedTerm_e3886d30bd *
              qP.radius ^ parabolicMorreyExponent d)) * R := by ring
        _ = _ := by rw [dyadic_step_factor hqP]

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
  let sharedTerm_8544ec28a5 := ((((d : Real) + 2) / ((d : Real) + 1)))
  let sharedTerm_449be77bae := (C_P * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)))
  let sharedTerm_244ced5ce9 := (1 + 3 * (d : Real))
  let qP := parabolicDyadicSourceBox index
  let qC := parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)
  let QP  := parabolicBox 1 qP.radius qP.baseTime qP.center

  let R : Real := parabolicLpNormOn d (timeDerivative u) QP +
    ∑ i : Fin d, ∑ j : Fin d,
      parabolicLpNormOn d (fun w => velocityHessian u w i j) QP
  have hqP  := parabolicDyadicSourceBox_radius_pos index
  have hqC  := parabolicDyadicSourceBox_radius_pos
    (parabolicDyadicChildIndex index child)


  have hres := smooth_parent_residual_memLp qP.baseTime qP.center hqP u hu
  have hmean := smooth_parent_residual_mean_bound C_P qP.baseTime qP.center hqP u hu
    (hC_P qP.baseTime qP.center qP.radius hqP u hu) hres
  have hnested := parabolicMorreyNestedProjection_abs_sub_le_largeResidual
    qP.baseTime qP.center hqP qC.baseTime qC.center hqC (parabolicDyadicForwardBox_child_subset index child) u z (hz) hres
  change _ <= ((sharedTerm_244ced5ce9) * (2 : Real) ^ (2 / ((d : Real) + 1)) * C_P) *
    qP.radius ^ parabolicMorreyExponent d * R
  calc
    _ <= (sharedTerm_244ced5ce9) *
        (qP.radius / qC.radius) ^ sharedTerm_8544ec28a5 *
        parabolicLpMeanNormOn d
          (fun w => u w - parabolicMorreyBoxAffineProjection
            qP.baseTime qP.center qP.radius u w) QP hres := hnested
    _ <= (sharedTerm_244ced5ce9) *
        (qP.radius / qC.radius) ^ sharedTerm_8544ec28a5 *
        (sharedTerm_449be77bae *
          qP.radius ^ parabolicMorreyExponent d * R) := by
      gcongr
    _ = _ := by
      rw [(parabolicDyadicSourceBox_radius_childIndex index child)]
      calc
        (sharedTerm_244ced5ce9) *
            (qP.radius / (qP.radius / 2)) ^ sharedTerm_8544ec28a5 *
            (sharedTerm_449be77bae *
              qP.radius ^ parabolicMorreyExponent d * R) =
          ((sharedTerm_244ced5ce9) *
            (qP.radius / (qP.radius / 2)) ^ sharedTerm_8544ec28a5 *
            (sharedTerm_449be77bae *
              qP.radius ^ parabolicMorreyExponent d)) * R := by ring
        _ = _ := by rw [dyadic_step_factor hqP]
end


variable (d : Nat) (hd : 1 <= d)

include hd
/-- One dyadic child/parent moment-jet discrepancy for an actual smooth
function, with a dimension-only constant. -/
theorem exists_parabolicMorreyDyadicChildAffineJetConst  :
    ∃ C : Real, 0 < C ∧
      ∀ (n : Nat) (index : ParabolicDyadicIndex d n)
        (child : ParabolicDyadicChild d) (u : HypoellipticAleksandrov.Parabolic.ScalarField d),
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
theorem exists_parabolicMorreyDyadicChildProjectionConst  :
    ∃ C : Real, 0 < C ∧
      ∀ (n : Nat) (index : ParabolicDyadicIndex d n)
        (child : ParabolicDyadicChild d) (u : HypoellipticAleksandrov.Parabolic.ScalarField d),
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

end HypoellipticAleksandrov.Parabolic
