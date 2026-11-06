module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientL2Transpose
public import HypoellipticAleksandrov.Parabolic.SpatialSegmentSafeOpen
public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochnerContinuous
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder





/-!
# Weak derivatives paired with signed spatial difference quotients

This module identifies the pairing of a signed spatial difference quotient
with a smooth compactly supported test as the average of pairings with the
selected weak velocity derivative.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

variable (k : Fin d)

private theorem spatialShift_segment_formula
      (h t : ℝ) (z : TimeVelocity d) :
    spatialShift k (t * h) z =
      z + t • (spatialShift k h z - z) := by
  rcases z with ⟨r, y⟩
  simp only [spatialShift_apply, Prod.mk_add_mk, add_zero, Prod.mk_sub_mk,
    sub_self, Prod.smul_mk, smul_zero, Prod.mk.injEq, true_and]
  module

private theorem backward_spatialDifferenceQuotient_eq_intervalIntegral
      (h : ℝ) (hh : h ≠ 0)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (z : TimeVelocity d) :
    spatialDifferenceQuotient k (-h) φ z =
      ∫ t in (0 )..1,
        velocityGradient φ (spatialShift k (-(t * h)) z) k := by
  let F  := fun t => φ (spatialShift k (-(t * h)) z)
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by simp)

  have hFderiv : ∀ t : ℝ,
      deriv F t = -h * velocityGradient φ (spatialShift k (-(t * h)) z) k := by
    intro t

    rw [show deriv F t = (fderiv ℝ φ (spatialShift k (-(t * h)) z))
        ((0, -h • PDE.basisVec k) ) from ((hφdiff _).hasFDerivAt.comp_hasDerivAt t (by
            convert (((hasDerivAt_id t).mul_const h).neg.smul_const
              ((0, PDE.basisVec k) : TimeVelocity d)).const_add z using 1 <;>
              simp [spatialShift])).deriv]
    change (fderiv ℝ φ (spatialShift k (-(t * h)) z))
        ((0, -h • PDE.basisVec k) ) = _
    rw [show ((0, -h • PDE.basisVec k) : TimeVelocity d) =
        -h • ((0, PDE.basisVec k) : TimeVelocity d) by simp]
    rw [map_smul]
    rfl


  have hFTC := intervalIntegral.integral_deriv_eq_sub
       (fun t _ => (show Differentiable ℝ F by

           exact hφdiff.fun_comp (by
               dsimp only [spatialShift]
               fun_prop)) t)
    (show IntervalIntegrable (deriv F) volume 0 1 by
        rw [show deriv F = fun t =>
            -h * velocityGradient φ (spatialShift k (-(t * h)) z) k by
          funext t
          exact hFderiv t]
        exact (continuous_const.mul (by
            unfold velocityGradient
            apply ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).comp
            dsimp only [spatialShift]
            fun_prop)).intervalIntegrable 0 1)
  rw [show (∫ t in (0 )..1, deriv F t) =
      -h * ∫ t in (0 )..1,
        velocityGradient φ (spatialShift k (-(t * h)) z) k by
    simp_rw [hFderiv, intervalIntegral.integral_const_mul]]
    at hFTC
  simp only [F, one_mul, neg_mul, zero_mul, neg_zero,
    spatialShift_zero, id_eq] at hFTC
  rw [spatialDifferenceQuotient_apply, spatialTranslate_apply]
  apply (div_eq_iff (neg_ne_zero.mpr hh)).2
  linarith

variable (U : HypoellipticAleksandrov.Parabolic.Region d) (k : Fin d)

private theorem translated_test_tsupport_subset
      (h t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (φ : TimeVelocity d → ℝ)
    (hφsafe : tsupport φ ⊆ spatialSegmentSafeSet U k h) :
    tsupport (fun z => φ (spatialShift k (-(t * h)) z)) ⊆ U := by
  intro z hz

  have hsafe := hφsafe (by
      change z ∈ tsupport (spatialTranslate k (-(t * h)) φ) at hz
      rwa [mem_tsupport_spatialTranslate_iff] at hz)
  rw [mem_spatialSegmentSafeSet_iff,
    segment_eq_image' ℝ (spatialShift k (-(t * h)) z)
      (spatialShift k h (spatialShift k (-(t * h)) z))] at hsafe
  apply hsafe
  refine ⟨t, ht, ?_⟩
  change spatialShift k (-(t * h)) z +
      t • (spatialShift k h (spatialShift k (-(t * h)) z) -
        spatialShift k (-(t * h)) z) = z
  rw [← spatialShift_segment_formula]
  change (spatialShift k (t * h) ∘ spatialShift k (-(t * h))) z = z
  rw [spatialShift_comp]
  simp

private theorem integrable_joint_shifted_mul
      (h : ℝ)
    (u φ : TimeVelocity d → ℝ)
    (hu : ParabolicMemLpOn U (2 ) u)
    (hφ : ContDiff ℝ PDE.smoothOrder φ) (hφcompact : HasCompactSupport φ) :
    Integrable (Function.uncurry fun t z =>
      u z * velocityGradient φ (spatialShift k (-(t * h)) z) k)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod
        (volume.restrict U )) := by
  let sharedTerm_81540a5446 := ((fun p : ℝ × TimeVelocity d => velocityGradient φ (spatialShift k (-(p.1 * h)) p.2) k))
  let μt  := volume.restrict (Ioc (0 : ℝ) 1)
  let μU  := volume.restrict U
  let shear : ℝ × TimeVelocity d → ℝ × TimeVelocity d :=
    fun p => (p.1, spatialShift k (-(p.1 * h)) p.2)


  have hgradProd  := (show MemLp (fun z  => velocityGradient φ z k)
      (2 ) by
      exact ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hφcompact.fderiv_apply ℝ _)).comp_snd μt

  have hprodRestrict : μt.prod μU =
      (μt.prod (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)).restrict (univ ×ˢ U) := by
    calc
      μt.prod μU = (μt.restrict univ).prod
          ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict U) := by simp [μU]
      _ = (μt.prod (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)).restrict (univ ×ˢ U) :=
        Measure.prod_restrict univ U


  simpa only [μt, μU, Function.uncurry_def, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Pi.mul_def] using
    (hu.comp_snd μt).integrable_mul (by
        rw [hprodRestrict]
        exact (show MemLp sharedTerm_81540a5446
      (2 ) (μt.prod (volume )) by
            simpa only [shear, Function.comp_def] using hgradProd.comp_measurePreserving (show MeasurePreserving shear
      (μt.prod (volume ))
      (μt.prod (volume )) by
                refine MeasurePreserving.skew_product (g := fun t z => spatialShift k (-(t * h)) z)
                  (MeasurePreserving.id _) ?_ ?_
                · dsimp [spatialShift]
                  fun_prop
                · filter_upwards [] with t
                  exact (spatialShift_measurePreserving k (-(t * h))).map_eq)).mono_measure Measure.restrict_le_self)




variable {d : ℕ} (U : HypoellipticAleksandrov.Parabolic.Region d) (k : Fin d) (h : ℝ)

private theorem integrable_joint_shifted_test_mul

    (g φ : TimeVelocity d → ℝ)
    (hg : ParabolicMemLpOn U (2 ) g)
    (hφmem : MemLp φ (2 ) ) :
    Integrable (Function.uncurry fun t z =>
      g z * φ (spatialShift k (-(t * h)) z))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod
        (volume.restrict U )) := by
  let sharedTerm_9104ca8572 := ((fun p : ℝ × TimeVelocity d => φ (spatialShift k (-(p.1 * h)) p.2)))
  let μt  := volume.restrict (Ioc (0 : ℝ) 1)
  let shear : ℝ × TimeVelocity d → ℝ × TimeVelocity d :=
    fun p => (p.1, spatialShift k (-(p.1 * h)) p.2)


  have hprod : μt.prod (volume.restrict U ) =
      (μt.prod volume).restrict (univ ×ˢ U) := by
    calc
      μt.prod (volume.restrict U ) =
          (μt.restrict univ).prod (volume.restrict U) := by simp
      _ = (μt.prod volume).restrict (univ ×ˢ U) := Measure.prod_restrict univ U


  simpa only [μt, Function.uncurry_def, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Pi.mul_def,
    timeVelocityVolumeOn] using (hg.comp_snd μt).integrable_mul (by
        rw [hprod]
        exact (show MemLp sharedTerm_9104ca8572 (2 ) (μt.prod volume) by
            simpa only [shear, Function.comp_def] using (hφmem.comp_snd μt).comp_measurePreserving (show MeasurePreserving shear (μt.prod volume) (μt.prod volume) by
                refine MeasurePreserving.skew_product (g := fun t z => spatialShift k (-(t * h)) z)
                  (MeasurePreserving.id _) ?_ ?_
                · dsimp [spatialShift]
                  fun_prop
                · filter_upwards [] with t
                  exact (spatialShift_measurePreserving k (-(t * h))).map_eq)).mono_measure Measure.restrict_le_self)

variable (u g φ : TimeVelocity d → ℝ) (hh : h ≠ 0) (hu : ParabolicMemLpOn U (2 ) u) (hg : ParabolicMemLpOn U (2 ) g) (hweak : HasWeakVelocityPartialDerivOn U k u g) (hφ : ContDiff ℝ PDE.smoothOrder φ) (hφcompact : HasCompactSupport φ) (hφsafe : tsupport φ ⊆ spatialSegmentSafeSet U k h)

include hh hu hg hweak hφ hφcompact hφsafe in
/-- Pairing a signed spatial difference quotient with a smooth compactly
supported test equals the average pairing with the selected weak derivative. -/
theorem HasWeakVelocityPartialDerivOn.setIntegral_spatialDifferenceQuotient_mul_eq_intervalIntegral
      :
    (∫ z in U, spatialDifferenceQuotient k h u z * φ z
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ∫ t in (0 )..1,
        ∫ z in U, g z * φ (spatialShift k (-(t * h)) z)
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by


  rw [setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
    U k h u φ hu hφ.continuous hφcompact (by
        intro z hz
        have hs := hφsafe hz
        rw [mem_spatialSegmentSafeSet_iff] at hs
        exact hs (left_mem_segment ℝ z _)) (by
        intro z hz
        have hs := hφsafe hz
        rw [mem_spatialSegmentSafeSet_iff] at hs
        exact hs (right_mem_segment ℝ z _))]


  rw [show (∫ z in U, u z * spatialDifferenceQuotient k (-h) φ z) =
      ∫ z in U, ∫ t in (0 )..1,
        u z * velocityGradient φ (spatialShift k (-(t * h)) z) k by
    apply integral_congr_ae
    filter_upwards with z
    rw [backward_spatialDifferenceQuotient_eq_intervalIntegral k h hh φ hφ,
      intervalIntegral.integral_const_mul]]
  rw [← (intervalIntegral_integral_swap (integrable_joint_shifted_mul U k h u φ hu hφ hφcompact))]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t ht



  have htestSupport := translated_test_tsupport_subset U k h t (by
      simpa only [Set.uIcc_of_le zero_le_one] using ht) φ hφsafe
  have hw := hweak _
    (ContDiff.spatialTranslate hφ) (HasCompactSupport.spatialTranslate hφcompact) htestSupport
  simpa only [velocityGradient_spatialTranslate, spatialTranslate_apply, neg_neg] using
    congrArg Neg.neg hw

include hh hu hweak hφsafe in
/-- The averaged weak-derivative identity obeys the sharp constant-one `L²`
Cauchy--Schwarz bound. -/
theorem HasWeakVelocityPartialDerivOn.abs_setIntegral_spatialDifferenceQuotient_mul_le
      :
    |∫ z in U, spatialDifferenceQuotient k h u z * φ z
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)| ≤
      ‖hg.toLp g‖ *
        ‖(hφ.continuous.memLp_of_hasCompactSupport (p := (2 )) (μ :=
          (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) hφcompact).toLp φ‖ := by
  let sharedTerm_149f4b9baf := ((1 / (2 : ℝ)))
  let sharedTerm_617e1015cb := ((by norm_num : (0 : ℝ) ≤ 1))
  rw [hweak.setIntegral_spatialDifferenceQuotient_mul_eq_intervalIntegral
    U k h u g φ hh hu hg hφ hφcompact hφsafe]
  refine (intervalIntegral.abs_integral_le_integral_abs sharedTerm_617e1015cb).trans ?_
  let hφmem : MemLp φ (2 )  :=
    hφ.continuous.memLp_of_hasCompactSupport hφcompact



  calc
    ∫ t in (0 )..1,
        |∫ z in U, g z * φ (spatialShift k (-(t * h)) z)| ≤
        ∫ _t in (0 )..1, ‖hg.toLp g‖ * ‖hφmem.toLp φ‖ := intervalIntegral.integral_mono_on (by norm_num) (show IntervalIntegrable (fun t =>
      ∫ z in U, g z * φ (spatialShift k (-(t * h)) z)) volume 0 1 by
            apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
              sharedTerm_617e1015cb).2
            simpa only [IntegrableOn, Function.uncurry_def, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
              (integrable_joint_shifted_test_mul U k h g φ hg hφmem).integral_prod_left).abs
        (intervalIntegrable_const)
        (fun t _ => (show ∀ t : ℝ,
      |∫ z in U, g z * φ (spatialShift k (-(t * h)) z)| ≤
        ‖hg.toLp g‖ * ‖hφmem.toLp φ‖ by
            intro t
            let ψ  := fun z => φ (spatialShift k (-(t * h)) z)

            have hψU : MemLp ψ (2 )
                (volume.restrict U ) :=
              (show MemLp ψ (2 ) by
                  change MemLp (φ ∘ spatialShift k (-(t * h))) (2 )
                  exact hφmem.comp_measurePreserving (spatialShift_measurePreserving k (-(t * h)))).mono_measure Measure.restrict_le_self

            calc
              |∫ z in U, g z * ψ z| ≤ ∫ z in U, |g z| * |ψ z| := by
                simpa only [Real.norm_eq_abs, norm_mul] using
                  (norm_integral_le_integral_norm (μ := volume.restrict U) (fun z => g z * ψ z))
              _ ≤ (∫ z in U, |g z| ^ (2 : ℝ)) ^ sharedTerm_149f4b9baf *
                  (∫ z in U, |ψ z| ^ (2 : ℝ)) ^ sharedTerm_149f4b9baf := by
                simpa only [Real.norm_eq_abs] using
                  (integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict U) (f := g) (g := ψ)
                    Real.HolderConjugate.two_two (by
                        simpa only [ParabolicMemLpOn, ENNReal.ofReal_ofNat] using
                            hg) (by simpa only [ENNReal.ofReal_ofNat] using hψU))
              _ = ‖hg.toLp g‖ * ‖hψU.toLp ψ‖ := by
                have hgsq := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_norm_sq_eq_norm_sq_toLp g hg
                have hψsq := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_norm_sq_eq_norm_sq_toLp ψ hψU
                simp only [Real.norm_eq_abs] at hgsq hψsq
                have hgroot : (∫ z, |g z| ^ (2 : ℝ) ∂timeVelocityVolumeOn U) ^
                    sharedTerm_149f4b9baf = ‖hg.toLp g‖ := by
                  simp only [Real.rpow_two]
                  rw [← Real.sqrt_eq_rpow, hgsq, Real.sqrt_sq_eq_abs,
                    abs_of_nonneg (norm_nonneg _)]
                have hψroot : (∫ z, |ψ z| ^ (2 : ℝ) ∂timeVelocityVolumeOn U) ^
                    sharedTerm_149f4b9baf = ‖hψU.toLp ψ‖ := by
                  simp only [Real.rpow_two]
                  rw [← Real.sqrt_eq_rpow, hψsq, Real.sqrt_sq_eq_abs,
                    abs_of_nonneg (norm_nonneg _)]
                change ((∫ z, |g z| ^ (2 : ℝ) ∂timeVelocityVolumeOn U) ^ sharedTerm_149f4b9baf) *
                    ((∫ z, |ψ z| ^ (2 : ℝ) ∂timeVelocityVolumeOn U) ^ sharedTerm_149f4b9baf) = _
                rw [hgroot, hψroot]
              _ ≤ ‖hg.toLp g‖ * ‖hφmem.toLp φ‖ := by
                gcongr
                rw [Lp.norm_toLp, Lp.norm_toLp]
                refine ENNReal.toReal_mono (memLp_iff.mp hφmem).ne ?_
                calc
                  eLpNorm ψ 2 (volume.restrict U) ≤ eLpNorm ψ 2 volume :=
                    eLpNorm_mono_measure ψ Measure.restrict_le_self
                  _ = eLpNorm φ 2 volume := eLpNorm_comp_measurePreserving hφmem.aestronglyMeasurable
                      (spatialShift_measurePreserving k (-(t * h)))
              _ = ‖hg.toLp g‖ * ‖hφmem.toLp φ‖ := rfl) t)
    _ = ‖hg.toLp g‖ * ‖hφmem.toLp φ‖ := by simp

end HypoellipticAleksandrov.Parabolic
