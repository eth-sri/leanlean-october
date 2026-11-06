module

public import PDEFoundation.Measure.SegmentDouble
public import PDEFoundation.Sobolev.Inequalities.SmoothSegment
public import PDEFoundation.Sobolev.Mean
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
public import PDEFoundation.Calculus.RegularityOrder




/-!
# Smooth convex-domain Poincaré estimates

This file collects the bounded-domain integrability facts and analytic
estimates used before passing the diameter-only Poincaré inequality from
globally smooth functions to Sobolev representatives.
-/

 public section

namespace PDE

open MeasureTheory
open scoped ENNReal

variable {d : ℕ} {U : Set (Vec d)}

section
variable (hU : IsSobolevRegularDomain U) {u : Vec d → ℝ} (hu : ContDiff ℝ 0 u) {p : ℝ} (hp : 0 ≤ p)

include hU hu hp
/-- For a fixed point, the `p`th power of the smooth pairwise oscillation is
integrable on a bounded Sobolev-regular domain. -/
theorem integrableOn_abs_sub_rpow_of_contDiff

     (x : Vec d) :
    IntegrableOn (fun y => |u x - u y| ^ p)
      U  := (IntegrableOn.mono_set
  (ContinuousOn.integrableOn_compact
    (Bornology.IsBounded.isCompact_closure (IsBoundedDomain.isBounded (IsSobolevRegularDomain.isBoundedDomain hU)))
    (Continuous.continuousOn
      (Continuous.comp (Real.continuous_rpow_const hp)
        (Continuous.abs (Continuous.sub continuous_const (ContDiff.continuous hu))))))
  subset_closure)

/-- The smooth mean-subtracted `p`th power is integrable on a bounded
Sobolev-regular domain. -/
theorem integrableOn_abs_sub_integralAverage_rpow_of_contDiff

     :
    IntegrableOn
      (fun x => |u x - integralAverage U u| ^ p)
      U  := (IntegrableOn.mono_set
  (ContinuousOn.integrableOn_compact
    (Bornology.IsBounded.isCompact_closure (IsBoundedDomain.isBounded (IsSobolevRegularDomain.isBoundedDomain hU)))
    (Continuous.continuousOn
      (Continuous.comp (Real.continuous_rpow_const hp)
        (Continuous.abs (Continuous.sub (ContDiff.continuous hu) continuous_const)))))
  subset_closure)

/-- The `p`th power of pairwise smooth oscillation is integrable on the
product of a bounded Sobolev-regular domain with itself. -/
theorem integrableOn_prod_abs_sub_rpow_of_contDiff

     :
    IntegrableOn
      (fun z : Vec d × Vec d =>
        |u z.1 - u z.2| ^ p)
      (U ×ˢ U) (volume.prod volume) := (IntegrableOn.mono_set
  (ContinuousOn.integrableOn_compact
    (IsCompact.prod
      (Bornology.IsBounded.isCompact_closure (IsBoundedDomain.isBounded (IsSobolevRegularDomain.isBoundedDomain hU)))
      (Bornology.IsBounded.isCompact_closure (IsBoundedDomain.isBounded (IsSobolevRegularDomain.isBoundedDomain hU))))
    (Continuous.continuousOn
      (Continuous.comp (Real.continuous_rpow_const hp)
        (Continuous.abs
          (Continuous.sub (Continuous.comp (ContDiff.continuous hu) continuous_fst)
            (Continuous.comp (ContDiff.continuous hu) continuous_snd))))))
  (Set.prod_mono subset_closure subset_closure))
end


/-- Integrated Jensen inequality comparing oscillation about the arithmetic
mean with the normalized pairwise oscillation. -/
theorem setIntegral_abs_sub_integralAverage_rpow_le

    (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ PDE.smoothOrder u)
    {p : ℝ} (hp : 1 ≤ p)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    ∫ x in U, |u x - integralAverage U u| ^ p ≤
      (volume U).toReal⁻¹ *
        ∫ x in U, ∫ y in U,
          |u x - u y| ^ p := by
  have hpNonneg : 0 ≤ p :=
    zero_le_one.trans hp

  have hleft  :=
    integrableOn_abs_sub_integralAverage_rpow_of_contDiff
      hU.isSobolevRegularDomain (hu.of_le (by simp)) hpNonneg
  have hpair :
      Integrable
        (fun z : Vec d × Vec d =>
          |u z.1 - u z.2| ^ p)
        ((volume.restrict U).prod
          (volume.restrict U)) := by
    simpa only [← Measure.prod_restrict, IntegrableOn] using
      integrableOn_prod_abs_sub_rpow_of_contDiff
        hU.isSobolevRegularDomain
        (hu.of_le (by simp)) hpNonneg
  have hinner :
      IntegrableOn
        (fun x => ∫ y in U, |u x - u y| ^ p)
        U  := by
    simpa only [IntegrableOn] using hpair.integral_prod_left

  calc
    (∫ x in U,
        |u x - integralAverage U u| ^ p) ≤
        ∫ x in U,
          (volume U).toReal⁻¹ *
            ∫ y in U, |u x - u y| ^ p := by
      refine setIntegral_mono_on
        hleft (hinner.const_mul (volume U).toReal⁻¹) hU.measurableSet ?_
      intro x _hx
      have hJensen :=
        abs_sub_integralAverage_rpow_le_integral_abs_sub_rpow
          hp (show _ by

              exact
                (hu.continuous.continuousOn.integrableOn_compact
                  hU.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure) hUPos hUTop x
          (integrableOn_abs_sub_rpow_of_contDiff
            hU.isSobolevRegularDomain
            (hu.of_le (by simp)) hpNonneg x)
      simpa only [normalizedVolumeOn,
        integral_smul_measure, ENNReal.toReal_inv,
        volumeOn] using! hJensen
    _ = (volume U).toReal⁻¹ *
        ∫ x in U, ∫ y in U,
          |u x - u y| ^ p := by
      rw [integral_const_mul]

variable {D : ℝ} (hU : IsOpenBoundedConvexDomain U) (hUDiameter : HasEuclideanDiameterLE U D) (hD : 0 ≤ D) {u : Vec d → ℝ} (hu : ContDiff ℝ PDE.smoothOrder u) {p : ℝ} (hp : 1 ≤ p)

include hU hUDiameter hD hu hp
/-- Smooth pairwise oscillation is controlled by the diameter and the
Euclidean gradient, with a constant independent of `p`. -/
theorem setIntegral_setIntegral_abs_sub_rpow_le
      :
    (∫ x in U, ∫ y in U,
        |u x - u y| ^ p) ≤
      D ^ p * ((2 : ℝ) ^ d * (volume U).toReal *
        ∫ z in U,
          vecEuclideanNorm (classicalGradient u z) ^ p) := by
  let sharedTerm_1c1b45c052 := ((2 : ℝ) ^ d * (volume U).toReal)
  let sharedTerm_6ef83d4276 := ((volume.restrict (Set.Ioc (0 : ℝ) 1)))
  have hpNonneg : 0 ≤ p :=
    zero_le_one.trans hp
  let g  :=
    fun z =>
      vecEuclideanNorm (classicalGradient u z) ^ p
  let μU : Measure (Vec d) :=
    volumeOn U
  let μPair : Measure (Vec d × Vec d) :=
    μU.prod μU
  let F : ℝ → Vec d × Vec d → ℝ :=
    fun t z => g (segmentBlend z.1 t z.2)
  have hgradCont :
      Continuous (classicalGradient u) :=
    PDE.ContDiff.continuous_classicalGradient
      (hu.of_le (by norm_num) : ContDiff ℝ 1 u)
  have hgCont : Continuous g := Real.continuous_rpow_const hpNonneg
        |>.comp (continuous_vecEuclideanNorm.comp hgradCont)

  have hclosureCompact : IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  have hPairIntegrable (t : ℝ) :
      Integrable (F t) μPair := by

    have hOnClosure :
        IntegrableOn (F t)
          (closure U ×ˢ closure U)
          (volume.prod volume) :=
      (hgCont.comp (by
          simpa only [segmentBlend_eq_smul_add] using!
            (((continuous_const_smul (1 - t)).comp
              continuous_snd).add
                ((continuous_const_smul t).comp continuous_fst)))).continuousOn
        |>.integrableOn_compact
          (hclosureCompact.prod hclosureCompact)
    have hOnProduct  :=
      hOnClosure.mono_set
        (Set.prod_mono subset_closure subset_closure)
    change
      Integrable (F t)
        ((volume.restrict U).prod
          (volume.restrict U))
    rw [Measure.prod_restrict]
    exact hOnProduct

  have hTriple :
      Integrable (Function.uncurry F)
        (sharedTerm_6ef83d4276.prod
          μPair) := by
    have hOnClosure :
        IntegrableOn (Function.uncurry F)
          (Set.Icc (0 : ℝ) 1 ×ˢ
            (closure U ×ˢ closure U))
          (volume.prod (volume.prod volume)) :=
      (show Continuous (Function.uncurry F) by

          exact hgCont.comp (by
              simpa only [segmentBlend_eq_smul_add] using!
                (((continuous_const.sub continuous_fst).smul
                  (continuous_snd.comp continuous_snd)).add
                    (continuous_fst.smul
                      (continuous_fst.comp continuous_snd))))).continuousOn.integrableOn_compact
        (isCompact_Icc.prod
          (hclosureCompact.prod hclosureCompact))
    have hOnProduct  :=
      hOnClosure.mono_set
        (Set.prod_mono Set.Ioc_subset_Icc_self
          (Set.prod_mono subset_closure subset_closure))
    change
      Integrable (Function.uncurry F)
        (sharedTerm_6ef83d4276.prod
          ((volume.restrict U).prod
            (volume.restrict U)))
    rw [Measure.prod_restrict, Measure.prod_restrict]
    exact hOnProduct
  have hPairOscillation :
      Integrable
        (fun z : Vec d × Vec d =>
          |u z.1 - u z.2| ^ p) μPair := by
    change
      Integrable
        (fun z : Vec d × Vec d =>
          |u z.1 - u z.2| ^ p)
        ((volume.restrict U).prod
          (volume.restrict U))
    simpa only [← Measure.prod_restrict, IntegrableOn] using
      integrableOn_prod_abs_sub_rpow_of_contDiff
        hU.isSobolevRegularDomain
        (hu.of_le (by simp)) hpNonneg





  let C : ℝ :=
    sharedTerm_1c1b45c052 *
      ∫ z in U, g z


  calc
    (∫ x in U, ∫ y in U,
        |u x - u y| ^ p) =
        ∫ z, |u z.1 - u z.2| ^ p ∂μPair := (Eq.symm (id (integral_prod (fun z => |u z.1 - u z.2| ^ p) hPairOscillation)))
    _ ≤ ∫ z,
        D ^ p * (∫ t in (0 )..1, F t z)
          ∂μPair :=
      (by
          refine integral_mono_ae
            hPairOscillation ((show Integrable
        (fun z =>
          ∫ t in (0 )..1, F t z) μPair by

                simpa only [
                  intervalIntegral.integral_of_le zero_le_one]
                  using! hTriple.integral_prod_right).const_mul (D ^ p)) ?_

          change
            (fun z : Vec d × Vec d =>
              |u z.1 - u z.2| ^ p) ≤ᵐ[
                (volume.restrict U).prod
                  (volume.restrict U)]
              (fun z =>
                D ^ p * (∫ t in (0 )..1, F t z))
          rw [Measure.prod_restrict]
          filter_upwards [ae_restrict_mem (hU.measurableSet.prod hU.measurableSet)] with z hz
          exact
            abs_sub_rpow_le_diameter_rpow_mul_integral_euclideanGradient_rpow
              hp hUDiameter hu hz.1 hz.2)
    _ = D ^ p *
        ∫ z, (∫ t in (0 )..1, F t z) ∂μPair := by
      rw [integral_const_mul]
    _ = D ^ p *
        ∫ t in (0 )..1,
          ∫ z, F t z ∂μPair := by

      rw [intervalIntegral_integral_swap (by
          simpa only [Set.uIoc_of_le zero_le_one] using
            hTriple)]
    _ ≤ D ^ p * C :=
      mul_le_mul_of_nonneg_left (by
          calc
            (∫ t in (0 )..1,
                ∫ z, F t z ∂μPair) ≤
                ∫ _t in (0 )..1, C := by
              refine intervalIntegral.integral_mono_on
                zero_le_one (by
                    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
                      zero_le_one]
                    exact hTriple.integral_prod_left) intervalIntegrable_const ?_
              intro t ht
              have hFubini :=
                integral_prod (F t) (hPairIntegrable t)
              have hSegment :=
                setIntegral_setIntegral_comp_segmentBlend_le_two_pow_mul
                  hU hgCont (by
                      intro z
                      exact Real.rpow_nonneg (vecEuclideanNorm_nonneg _) p) t ht
              linarith
            _ = C := by
              simp)
        (Real.rpow_nonneg hD p)
    _ = D ^ p * (sharedTerm_1c1b45c052 *
        ∫ z in U,
          vecEuclideanNorm (classicalGradient u z) ^ p) := rfl

/-- Diameter-only smooth Poincaré inequality in integral-power form.

The constant `2 ^ d` is independent of the real exponent `p ≥ 1`. -/
theorem setIntegral_abs_sub_integralAverage_rpow_le_two_pow_mul

    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    (∫ x in U,
        |u x - integralAverage U u| ^ p) ≤
      (2 : ℝ) ^ d * D ^ p *
        ∫ z in U,
          vecEuclideanNorm (classicalGradient u z) ^ p := by
  let sharedTerm_fcf3b5ec88 := (∫ z in U, vecEuclideanNorm (classicalGradient u z) ^ p ∂volume)


  have hJensen :=
    setIntegral_abs_sub_integralAverage_rpow_le
      hU hu hp hUPos hUTop
  have hPairwise :=
    setIntegral_setIntegral_abs_sub_rpow_le
      hU hUDiameter hD hu hp
  calc
    (∫ x in U,
        |u x - integralAverage U u| ^ p) ≤
        (volume U).toReal⁻¹ *
          ∫ x in U, ∫ y in U,
            |u x - u y| ^ p :=
      hJensen
    _ ≤ (volume U).toReal⁻¹ *
        (D ^ p * ((2 : ℝ) ^ d * (volume U).toReal *
          sharedTerm_fcf3b5ec88)) :=
      mul_le_mul_of_nonneg_left hPairwise
        (by
            positivity)
    _ = (2 : ℝ) ^ d * D ^ p *
        sharedTerm_fcf3b5ec88 := by
      field_simp [((ENNReal.toReal_pos hUPos.ne' hUTop.ne).ne')]

end PDE
