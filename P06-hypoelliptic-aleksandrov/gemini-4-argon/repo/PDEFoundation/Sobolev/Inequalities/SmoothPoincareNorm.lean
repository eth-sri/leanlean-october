module

public import PDEFoundation.Measure.LpPower
public import PDEFoundation.Sobolev.Inequalities.SmoothPoincare
public import PDEFoundation.Sobolev.W1p.EuclideanGradient
public import PDEFoundation.Sobolev.W1p.Smooth
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import PDEFoundation.Measure.AffineVolume
import PDEFoundation.Measure.Jensen
import PDEFoundation.Measure.NormalizedLp
import PDEFoundation.Measure.SegmentDouble
import PDEFoundation.Sobolev.Inequalities.SmoothSegment
import PDEFoundation.Sobolev.Mean

/-!
# Smooth convex-domain Poincaré estimates in `L^p` norm form

This file converts the integral-power estimate for globally smooth functions
into the extended-real norm used by the public Sobolev theorem. The displayed
constant is `2 ^ d`, uniformly for every real exponent `p ≥ 1`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory
open scoped Pointwise

theorem eLpNormOn_sub_integralAverage_le_two_pow_mul_of_contDiff
    {d : ℕ} {U : Set (Vec d)} {D p : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hp : 1 ≤ p)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    eLpNormOn U (ENNReal.ofReal p)
        (fun x => u x - integralAverage U u) ≤
      ENNReal.ofReal ((2 : ℝ) ^ d * D) *
        euclideanFieldELpNormOn U (ENNReal.ofReal p)
          (classicalGradient u) := by
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  have hpPos : 0 < p :=
    zero_lt_one.trans_le hp
  let us :
      W1pFunction U (ENNReal.ofReal p) :=
    W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
      hU (hu.of_le (by norm_num))
  have hsubMem :
      MemLp (fun x => u x - integralAverage U u)
        (ENNReal.ofReal p) (volumeOn U) := by
    have hconst :
        MemLp (fun _ : Vec d => integralAverage U u)
          (ENNReal.ofReal p) (volumeOn U) :=
      memLp_const _
    simpa only [us,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain_toFun]
      using! us.memLp.sub hconst
  have hgradHilbert :
      MemLp (toHilbertVecField (classicalGradient u))
        (ENNReal.ofReal p) (volumeOn U) := by
    apply gradMemLpOn_iff_memLp_toHilbertVecField.mp
    simpa only [us,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain_grad]
      using us.gradMemLp
  have hgradMem :
      MemLp
        (fun x => vecEuclideanNorm (classicalGradient u x))
        (ENNReal.ofReal p) (volumeOn U) := by
    exact
      MemLp.ae_eq
        (Filter.Eventually.of_forall fun x =>
          norm_toHilbertVecField_apply
            (classicalGradient u) x)
        hgradHilbert.norm
  let A : ℝ :=
    ∫ x in U, |u x - integralAverage U u| ^ p ∂volume
  let B : ℝ :=
    ∫ x in U,
      vecEuclideanNorm (classicalGradient u x) ^ p ∂volume
  let C : ℝ :=
    (2 : ℝ) ^ d
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact integral_nonneg_of_ae <|
      Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (abs_nonneg _) _
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact integral_nonneg_of_ae <|
      Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact one_le_pow₀ (by norm_num)
  have hIntegral : A ≤ C * D ^ p * B := by
    have _h_xinl_0 : (∫ x in U,
        |u x - integralAverage U u| ^ p ∂volume) ≤
      (2 : ℝ) ^ d * D ^ p *
        ∫ z in U,
          vecEuclideanNorm (classicalGradient u z) ^ p
            ∂volume := by
      have hvolReal : (volume U).toReal ≠ 0 :=
        (ENNReal.toReal_pos hUPos.ne' hUTop.ne).ne'
      have hvolInvNonneg : 0 ≤ (volume U).toReal⁻¹ := by
        positivity
      have hJensen : ∫ x in U, |u x - integralAverage U u| ^ p ∂volume ≤
      (volume U).toReal⁻¹ *
        ∫ x in U, ∫ y in U,
          |u x - u y| ^ p ∂volume ∂volume := by
          have hpNonneg : 0 ≤ p :=
            zero_le_one.trans hp
          have huInt :
              IntegrableOn u U volume := by
            have hclosureCompact : IsCompact (closure U) :=
              hU.isBoundedDomain.isBounded.isCompact_closure
            exact
              (hu.continuous.continuousOn.integrableOn_compact
                hclosureCompact).mono_set subset_closure
          have hleft :=
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
                (fun x => ∫ y in U, |u x - u y| ^ p ∂volume)
                U volume := by
            simpa only [IntegrableOn] using hpair.integral_prod_left
          have hright :
              IntegrableOn
                (fun x =>
                  (volume U).toReal⁻¹ *
                    ∫ y in U, |u x - u y| ^ p ∂volume)
                U volume :=
            hinner.const_mul (volume U).toReal⁻¹
          calc
            (∫ x in U,
                |u x - integralAverage U u| ^ p ∂volume) ≤
                ∫ x in U,
                  (volume U).toReal⁻¹ *
                    ∫ y in U, |u x - u y| ^ p ∂volume
                  ∂volume := by
              refine setIntegral_mono_on
                hleft hright hU.measurableSet ?_
              intro x _hx
              have hJensen : |u x - integralAverage U u| ^ p ≤
              ∫ y, |u x - u y| ^ p ∂normalizedVolumeOn U := by
                have hup : IntegrableOn (fun y => |u x - u y| ^ p) U volume := by
                  have hU := hU.isSobolevRegularDomain
                  have hu : ContDiff ℝ 0 u := (hu.of_le (by simp))
                  have huCont : Continuous u :=
                    hu.continuous
                  have hcont :
                      Continuous (fun y => |u x - u y| ^ p) :=
                    Real.continuous_rpow_const hpNonneg
                      |>.comp (continuous_const.sub huCont).abs
                  have hclosureCompact : IsCompact (closure U) :=
                    hU.isBoundedDomain.isBounded.isCompact_closure
                  exact
                    (hcont.continuousOn.integrableOn_compact
                      hclosureCompact).mono_set subset_closure

                let : IsProbabilityMeasure (normalizedVolumeOn U) :=
                  isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
                    hUPos hUTop
                have hconst :
                    IntegrableOn (fun _ : Vec d => u x) U volume :=
                  integrableOn_const hUTop.ne
                have hdiff :
                    Integrable (fun y => u x - u y)
                      (normalizedVolumeOn U) :=
                  integrable_normalizedVolumeOn_of_integrableOn
                    (hconst.sub huInt) hUPos
                have hpowDiff :
                    Integrable (fun y => |u x - u y| ^ p)
                      (normalizedVolumeOn U) :=
                  integrable_normalizedVolumeOn_of_integrableOn
                    hup hUPos
                have _h_xinl_0 : u x - integralAverage U u =
              ∫ y, (u x - u y) ∂normalizedVolumeOn U := by
                    rw [normalizedVolumeOn, integral_smul_measure,
                      ENNReal.toReal_inv]
                    have hvolReal : (volume U).toReal ≠ 0 :=
                      (ENNReal.toReal_pos hUPos.ne' hUTop.ne).ne'
                    have hconstInt :
                        IntegrableOn (fun _ : Vec d => u x) U volume :=
                      integrableOn_const hUTop.ne
                    have hconst :
                        ∫ y in U, (u x : ℝ) ∂volume =
                          (volume U).toReal * u x := by
                      rw [setIntegral_const]
                      rfl
                    let I : ℝ := ∫ y in U, u y ∂volume
                    have hscale :
                        u x - (volume U).toReal⁻¹ * I =
                          (volume U).toReal⁻¹ *
                            ((volume U).toReal * u x - I) := by
                      field_simp [hvolReal]
                    calc
                      u x - integralAverage U u =
                          u x - (volume U).toReal⁻¹ * I := by
                        rfl
                      _ = (volume U).toReal⁻¹ *
                            ((volume U).toReal * u x - I) :=
                        hscale
                      _ = (volume U).toReal⁻¹ *
                            ((∫ y in U, u x ∂volume) - I) := by
                        rw [← hconst]
                      _ = (volume U).toReal⁻¹ *
                          ∫ y in U, (u x - u y) ∂volume := by
                        rw [integral_sub hconstInt huInt]

                  /- Jensen's inequality for the mean-subtracted value, written on normalized
                  restricted volume. -/
                rw [_h_xinl_0]
                exact abs_integral_rpow_le_integral_abs_rpow
                  hp hdiff hpowDiff
              simpa only [normalizedVolumeOn,
                integral_smul_measure, ENNReal.toReal_inv,
                volumeOn] using! hJensen
            _ = (volume U).toReal⁻¹ *
                ∫ x in U, ∫ y in U,
                  |u x - u y| ^ p ∂volume ∂volume := by
              rw [integral_const_mul]

        /- Smooth pairwise oscillation is controlled by the diameter and the
        Euclidean gradient, with a constant independent of `p`. -/
      have hPairwise : (∫ x in U, ∫ y in U,
            |u x - u y| ^ p ∂volume ∂volume) ≤
          D ^ p * ((2 : ℝ) ^ d * (volume U).toReal *
            ∫ z in U,
              vecEuclideanNorm (classicalGradient u z) ^ p
                ∂volume) := by
          have hpNonneg : 0 ≤ p :=
            zero_le_one.trans hp
          let g : Vec d → ℝ :=
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
          have hgCont : Continuous g := by
            exact
              Real.continuous_rpow_const hpNonneg
                |>.comp (continuous_vecEuclideanNorm.comp hgradCont)
          have hgNonneg : ∀ z, 0 ≤ g z := by
            intro z
            exact Real.rpow_nonneg (vecEuclideanNorm_nonneg _) p
          have hclosureCompact : IsCompact (closure U) :=
            hU.isBoundedDomain.isBounded.isCompact_closure
          have hPairIntegrable (t : ℝ) :
              Integrable (F t) μPair := by
            have hsegmentCont :
                Continuous
                  (fun z : Vec d × Vec d =>
                    segmentBlend z.1 t z.2) := by
              simpa only [segmentBlend_eq_smul_add] using!
                (((continuous_const_smul (1 - t)).comp
                  continuous_snd).add
                    ((continuous_const_smul t).comp continuous_fst))
            have hOnClosure :
                IntegrableOn (F t)
                  (closure U ×ˢ closure U)
                  (volume.prod volume) :=
              (hgCont.comp hsegmentCont).continuousOn
                |>.integrableOn_compact
                  (hclosureCompact.prod hclosureCompact)
            have hOnProduct :
                IntegrableOn (F t) (U ×ˢ U)
                  (volume.prod volume) :=
              hOnClosure.mono_set
                (Set.prod_mono subset_closure subset_closure)
            change
              Integrable (F t)
                ((volume.restrict U).prod
                  (volume.restrict U))
            rw [Measure.prod_restrict]
            exact hOnProduct
          have hFCont :
              Continuous (Function.uncurry F) := by
            have hsegmentCont :
                Continuous
                  (fun q : ℝ × (Vec d × Vec d) =>
                    segmentBlend q.2.1 q.1 q.2.2) := by
              simpa only [segmentBlend_eq_smul_add] using!
                (((continuous_const.sub continuous_fst).smul
                  (continuous_snd.comp continuous_snd)).add
                    (continuous_fst.smul
                      (continuous_fst.comp continuous_snd)))
            exact hgCont.comp hsegmentCont
          have hTriple :
              Integrable (Function.uncurry F)
                ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
                  μPair) := by
            have hOnClosure :
                IntegrableOn (Function.uncurry F)
                  (Set.Icc (0 : ℝ) 1 ×ˢ
                    (closure U ×ˢ closure U))
                  (volume.prod (volume.prod volume)) :=
              hFCont.continuousOn.integrableOn_compact
                (isCompact_Icc.prod
                  (hclosureCompact.prod hclosureCompact))
            have hOnProduct :
                IntegrableOn (Function.uncurry F)
                  (Set.Ioc (0 : ℝ) 1 ×ˢ (U ×ˢ U))
                  (volume.prod (volume.prod volume)) :=
              hOnClosure.mono_set
                (Set.prod_mono Set.Ioc_subset_Icc_self
                  (Set.prod_mono subset_closure subset_closure))
            change
              Integrable (Function.uncurry F)
                ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
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
          have hIntervalSection :
              Integrable
                (fun z =>
                  ∫ t in (0 : ℝ)..1, F t z) μPair := by
            have hsection :=
              hTriple.integral_prod_right
            simpa only [
              intervalIntegral.integral_of_le zero_le_one]
              using! hsection
          have hDiameterPowNonneg : 0 ≤ D ^ p :=
            Real.rpow_nonneg hD p
          have hRight :
              Integrable
                (fun z =>
                  D ^ p * (∫ t in (0 : ℝ)..1, F t z))
                μPair :=
            hIntervalSection.const_mul (D ^ p)
          have hPairBound :
              (∫ z, |u z.1 - u z.2| ^ p ∂μPair) ≤
                ∫ z,
                  D ^ p * (∫ t in (0 : ℝ)..1, F t z)
                    ∂μPair := by
            refine integral_mono_ae
              hPairOscillation hRight ?_
            have hmeas : MeasurableSet (U ×ˢ U) :=
              hU.measurableSet.prod hU.measurableSet
            change
              (fun z : Vec d × Vec d =>
                |u z.1 - u z.2| ^ p) ≤ᵐ[
                  (volume.restrict U).prod
                    (volume.restrict U)]
                (fun z =>
                  D ^ p * (∫ t in (0 : ℝ)..1, F t z))
            rw [Measure.prod_restrict]
            filter_upwards [ae_restrict_mem hmeas] with z hz
            exact
              abs_sub_rpow_le_diameter_rpow_mul_integral_euclideanGradient_rpow
                hp hUDiameter hu hz.1 hz.2
          have hIntervalPair :
              IntervalIntegrable
                (fun t => ∫ z, F t z ∂μPair)
                volume 0 1 := by
            rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
              zero_le_one]
            exact hTriple.integral_prod_left
          let C : ℝ :=
            (2 : ℝ) ^ d * (volume U).toReal *
              ∫ z in U, g z ∂volume
          have hConstInterval :
              IntervalIntegrable (fun _ : ℝ => C)
                volume 0 1 :=
            intervalIntegrable_const
          have hIntervalBound :
              (∫ t in (0 : ℝ)..1,
                ∫ z, F t z ∂μPair) ≤ C := by
            calc
              (∫ t in (0 : ℝ)..1,
                  ∫ z, F t z ∂μPair) ≤
                  ∫ _t in (0 : ℝ)..1, C := by
                refine intervalIntegral.integral_mono_on
                  zero_le_one hIntervalPair hConstInterval ?_
                intro t ht
                have hFubini :=
                  integral_prod (F t) (hPairIntegrable t)
                have hSegment :=
                  setIntegral_setIntegral_comp_segmentBlend_le_two_pow_mul
                    hU hgCont hgNonneg t ht
                change (∫ z, F t z ∂μPair) ≤ C
                rw [hFubini]
                simpa only [F, g, μPair, μU, volumeOn, C] using
                  hSegment
              _ = C := by
                simp
          calc
            (∫ x in U, ∫ y in U,
                |u x - u y| ^ p ∂volume ∂volume) =
                ∫ z, |u z.1 - u z.2| ^ p ∂μPair := by
              symm
              simpa only [μPair, μU, volumeOn] using
                integral_prod
                  (fun z : Vec d × Vec d =>
                    |u z.1 - u z.2| ^ p)
                  hPairOscillation
            _ ≤ ∫ z,
                D ^ p * (∫ t in (0 : ℝ)..1, F t z)
                  ∂μPair :=
              hPairBound
            _ = D ^ p *
                ∫ z, (∫ t in (0 : ℝ)..1, F t z) ∂μPair := by
              rw [integral_const_mul]
            _ = D ^ p *
                ∫ t in (0 : ℝ)..1,
                  ∫ z, F t z ∂μPair := by
              have hTripleInterval :
                  Integrable (Function.uncurry F)
                    ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
                      μPair) := by
                simpa only [Set.uIoc_of_le zero_le_one] using
                  hTriple
              rw [intervalIntegral_integral_swap hTripleInterval]
            _ ≤ D ^ p * C :=
              mul_le_mul_of_nonneg_left hIntervalBound
                hDiameterPowNonneg
            _ = D ^ p * ((2 : ℝ) ^ d * (volume U).toReal *
                ∫ z in U,
                  vecEuclideanNorm (classicalGradient u z) ^ p
                    ∂volume) := by
              rfl

        /- Diameter-only smooth Poincaré inequality in integral-power form.

        The constant `2 ^ d` is independent of the real exponent `p ≥ 1`. -/
      calc
        (∫ x in U,
            |u x - integralAverage U u| ^ p ∂volume) ≤
            (volume U).toReal⁻¹ *
              ∫ x in U, ∫ y in U,
                |u x - u y| ^ p ∂volume ∂volume :=
          hJensen
        _ ≤ (volume U).toReal⁻¹ *
            (D ^ p * ((2 : ℝ) ^ d * (volume U).toReal *
              ∫ z in U,
                vecEuclideanNorm (classicalGradient u z) ^ p
                  ∂volume)) :=
          mul_le_mul_of_nonneg_left hPairwise
            hvolInvNonneg
        _ = (2 : ℝ) ^ d * D ^ p *
            ∫ z in U,
              vecEuclideanNorm (classicalGradient u z) ^ p
                ∂volume := by
          field_simp [hvolReal]
    simpa only [A, B, C] using _h_xinl_0
  have hRoot :
      A ^ (1 / p : ℝ) ≤
        C * D * B ^ (1 / p : ℝ) := by
      have hpPos : 0 < p :=
        zero_lt_one.trans_le hp
      have hinvNonneg : 0 ≤ (1 / p : ℝ) := by
        positivity
      have hinvLeOne : (1 / p : ℝ) ≤ 1 :=
        (div_le_one hpPos).2 hp
      have hCNonneg : 0 ≤ C :=
        zero_le_one.trans hC
      have hDPowNonneg : 0 ≤ D ^ p :=
        Real.rpow_nonneg hD p
      calc
        A ^ (1 / p : ℝ) ≤
            (C * D ^ p * B) ^ (1 / p : ℝ) :=
          Real.rpow_le_rpow hA hIntegral hinvNonneg
        _ = C ^ (1 / p : ℝ) *
            (D ^ p) ^ (1 / p : ℝ) *
              B ^ (1 / p : ℝ) := by
          rw [Real.mul_rpow (mul_nonneg hCNonneg hDPowNonneg) hB,
            Real.mul_rpow hCNonneg hDPowNonneg]
        _ = C ^ (1 / p : ℝ) * D *
            B ^ (1 / p : ℝ) := by
          rw [one_div, Real.rpow_rpow_inv hD hpPos.ne']
        _ ≤ C * D * B ^ (1 / p : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_
            (Real.rpow_nonneg hB _)
          exact
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_self_of_one_le hC hinvLeOne) hD

    /- Smooth diameter-only Poincaré inequality in the unnormalized extended
    `L^p` norm. The constant `2 ^ d` is independent of `p`. -/
  have hLeftReal :
      (eLpNormOn U (ENNReal.ofReal p)
        (fun x => u x - integralAverage U u)).toReal =
          A ^ (1 / p : ℝ) := by
    simpa only [eLpNormOn, volumeOn, A, Real.norm_eq_abs] using
      toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv
        hpPos hsubMem
  have hGradReal :
      (euclideanFieldELpNormOn U (ENNReal.ofReal p)
        (classicalGradient u)).toReal =
          B ^ (1 / p : ℝ) := by
    simpa only [euclideanFieldELpNormOn, eLpNormOn, volumeOn,
      B, Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
      toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv
        hpPos hgradMem
  have hLeftTop :
      eLpNormOn U (ENNReal.ofReal p)
        (fun x => u x - integralAverage U u) ≠ ∞ :=
    hsubMem.eLpNorm_ne_top
  have hGradTop :
      euclideanFieldELpNormOn U (ENNReal.ofReal p)
        (classicalGradient u) ≠ ∞ :=
    hgradMem.eLpNorm_ne_top
  have hRightTop :
      ENNReal.ofReal (C * D) *
        euclideanFieldELpNormOn U (ENNReal.ofReal p)
          (classicalGradient u) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGradTop
  have hCDNonneg : 0 ≤ C * D :=
    mul_nonneg (zero_le_one.trans hC) hD
  refine
    (ENNReal.toReal_le_toReal hLeftTop hRightTop).mp ?_
  rw [hLeftReal, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hCDNonneg, hGradReal]
  simpa only [C] using hRoot

/- Smooth diameter-only Poincaré inequality in the normalized extended
`L^p` norm. The constant `2 ^ d` is independent of `p`. -/
theorem eLpMeanNormOn_sub_integralAverage_le_two_pow_mul_of_contDiff
    {d : ℕ} {U : Set (Vec d)} {D p : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hp : 1 ≤ p)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    eLpMeanNormOn U (ENNReal.ofReal p)
        (fun x => u x - integralAverage U u) ≤
      ENNReal.ofReal ((2 : ℝ) ^ d * D) *
        euclideanFieldELpMeanNormOn U (ENNReal.ofReal p)
          (classicalGradient u) := by
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn
      hUTop,
    euclideanFieldELpMeanNormOn_eq_volume_inv_rpow_mul
      hUTop]
  calc
    (volume U)⁻¹ ^ (1 / ENNReal.ofReal p).toReal *
          eLpNormOn U (ENNReal.ofReal p)
            (fun x => u x - integralAverage U u) ≤
        (volume U)⁻¹ ^ (1 / ENNReal.ofReal p).toReal *
          (ENNReal.ofReal ((2 : ℝ) ^ d * D) *
            euclideanFieldELpNormOn U (ENNReal.ofReal p)
              (classicalGradient u)) :=
      mul_le_mul_right
        (eLpNormOn_sub_integralAverage_le_two_pow_mul_of_contDiff
          hU hUDiameter hD hu hp hUPos hUTop) _
    _ = ENNReal.ofReal ((2 : ℝ) ^ d * D) *
        ((volume U)⁻¹ ^ (1 / ENNReal.ofReal p).toReal *
          euclideanFieldELpNormOn U (ENNReal.ofReal p)
            (classicalGradient u)) := by
      ac_rfl

end PDE
