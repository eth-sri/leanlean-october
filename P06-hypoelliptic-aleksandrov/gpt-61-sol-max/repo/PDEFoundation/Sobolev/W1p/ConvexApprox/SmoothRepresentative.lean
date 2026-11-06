module

public import PDEFoundation.Measure.Jensen
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Kernel
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
public import PDEFoundation.Calculus.RegularityOrder




/-!
# Smooth representatives for convex-domain approximation

This file defines the globally smooth representative of convex approximation.
It also records the measurable change of variables, exact `L^p` bounds, and
integrability lemmas needed by the later density and weak-derivative modules.

The convolution contraction used below is kept private: it is an implementation
lemma for this layer, not a second public Sobolev-space API.
-/

@[expose] public section

open scoped ENNReal Pointwise Convolution

namespace PDE

open MeasureTheory

noncomputable section

private theorem isProbabilityMeasure_withDensity_ofReal
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ : α → ℝ}
    (hρNonneg : ∀ x, 0 ≤ ρ x)
    (hρInt : Integrable ρ μ)
    (hρOne : ∫ x, ρ x ∂μ = 1) :
    IsProbabilityMeasure
      (μ.withDensity fun x => ENNReal.ofReal (ρ x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hρInt
    (ae_of_all _ hρNonneg), hρOne]
  simp

variable {d : ℕ}

private theorem lintegral_comp_sub_right
     (f : Vec d → ℝ≥0∞) (hf : Measurable f)
    (t : Vec d) :
    ∫⁻ x, f (x - t) ∂(volume : Measure (Vec d)) =
      ∫⁻ x, f x ∂(volume : Measure (Vec d)) := (measurePreserving_sub_right volume t).lintegral_comp hf

private theorem fubini_translation_key
     (ρ : Vec d → ℝ≥0∞) (g : Vec d → ℝ)
    (p : ℝ) (hρ : Measurable ρ) (hg : Measurable g) :
    ∫⁻ x, ∫⁻ t,
        ρ t * (ENNReal.ofReal |g (x - t)|) ^ p =
      (∫⁻ t, ρ t) *
        (∫⁻ x, (ENNReal.ofReal |g x|) ^ p) := by
  have hswap :
      ∫⁻ x, ∫⁻ t,
          ρ t * (ENNReal.ofReal |g (x - t)|) ^ p =
        ∫⁻ t, ∫⁻ x,
          ρ t * (ENNReal.ofReal |g (x - t)|) ^ p := by
    apply lintegral_lintegral_swap
    apply AEMeasurable.mul
    · exact (hρ.comp measurable_snd).aemeasurable
    · apply Measurable.aemeasurable
      apply Measurable.pow_const
      exact
        ENNReal.measurable_ofReal.comp
          (continuous_abs.measurable.comp
            (hg.comp (measurable_fst.sub measurable_snd)))
  rw [hswap]
  have hfactor :
      ∫⁻ t, ∫⁻ x,
          ρ t * (ENNReal.ofReal |g (x - t)|) ^ p =
        ∫⁻ t, ρ t *
          ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p := by
    congr 1
    ext t
    exact
      lintegral_const_mul _ <|
        Measurable.pow_const
          (ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp
              (hg.comp
                (measurable_id.sub measurable_const)))) p
  rw [hfactor]
  have htrans :
      ∀ t,
        ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p
            ∂(volume : Measure (Vec d)) =
          ∫⁻ x, (ENNReal.ofReal |g x|) ^ p := by
    intro t
    exact
      lintegral_comp_sub_right _
        (Measurable.pow_const
          (ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp hg)) p) t
  simp_rw [htrans]
  rw [lintegral_mul_const _ hρ, mul_comm]

private theorem integral_withDensity_ofReal_eq_integral_mul
     {f g : Vec d → ℝ}
    (hfNonneg : ∀ x, 0 ≤ f x)
    (hfMeas : AEMeasurable f ) :
    ∫ x, g x
        ∂(volume.withDensity fun x => ENNReal.ofReal (f x)) =
      ∫ x, f x * g x := by
  have heq :
      (fun x => ENNReal.ofReal (f x)) =
        fun x => (Real.toNNReal (f x) : ℝ≥0∞) := by
    funext x
    rw [ENNReal.ofReal_eq_coe_nnreal (hfNonneg x),
      Real.toNNReal_of_nonneg (hfNonneg x)]
  rw [heq]
  rw [integral_withDensity_eq_integral_smul₀
    (hfMeas.real_toNNReal)]
  congr 1
  funext x
  simp [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (hfNonneg x)]

section
variable {ρ g : Vec d → ℝ} {p : ENNReal} (hp : 1 ≤ p) (hpTop : p ≠ ⊤) (hρNonneg : ∀ x, 0 ≤ ρ x) (hρInt : Integrable ρ volume) (hρOne : ∫ x, ρ x = 1) (hρMeas : Measurable ρ)

include hp hpTop hρNonneg hρInt hρOne hρMeas
private theorem young_convolution_nonneg_integral_one

    (hgMeas : Measurable g) :
    eLpNorm
        (convolution ρ g
          (ContinuousLinearMap.lsmul ℝ ℝ) )
        p  ≤
      eLpNorm g p  := by
  let sharedTerm_ed3401cd9d := (Continuous (fun y : ℝ => |y| ^ p.toReal))
  have hpNeZero  :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpPos  :=
    ENNReal.toReal_pos hpNeZero hpTop

  let μ : Measure (Vec d) :=
    volume.withDensity fun t => ENNReal.ofReal (ρ t)
  let _ : IsProbabilityMeasure μ :=
    isProbabilityMeasure_withDensity_ofReal
      hρNonneg hρInt hρOne
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpNeZero hpTop
    (hρMeas.aestronglyMeasurable.convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hgMeas.aestronglyMeasurable)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpNeZero hpTop
    hgMeas.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow _
    (by positivity : 0 ≤ 1 / p.toReal)
  have hfubini :=
    fubini_translation_key
      (fun t => ENNReal.ofReal (ρ t)) g p.toReal
      hρMeas.ennreal_ofReal hgMeas
  have hρLintegralOne :
      ∫⁻ t, ENNReal.ofReal (ρ t) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρInt
      (ae_of_all _ hρNonneg), hρOne]
    simp

  calc
    ∫⁻ x,
        ‖convolution ρ g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^
          p.toReal ≤
      ∫⁻ x, ∫⁻ t,
          ENNReal.ofReal (ρ t) *
            (ENNReal.ofReal |g (x - t)|) ^ p.toReal :=
      lintegral_mono (show ∀ x,
        ‖convolution ρ g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^
            p.toReal ≤
          ∫⁻ t,
            ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal by
          intro x
          rw [convolution_def]
          simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
          rw [Real.enorm_eq_ofReal_abs]
          have heqIntegral :
              ∫ t, ρ t * g (x - t) =
                ∫ t, g (x - t) ∂μ := by
            symm
            exact
              integral_withDensity_ofReal_eq_integral_mul
                hρNonneg hρMeas.aemeasurable
          rw [heqIntegral]
          by_cases hgInt :
              Integrable (fun t => g (x - t)) μ
          · by_cases hgPowInt :
                Integrable
                  (fun t => |g (x - t)| ^ p.toReal) μ
            · have hJensen :=
                abs_integral_rpow_le_integral_abs_rpow
                   (by
                       rw [← ENNReal.toReal_one]
                       exact
                         (ENNReal.toReal_le_toReal
                           ENNReal.one_ne_top hpTop).mpr hp) hgInt hgPowInt
              have heqPow :
                  ∫ t, |g (x - t)| ^ p.toReal ∂μ =
                    (∫⁻ t,
                        ENNReal.ofReal (ρ t) *
                          (ENNReal.ofReal |g (x - t)|) ^
                            p.toReal).toReal := by
                rw [integral_withDensity_ofReal_eq_integral_mul
                  hρNonneg hρMeas.aemeasurable]
                rw [integral_eq_lintegral_of_nonneg_ae]
                · congr 1
                  apply lintegral_congr
                  intro t
                  rw [ENNReal.ofReal_mul (hρNonneg t)]
                  congr 1
                  rw [← ENNReal.ofReal_rpow_of_nonneg
                    (abs_nonneg _) hpPos.le]
                · exact
                    ae_of_all _ fun t =>
                      mul_nonneg (hρNonneg t)
                        (Real.rpow_nonneg (abs_nonneg _) _)
                · have hAbsPowMeas :
                      Measurable
                        (fun t =>
                          |g (x - t)| ^ p.toReal) := by
                    have hcont :
                        sharedTerm_ed3401cd9d :=
                      continuous_abs.rpow_const
                        (fun _ => Or.inr hpPos.le)
                    exact
                      hcont.measurable.comp
                        (hgMeas.comp
                          (measurable_const.sub measurable_id))
                  exact
                    (hρMeas.mul hAbsPowMeas).aestronglyMeasurable
              calc
                ENNReal.ofReal
                      |∫ t, g (x - t) ∂μ| ^ p.toReal =
                    ENNReal.ofReal
                      (|∫ t, g (x - t) ∂μ| ^ p.toReal) := by
                  rw [← ENNReal.ofReal_rpow_of_nonneg
                    (abs_nonneg _) hpPos.le]
                _ ≤
                    ENNReal.ofReal
                      (∫ t, |g (x - t)| ^ p.toReal ∂μ) :=
                  ENNReal.ofReal_le_ofReal hJensen
                _ =
                    ENNReal.ofReal
                      ((∫⁻ t,
                          ENNReal.ofReal (ρ t) *
                            (ENNReal.ofReal |g (x - t)|) ^
                              p.toReal).toReal) := by
                  rw [heqPow]
                _ ≤
                    ∫⁻ t,
                      ENNReal.ofReal (ρ t) *
                        (ENNReal.ofReal |g (x - t)|) ^ p.toReal :=
                  ENNReal.ofReal_toReal_le
            · have hnotFinite :
                  ∫⁻ t,
                      ENNReal.ofReal (ρ t) *
                        (ENNReal.ofReal |g (x - t)|) ^ p.toReal =
                    ⊤ := by
                have heq :
                    ∫⁻ t,
                        ENNReal.ofReal (ρ t) *
                          (ENNReal.ofReal |g (x - t)|) ^
                            p.toReal =
                      ∫⁻ t,
                        (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                        ∂μ := by
                  have hsub :
                      Measurable (fun t  => x - t) :=
                    measurable_const.sub measurable_id
                  have hAbsMeas :
                      Measurable (fun t => |g (x - t)|) :=
                    continuous_abs.measurable.comp
                      (hgMeas.comp hsub)
                  have hMeasPow  :=
                    Measurable.pow_const
                      hAbsMeas.ennreal_ofReal p.toReal
                  symm
                  convert
                    lintegral_withDensity_eq_lintegral_mul
                      volume hρMeas.ennreal_ofReal hMeasPow
                    using 2
                rw [heq]
                have hAbsPowNonneg :
                    ∀ t, 0 ≤ |g (x - t)| ^ p.toReal :=
                  fun t =>
                    Real.rpow_nonneg (abs_nonneg _) _

                have htop :
                    ∫⁻ t,
                        (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                        ∂μ =
                      ⊤ := by
                  rw [←
                    lintegral_ofReal_ne_top_iff_integrable
                      (show Measurable
                      (fun t => |g (x - t)| ^ p.toReal) by
                          have hcont :
                              sharedTerm_ed3401cd9d :=
                            continuous_abs.rpow_const
                              (fun _ => Or.inr hpPos.le)
                          have hsub :
                              Measurable (fun t  => x - t) :=
                            measurable_const.sub measurable_id
                          exact
                            hcont.measurable.comp (hgMeas.comp hsub)).aestronglyMeasurable
                      (ae_of_all _ hAbsPowNonneg)] at hgPowInt
                  push Not at hgPowInt
                  convert hgPowInt using 1
                  congr 1
                  ext t
                  rw [← ENNReal.ofReal_rpow_of_nonneg
                    (abs_nonneg _) hpPos.le]
                rw [htop]
              simp [hnotFinite]
          · rw [integral_undef hgInt]
            simp only [abs_zero, ENNReal.ofReal_zero]
            rw [ENNReal.zero_rpow_of_pos hpPos]
            exact zero_le)
    _ =
        (∫⁻ t, ENNReal.ofReal (ρ t)) *
          (∫⁻ x,
            (ENNReal.ofReal |g x|) ^ p.toReal) :=
      hfubini
    _ =
        1 *
          (∫⁻ x,
            (ENNReal.ofReal |g x|) ^ p.toReal) := by
      rw [hρLintegralOne]
    _ =
        ∫⁻ x,
          (ENNReal.ofReal |g x|) ^ p.toReal := one_mul _
    _ =
        ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
      congr 1
      ext x
      rw [Real.enorm_eq_ofReal_abs]

private theorem young_convolution_nonneg_integral_one_of_aemeasurable

    (hgMeas : AEMeasurable g ) :
    eLpNorm
        (convolution ρ g
          (ContinuousLinearMap.lsmul ℝ ℝ) )
        p  ≤
      eLpNorm g p  := (Eq.mpr
  (id
    (congrArg (fun _a => eLpNorm _a p volume ≤ eLpNorm g p volume)
      (id (convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) Filter.EventuallyEq.rfl (AEMeasurable.ae_eq_mk hgMeas)))))
  (Trans.trans
    (young_convolution_nonneg_integral_one hp hpTop hρNonneg hρInt hρOne hρMeas (AEMeasurable.measurable_mk hgMeas))
    (eLpNorm_congr_ae (Filter.EventuallyEq.symm (AEMeasurable.ae_eq_mk hgMeas)))))
end


/-- A globally smooth representative of convex-domain approximation. -/
def convexApproxSmoothRepresentative
     (U : Set (Vec d)) (ρ u : Vec d → ℝ)
    (x0 : Vec d) (r ε : ℝ) : Vec d → ℝ :=
  fun x =>
    (scaledConvexApproxKernel ρ (ε * r) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u) ((1 - ε) • x + ε • x0)

variable {U : Set (Vec d)} {ρ u : Vec d → ℝ}

theorem contDiff_convexApproxSmoothRepresentative
      {p : ENNReal}
    (hU : MeasurableSet U)
    (hρ : IsConvexApproxKernel ρ)
    (hp : 1 ≤ p) (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    ContDiff ℝ PDE.smoothOrder
      (convexApproxSmoothRepresentative
        U ρ u x0 r ε) := (ContDiff.comp
  (HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport (mul_pos hε hr))
    (contDiff_scaledConvexApproxKernel hρ (ε * r))
    (MemLp.locallyIntegrable (Eq.mpr (id (congrArg (fun _a => _a) (propext (memLp_indicator_iff_restrict hU)))) hu) hp))
  (ContDiff.add (ContDiff.const_smul (1 - ε) contDiff_id) contDiff_const))

theorem
    convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem

    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    {x0 x : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    convexApproxSmoothRepresentative U ρ u x0 r ε x =
      convexApproxSmoothing ρ u x0 r ε x := (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
      hU hρ hx hball hr hε hεOne).symm

theorem measurableEmbedding_convexApproxSample
     (x0 z : Vec d) (r ε : ℝ)
    (hε : ε < 1) :
    MeasurableEmbedding
      (convexApproxSample x0 z r ε) := by
  let a : ℝ :=
    1 - ε
  let b : Vec d :=
    ε • (x0 - r • z)


  let e  :=
    (Homeomorph.smulOfNeZero a (show 0 < a by
        dsimp only [a]
        linarith).ne').trans
      (Homeomorph.addRight b)
  have heq :
      (fun x  => e x) =
        convexApproxSample x0 z r ε := by
    funext x
    simp [e, a, b, convexApproxSample]
  rw [← heq]
  exact e.toMeasurableEquiv.measurableEmbedding

variable {U : Set (Vec d)}

theorem map_restrict_convexApproxSample

    (_hU : MeasurableSet U)
    (x0 z : Vec d) (r ε : ℝ) (hε : ε < 1) :
    Measure.map (convexApproxSample x0 z r ε)
        (volume.restrict U) =
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
        volume.restrict
          (convexApproxSample x0 z r ε '' U) := by
  let a : ℝ :=
    1 - ε
  let b : Vec d :=
    ε • (x0 - r • z)

  have haNe  :=
    (show 0 < a by
        dsimp only [a]
        linarith).ne'
  let e  :=
    (Homeomorph.smulOfNeZero a haNe).trans
      (Homeomorph.addRight b)


  have hmapVolume :
      Measure.map (convexApproxSample x0 z r ε) volume =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
          volume := by
    have hmapSmul :
        Measure.map (fun x : Vec d => a • x) volume =
          ENNReal.ofReal ((a ^ d)⁻¹) • volume := by

      let f  :=
        a • (1 : Vec d →ₗ[ℝ] Vec d)

      have hdet : LinearMap.det f = a ^ d := by
        simp [f]
      have hmapf :=
        Real.map_linearMap_volume_pi_eq_smul_volume_pi
            (show LinearMap.det f ≠ 0 by
                simp [f, haNe])
      have hpowInvNonneg : 0 ≤ (a ^ d)⁻¹ := by
        positivity
      rw [hdet] at hmapf
      have hfun : (fun x : Vec d => a • x) = ⇑f := by
        funext x
        simp [f]
      rw [hfun]
      simpa only [abs_of_nonneg hpowInvNonneg] using
        hmapf
    calc
      Measure.map (convexApproxSample x0 z r ε) volume =
          (Measure.map (fun x : Vec d => a • x)
            volume).map
              (fun y  => y + b) := by
        rw [Measure.map_map
            (μ := volume)
            (g := fun y : Vec d => y + b)
            (f := fun x  => a • x)
            (measurable_id.add measurable_const)
            (measurable_const_smul a)]
        rfl
      _ =
          Measure.map (fun y  => y + b)
            (ENNReal.ofReal ((a ^ d)⁻¹) • volume) := by
        rw [hmapSmul]
      _ =
          ENNReal.ofReal ((a ^ d)⁻¹) •
            Measure.map (fun y  => y + b)
              volume := by
        rw [Measure.map_smul (f := fun y  => y + b) _
          (measurable_add_const b).aemeasurable]
      _ =
          ENNReal.ofReal ((a ^ d)⁻¹) • volume := by
        rw [map_add_right_eq_self]
      _ =
          ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
            volume := rfl
  calc
    Measure.map (convexApproxSample x0 z r ε)
        (volume.restrict U) =
      (Measure.map (convexApproxSample x0 z r ε)
        volume).restrict
          (convexApproxSample x0 z r ε '' U) :=
      (show Measure.map (convexApproxSample x0 z r ε)
          (volume.restrict U) =
        (Measure.map (convexApproxSample x0 z r ε)
          volume).restrict
            (convexApproxSample x0 z r ε '' U) by
          have htmp :
              (volume.restrict U).map e =
                (volume.map e).restrict (e '' U) := by
            have h :=
              ((e.toMeasurableEquiv.restrict_map
                (μ := volume) (s := e '' U)).symm)
            simpa [Set.preimage_image_eq _ e.injective] using h
          assumption)
    _ =
        (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
          volume).restrict
            (convexApproxSample x0 z r ε '' U) := by
      rw [hmapVolume]
    _ =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
          volume.restrict
            (convexApproxSample x0 z r ε '' U) := by
      rw [Measure.restrict_smul]

theorem eLpNorm_comp_convexApproxSample_le

    {u : Vec d → ℝ} {p : ENNReal}
    (hp : p ≠ ⊤) (hU : MeasurableSet U)
    (x0 z : Vec d) (r ε : ℝ) (hε : ε < 1)
    (hmap :
      convexApproxSample x0 z r ε '' U ⊆ U) :
    eLpNorm
        (fun x => u (convexApproxSample x0 z r ε x))
        p (volume.restrict U) ≤
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
          (1 / p).toReal *
        eLpNorm u p (volume.restrict U) := by
  let sharedTerm_623cbe13ce := (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal)
  by_cases huMeas : AEStronglyMeasurable u (volume.restrict U)
  swap
  · have hc : sharedTerm_623cbe13ce ≠ 0 :=
      (ENNReal.rpow_pos
        (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos (sub_pos.2 hε) d)))
        ENNReal.ofReal_ne_top).ne'
    rw [eLpNorm_of_not_aestronglyMeasurable huMeas, ENNReal.mul_top hc]
    exact le_top
  calc
    eLpNorm
        (fun x => u (convexApproxSample x0 z r ε x))
        p (volume.restrict U) =
      eLpNorm u p
        (Measure.map
          (convexApproxSample x0 z r ε)
          (volume.restrict U)) := by
      symm
      exact
        (measurableEmbedding_convexApproxSample
          x0 z r ε hε).eLpNorm_map_measure
    _ =
        eLpNorm u p
          (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
            volume.restrict
              (convexApproxSample x0 z r ε '' U)) := by
      rw [map_restrict_convexApproxSample
        hU x0 z r ε hε]
    _ =
        sharedTerm_623cbe13ce •
          eLpNorm u p
            (volume.restrict
              (convexApproxSample x0 z r ε '' U)) := by
      rw [eLpNorm_smul_measure_of_ne_top hp _ _
        (huMeas.mono_measure (Measure.restrict_mono_set volume hmap))]
    _ ≤
        sharedTerm_623cbe13ce •
          eLpNorm u p (volume.restrict U) := by
      gcongr <;> first | positivity | assumption | norm_num
    _ =
        sharedTerm_623cbe13ce *
          eLpNorm u p (volume.restrict U) := by
      rw [smul_eq_mul]

theorem eLpNorm_convexApproxSmoothing_le

    {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    eLpNorm (convexApproxSmoothing ρ u x0 r ε)
        p (volume.restrict U) ≤
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
          (1 / p).toReal *
        eLpNorm u p (volume.restrict U) := by
  let sharedTerm_5047b8f910 := (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal)
  let g : Vec d → ℝ :=
    scaledConvexApproxKernel ρ (ε * r) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u
  have hUMeas  :=
    hU.isOpen.measurableSet
  have hmapZeroMapsTo :
      Set.MapsTo
        (convexApproxSample x0 0 r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr.le (by simp) hε.le (le_of_lt hεOne)


  have hεr : 0 < ε * r := by
    positivity


  calc
    eLpNorm (convexApproxSmoothing ρ u x0 r ε)
        p (volume.restrict U) =
      eLpNorm
        (fun x =>
          g (convexApproxSample x0 0 r ε x))
        p (volume.restrict U) :=
      eLpNorm_congr_ae (by
          filter_upwards [ae_restrict_mem hUMeas] with x hx
          simpa [g, convexApproxSample] using
            (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
              (u := u)
              hU hρ hx hball hr hε hεOne))
    _ ≤
        sharedTerm_5047b8f910 *
          eLpNorm g p (volume.restrict U) :=
      eLpNorm_comp_convexApproxSample_le
        hpTop hUMeas x0 0 r ε hεOne (by
            intro y hy
            rcases hy with ⟨x, hx, rfl⟩
            exact hmapZeroMapsTo hx)
    _ ≤
        sharedTerm_5047b8f910 *
          eLpNorm g p  :=
      mul_le_mul' le_rfl
        (eLpNorm_mono_measure g
          Measure.restrict_le_self)
    _ ≤
        sharedTerm_5047b8f910 *
          eLpNorm (Set.indicator U u) p  :=
      mul_le_mul' le_rfl (by
          dsimp only [g]
          exact
            young_convolution_nonneg_integral_one_of_aemeasurable
               hpOne hpTop
              (scaledConvexApproxKernel_nonneg hρ hεr)
              (integrable_scaledConvexApproxKernel hρ hεr)
              (integral_scaledConvexApproxKernel hρ hεr)
              (measurable_scaledConvexApproxKernel
                hρ.continuous (ε * r))
              (show MemLp (Set.indicator U u) p by
                  rw [memLp_indicator_iff_restrict hUMeas]
                  exact hu).aestronglyMeasurable.aemeasurable)
    _ =
        sharedTerm_5047b8f910 *
          eLpNorm u p (volume.restrict U) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hUMeas]

variable {ρ u v : Vec d → ℝ} {p : ENNReal} (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ)

include hU hρ
theorem convexApproxSmoothing_sub_ae_eq


    (hp : 1 ≤ p)
    (hu : MemLpOn U p u) (hv : MemLpOn U p v)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    ((convexApproxSmoothing ρ (fun y => u y - v y) x0 r ε)) =ᵐ[
          volume.restrict U]
      fun x =>
        convexApproxSmoothing ρ u x0 r ε x -
          convexApproxSmoothing ρ v x0 r ε x := by
  let k  :=
    scaledConvexApproxKernel ρ (ε * r)
  let gu : Vec d → ℝ :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u
  let gv  :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U v
  let gw  :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U (fun y => u y - v y)
  have hUMeas  :=
    hU.isOpen.measurableSet

  have hkContinuous : Continuous k := by
    dsimp only [k]
    exact
      continuous_scaledConvexApproxKernel
        hρ.continuous (ε * r)
  have hkCompact : HasCompactSupport k := by
    dsimp only [k]
    exact
      hasCompactSupport_scaledConvexApproxKernel
        hρ.compactSupport (by
            positivity)

  have hvIndicator :
      MemLp (Set.indicator U v) p  := by
    rw [memLp_indicator_iff_restrict hUMeas]
    exact hv



  have hconvU :
      ConvolutionExists k (Set.indicator U u)
        (ContinuousLinearMap.lsmul ℝ ℝ)  :=
    hkCompact.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hkContinuous ((show MemLp (Set.indicator U u) p by
          rw [memLp_indicator_iff_restrict hUMeas]
          exact hu).locallyIntegrable hp)
  have hconvNegV :
      ConvolutionExists k
        ((-1 : ℝ) • Set.indicator U v)
        (ContinuousLinearMap.lsmul ℝ ℝ)  :=
    hkCompact.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hkContinuous (by
          simpa using (hvIndicator.locallyIntegrable hp).smul (-1 : ℝ))
  have hindicatorSub :
      Set.indicator U (fun y => u y - v y) =
        Set.indicator U u +
          (-1 : ℝ) • Set.indicator U v := by
    funext x
    by_cases hx : x ∈ U
    · simp [hx, sub_eq_add_neg]
    · simp [hx]
  have hconvSub :
      gw = fun x => gu x - gv x := by
    ext x
    dsimp only [gw, gu, gv]
    rw [hindicatorSub,
      hconvU.distrib_add hconvNegV, convolution_smul]
    simp [sub_eq_add_neg]
  filter_upwards [ae_restrict_mem hUMeas] with x hx
  have huRepresentative :
      convexApproxSmoothing ρ u x0 r ε x =
        gu (convexApproxSample x0 0 r ε x) := by
    simpa [gu, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := u) hU hρ hx hball hr hε hεOne)
  have hvRepresentative :
      convexApproxSmoothing ρ v x0 r ε x =
        gv (convexApproxSample x0 0 r ε x) := by
    simpa [gv, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := v) hU hρ hx hball hr hε hεOne)
  have hwRepresentative :
      convexApproxSmoothing ρ
          (fun y => u y - v y) x0 r ε x =
        gw (convexApproxSample x0 0 r ε x) := by
    simpa [gw, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := fun y => u y - v y)
        hU hρ hx hball hr hε hεOne)
  rw [huRepresentative, hvRepresentative, hwRepresentative]
  rw [hconvSub]

theorem eLpNorm_sub_convexApproxSmoothing_le


    (hpOne : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hu : MemLpOn U p u) (hv : MemLpOn U p v)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    eLpNorm
        (fun x =>
          convexApproxSmoothing ρ u x0 r ε x -
            convexApproxSmoothing ρ v x0 r ε x)
        p (volume.restrict U) ≤
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
          (1 / p).toReal *
        eLpNorm (fun x => u x - v x)
          p (volume.restrict U) := (Trans.trans
  (eLpNorm_congr_ae (Filter.EventuallyEq.symm (convexApproxSmoothing_sub_ae_eq hU hρ hpOne hu hv hball hr hε hεOne)))
  (eLpNorm_convexApproxSmoothing_le hU hρ hpOne hpTop (MemLp.sub hu hv) hball hr hε hεOne))

end

end PDE
