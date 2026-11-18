module

public import PDEFoundation.Measure.Jensen
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Kernel
public import Mathlib.MeasureTheory.Integral.Prod
public import PDEFoundation.Measure.AffineVolume
public import PDEFoundation.Sobolev.WeakDerivative
public import PDEFoundation.Sobolev.WeakDerivative.Algebra

@[expose] public noncomputable section

namespace PDE
open MeasureTheory
open scoped ENNReal Pointwise Convolution



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



private theorem integral_withDensity_ofReal_eq_integral_mul
    {d : ℕ} {f g : Vec d → ℝ}
    (hfNonneg : ∀ x, 0 ≤ f x)
    (hfMeas : AEMeasurable f volume) :
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


private theorem young_convolution_nonneg_integral_one_of_aemeasurable
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal}
    (hp : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hρNonneg : ∀ x, 0 ≤ ρ x)
    (hρInt : Integrable ρ volume)
    (hρOne : ∫ x, ρ x = 1)
    (hρMeas : Measurable ρ)
    (hgMeas : AEMeasurable g volume) :
    eLpNorm
        (convolution ρ g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        p volume ≤
      eLpNorm g p volume  := by
  have young_convolution_nonneg_integral_one {ρ g : Vec d → ℝ} (hρNonneg : ∀ x, 0 ≤ ρ x) (hρInt : Integrable ρ volume) (hρOne : ∫ x, ρ x = 1) (hρMeas : Measurable ρ) (hgMeas : Measurable g) :
      eLpNorm
        (convolution ρ g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        p volume ≤
      eLpNorm g p volume := by
    have fubini_translation_key {d : ℕ} (ρ : Vec d → ℝ≥0∞) (g : Vec d → ℝ) (p : ℝ) (hρ : Measurable ρ) (hg : Measurable g) :
        ∫⁻ x, ∫⁻ t,
          ρ t * (ENNReal.ofReal |g (x - t)|) ^ p
            ∂volume ∂volume =
        (∫⁻ t, ρ t ∂volume) *
          (∫⁻ x, (ENNReal.ofReal |g x|) ^ p
            ∂volume) := by
      have lintegral_comp_sub_right {d : ℕ} (f : Vec d → ℝ≥0∞) (hf : Measurable f) (t : Vec d) :
          ∫⁻ x, f (x - t) ∂(volume : Measure (Vec d)) =
          ∫⁻ x, f x ∂(volume : Measure (Vec d)) := by
        have heq :
            (fun x => f (x - t)) =
              f ∘ ((· + (-t)) : Vec d → Vec d) := by
          funext x
          simp [sub_eq_add_neg]
        rw [heq, lintegral_comp hf (measurable_add_const (-t))]
        have hmap :
            Measure.map (fun x => x + (-t))
                (volume : Measure (Vec d)) =
              volume := by
          simpa using
            (map_add_right_eq_self
              (μ := (volume : Measure (Vec d))) (-t))
        rw [hmap]
      have hswap :
          ∫⁻ x, ∫⁻ t,
              ρ t * (ENNReal.ofReal |g (x - t)|) ^ p
                ∂volume ∂volume =
            ∫⁻ t, ∫⁻ x,
              ρ t * (ENNReal.ofReal |g (x - t)|) ^ p
                ∂volume ∂volume := by
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
              ρ t * (ENNReal.ofReal |g (x - t)|) ^ p
                ∂volume ∂volume =
            ∫⁻ t, ρ t *
              ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p
                ∂volume ∂volume := by
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
              ∫⁻ x, (ENNReal.ofReal |g x|) ^ p
                ∂volume := by
        intro t
        exact
          lintegral_comp_sub_right _
            (Measurable.pow_const
              (ENNReal.measurable_ofReal.comp
                (continuous_abs.measurable.comp hg)) p) t
      simp_rw [htrans]
      rw [lintegral_mul_const _ hρ, mul_comm]
    have hpNeZero :=
      ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
    have hpPos :=
      ENNReal.toReal_pos hpNeZero hpTop
    have hpOne : 1 ≤ p.toReal := by
      rw [← ENNReal.toReal_one]
      exact
        (ENNReal.toReal_le_toReal
          ENNReal.one_ne_top hpTop).mpr hp
    let μ : Measure (Vec d) :=
      volume.withDensity fun t => ENNReal.ofReal (ρ t)
    let _ :=
      isProbabilityMeasure_withDensity_ofReal
        hρNonneg hρInt hρOne
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpNeZero hpTop
      (hρMeas.aestronglyMeasurable.convolution
        (ContinuousLinearMap.lsmul ℝ ℝ) hgMeas.aestronglyMeasurable)]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpNeZero hpTop
      hgMeas.aestronglyMeasurable]
    apply ENNReal.rpow_le_rpow _
      (by positivity : 0 ≤ 1 / p.toReal)
    have hρLintegralOne :
        ∫⁻ t, ENNReal.ofReal (ρ t) ∂volume = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hρInt
        (ae_of_all _ hρNonneg), hρOne]
      simp
    have hpointwise :
        ∀ x,
          ‖convolution ρ g
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^
              p.toReal ≤
            ∫⁻ t,
              ENNReal.ofReal (ρ t) *
                (ENNReal.ofReal |g (x - t)|) ^ p.toReal
              ∂volume := by
      intro x
      rw [convolution_def]
      simp
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
              (μ := μ) hpOne hgInt hgPowInt
          have heqPow :
              ∫ t, |g (x - t)| ^ p.toReal ∂μ =
                (∫⁻ t,
                    ENNReal.ofReal (ρ t) *
                      (ENNReal.ofReal |g (x - t)|) ^
                        p.toReal
                    ∂volume).toReal := by
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
                have hcont :=
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
                          p.toReal
                      ∂volume).toReal) := by
              rw [heqPow]
            _ ≤
                ∫⁻ t,
                  ENNReal.ofReal (ρ t) *
                    (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                  ∂volume :=
              ENNReal.ofReal_toReal_le
        · have hnotFinite :
              ∫⁻ t,
                  ENNReal.ofReal (ρ t) *
                    (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                  ∂volume =
                ⊤ := by
            have heq :
                ∫⁻ t,
                    ENNReal.ofReal (ρ t) *
                      (ENNReal.ofReal |g (x - t)|) ^
                        p.toReal
                    ∂volume =
                  ∫⁻ t,
                    (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                    ∂μ := by
              have hsub :
                  Measurable (fun t => x - t) :=
                measurable_const.sub measurable_id
              have hMeasPow :
                  Measurable
                    (fun t =>
                      (ENNReal.ofReal |g (x - t)|) ^
                        p.toReal) :=
                Measurable.pow_const
                  (continuous_abs.measurable.comp (hgMeas.comp hsub)).ennreal_ofReal p.toReal
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
            have hAbsPowMeas :
                Measurable
                  (fun t => |g (x - t)| ^ p.toReal) := by
              have hsub :
                  Measurable (fun t => x - t) :=
                measurable_const.sub measurable_id
              exact
                (continuous_abs.rpow_const (fun _ => Or.inr hpPos.le)).measurable.comp (hgMeas.comp hsub)
            have htop :
                ∫⁻ t,
                    (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                    ∂μ =
                  ⊤ := by
              rw [←
                lintegral_ofReal_ne_top_iff_integrable
                  hAbsPowMeas.aestronglyMeasurable
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
        simp
        rw [ENNReal.zero_rpow_of_pos hpPos]
        exact zero_le
    calc
      ∫⁻ x,
          ‖convolution ρ g
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^
            p.toReal
          ∂volume ≤
        ∫⁻ x, ∫⁻ t,
            ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal
            ∂volume ∂volume :=
        lintegral_mono hpointwise
      _ =
          (∫⁻ t, ENNReal.ofReal (ρ t) ∂volume) *
            (∫⁻ x,
              (ENNReal.ofReal |g x|) ^ p.toReal
              ∂volume) :=
        (fubini_translation_key (fun t => ENNReal.ofReal (ρ t)) g p.toReal hρMeas.ennreal_ofReal hgMeas)
      _ =
          1 *
            (∫⁻ x,
              (ENNReal.ofReal |g x|) ^ p.toReal
              ∂volume) := by
        rw [hρLintegralOne]
      _ =
          ∫⁻ x,
            (ENNReal.ofReal |g x|) ^ p.toReal
            ∂volume := one_mul _
      _ =
          ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂volume := by
        congr 1
        ext x
        rw [Real.enorm_eq_ofReal_abs]
  let g' :=
    hgMeas.mk g
  have hconv :
      convolution ρ g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume =
        convolution ρ g'
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    simpa [g'] using
      (convolution_congr
        (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := (volume : Measure (Vec d)))
        (h1 := Filter.EventuallyEq.rfl)
        (h2 := hgMeas.ae_eq_mk))
  rw [hconv]
  calc
    eLpNorm
          (convolution ρ g'
            (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          p volume ≤
        eLpNorm g' p volume :=
      young_convolution_nonneg_integral_one hρNonneg hρInt hρOne hρMeas
        hgMeas.measurable_mk
    _ = eLpNorm g p volume :=
      eLpNorm_congr_ae hgMeas.ae_eq_mk.symm

/-- A globally smooth representative of convex-domain approximation. -/
noncomputable def convexApproxSmoothRepresentative
    {d : ℕ} (U : Set (Vec d)) (ρ u : Vec d → ℝ)
    (x0 : Vec d) (r ε : ℝ) : Vec d → ℝ :=
  fun x =>
    (scaledConvexApproxKernel ρ (ε * r) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u) ((1 - ε) • x + ε • x0)

theorem contDiff_convexApproxSmoothRepresentative
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : MeasurableSet U)
    (hρ : IsConvexApproxKernel ρ)
    (hp : 1 ≤ p) (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
      (convexApproxSmoothRepresentative
        U ρ u x0 r ε) := by
  have hεr : 0 < ε * r := by
    positivity
  have huIndicator :
      MemLp (Set.indicator U u) p volume := by
    rw [memLp_indicator_iff_restrict hU]
    exact hu
  have hconv :=
    HasCompactSupport.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := volume)
      (f := scaledConvexApproxKernel ρ (ε * r))
      (g := Set.indicator U u)
      (hasCompactSupport_scaledConvexApproxKernel
        hρ.compactSupport hεr)
      (contDiff_scaledConvexApproxKernel hρ (ε * r))
      (huIndicator.locallyIntegrable hp)
  have haffine :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun x =>
          (1 - ε) • x + ε • x0) := by
    exact
      ((contDiff_id :
          ContDiff ℝ (⊤ : ℕ∞)
            (fun x => x)).const_smul (1 - ε)).add contDiff_const
  exact hconv.comp haffine

theorem
    convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    {x0 x : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    convexApproxSmoothRepresentative U ρ u x0 r ε x =
      convexApproxSmoothing ρ u x0 r ε x := by
  simpa only [convexApproxSmoothRepresentative] using
    (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
      hU hρ hx hball hr hε hεOne).symm



theorem eLpNorm_comp_convexApproxSample_le
    {d : ℕ} {U : Set (Vec d)}
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
        eLpNorm u p (volume.restrict U)   := by
  have map_restrict_convexApproxSample {U : Set (Vec d)} (_hU : MeasurableSet U) (r ε : ℝ) (hε : ε < 1) :
      Measure.map (convexApproxSample x0 z r ε)
        (volume.restrict U) =
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
        volume.restrict
          (convexApproxSample x0 z r ε '' U) := by
    let a : ℝ :=
      1 - ε
    let b :=
      ε • (x0 - r • z)
    have haPos : 0 < a := by
      linarith
    have haNe :=
      haPos.ne'
    let e :=
      (Homeomorph.smulOfNeZero a haNe).trans
        (Homeomorph.addRight b)
    have heq :
        (fun x => e x) =
          convexApproxSample x0 z r ε := by
      funext x
      simp [e, a, b, convexApproxSample]
    have hrestrict :
        Measure.map (convexApproxSample x0 z r ε)
            (volume.restrict U) =
          (Measure.map (convexApproxSample x0 z r ε)
            volume).restrict
              (convexApproxSample x0 z r ε '' U) := by
      have htmp :
          (volume.restrict U).map e =
            (volume.map e).restrict (e '' U) := by
        simpa [Set.preimage_image_eq _ e.injective] using ((e.toMeasurableEquiv.restrict_map (μ := volume) (s := e '' U)).symm)
      simpa [heq] using htmp
    have hmapVolume :
        Measure.map (convexApproxSample x0 z r ε) volume =
          ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
            volume := by
      have hmapSmul :
          Measure.map (fun x : Vec d => a • x) volume =
            ENNReal.ofReal ((a ^ d)⁻¹) • volume := by
        have hpowNonneg : 0 ≤ a ^ d := by
          positivity
        let f :=
          a • (1 : Vec d →ₗ[ℝ] Vec d)
        have hf : LinearMap.det f ≠ 0 := by
          simp [f, haNe]
        have hdet : LinearMap.det f = a ^ d := by
          simp [f]
        have hmapf :=
          Real.map_linearMap_volume_pi_eq_smul_volume_pi
            (ι := Fin d) (f := f) hf
        have hpowInvNonneg : 0 ≤ (a ^ d)⁻¹ := by
          positivity
        rw [hdet] at hmapf
        have hfun : (fun x => a • x) = ⇑f := by
          funext x
          simp [f]
        rw [hfun]
        simpa only [abs_of_nonneg hpowInvNonneg] using
          hmapf
      calc
        Measure.map (convexApproxSample x0 z r ε) volume =
            (Measure.map (fun x => a • x)
              volume).map
                (fun y => y + b) := by
          rw [Measure.map_map
              (μ := volume)
              (g := fun y => y + b)
              (f := fun x => a • x)
              (measurable_id.add measurable_const)
              (measurable_const_smul a)]
          rfl
        _ =
            Measure.map (fun y => y + b)
              (ENNReal.ofReal ((a ^ d)⁻¹) • volume) := by
          rw [hmapSmul]
        _ =
            ENNReal.ofReal ((a ^ d)⁻¹) •
              Measure.map (fun y => y + b)
                volume := by
          rw [Measure.map_smul (f := fun y => y + b) _
            (measurable_add_const b).aemeasurable]
        _ =
            ENNReal.ofReal ((a ^ d)⁻¹) • volume := by
          rw [map_add_right_eq_self]
        _ =
            ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
              volume := by
          simp only [a]
    calc
      Measure.map (convexApproxSample x0 z r ε)
          (volume.restrict U) =
        (Measure.map (convexApproxSample x0 z r ε)
          volume).restrict
            (convexApproxSample x0 z r ε '' U) :=
        hrestrict
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
  have measurableEmbedding_convexApproxSample (r ε : ℝ) (hε : ε < 1) :
      MeasurableEmbedding
      (convexApproxSample x0 z r ε) := by
    let a : ℝ :=
      1 - ε
    let b :=
      ε • (x0 - r • z)
    have haPos : 0 < a := by
      linarith
    let e :=
      (Homeomorph.smulOfNeZero a haPos.ne').trans
        (Homeomorph.addRight b)
    have heq :
        (fun x => e x) =
          convexApproxSample x0 z r ε := by
      funext x
      simp [e, a, b, convexApproxSample]
    rw [← heq]
    exact e.toMeasurableEquiv.measurableEmbedding
  by_cases huMeas : AEStronglyMeasurable u (volume.restrict U)
  swap
  · have hc : ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal ≠ 0 :=
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
        (measurableEmbedding_convexApproxSample r ε hε).eLpNorm_map_measure
    _ =
        eLpNorm u p
          (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
            volume.restrict
              (convexApproxSample x0 z r ε '' U)) := by
      rw [map_restrict_convexApproxSample
        hU r ε hε]
    _ =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal •
          eLpNorm u p
            (volume.restrict
              (convexApproxSample x0 z r ε '' U)) := by
      rw [eLpNorm_smul_measure_of_ne_top hp _ _
        (huMeas.mono_measure (Measure.restrict_mono_set volume hmap))]
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal •
          eLpNorm u p (volume.restrict U) := by
      exact
        smul_le_smul_of_nonneg_left
          (eLpNorm_mono_measure u
            (Measure.restrict_mono_set volume hmap))
          (by positivity)
    _ =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm u p (volume.restrict U) := by
      rw [smul_eq_mul]

theorem eLpNorm_convexApproxSmoothing_le
    {d : ℕ} {U : Set (Vec d)}
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
  let g :=
    scaledConvexApproxKernel ρ (ε * r) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u
  have hUMeas :=
    hU.isOpen.measurableSet
  have hmapZeroMapsTo :
      Set.MapsTo
        (convexApproxSample x0 0 r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr.le (by simp) hε.le (le_of_lt hεOne)
  have hmapZero :
      convexApproxSample x0 0 r ε '' U ⊆ U := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hmapZeroMapsTo hx
  have hrepresentative :
      (fun x =>
        convexApproxSmoothing ρ u x0 r ε x) =ᵐ[
          volume.restrict U]
        fun x =>
          g (convexApproxSample x0 0 r ε x) := by
    filter_upwards [ae_restrict_mem hUMeas] with x hx
    simpa [g, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := u)
        hU hρ hx hball hr hε hεOne)
  have hεr : 0 < ε * r := by
    positivity
  have huIndicator :
      MemLp (Set.indicator U u) p volume := by
    rw [memLp_indicator_iff_restrict hUMeas]
    exact hu
  have hconv :
      eLpNorm g p volume ≤
        eLpNorm (Set.indicator U u) p volume := by
    exact
      young_convolution_nonneg_integral_one_of_aemeasurable
        (d := d) hpOne hpTop
        (scaledConvexApproxKernel_nonneg hρ hεr)
        (integrable_scaledConvexApproxKernel hρ hεr)
        (integral_scaledConvexApproxKernel hρ hεr)
        (measurable_scaledConvexApproxKernel
          hρ.continuous (ε * r))
        huIndicator.aestronglyMeasurable.aemeasurable
  calc
    eLpNorm (convexApproxSmoothing ρ u x0 r ε)
        p (volume.restrict U) =
      eLpNorm
        (fun x =>
          g (convexApproxSample x0 0 r ε x))
        p (volume.restrict U) :=
      eLpNorm_congr_ae hrepresentative
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm g p (volume.restrict U) :=
      eLpNorm_comp_convexApproxSample_le
        hpTop hUMeas x0 0 r ε hεOne hmapZero
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm g p volume :=
      mul_le_mul' le_rfl
        (eLpNorm_mono_measure g
          Measure.restrict_le_self)
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm (Set.indicator U u) p volume :=
      mul_le_mul' le_rfl hconv
    _ =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm u p (volume.restrict U) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hUMeas]

theorem convexApproxSmoothing_sub_ae_eq
    {d : ℕ} {U : Set (Vec d)}
    {ρ u v : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    (hp : 1 ≤ p)
    (hu : MemLpOn U p u) (hv : MemLpOn U p v)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    (fun x =>
      convexApproxSmoothing ρ
        (fun y => u y - v y) x0 r ε x) =ᵐ[
          volume.restrict U]
      fun x =>
        convexApproxSmoothing ρ u x0 r ε x -
          convexApproxSmoothing ρ v x0 r ε x := by
  let k :=
    scaledConvexApproxKernel ρ (ε * r)
  let gu :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u
  let gv :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U v
  let gw :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U (fun y => u y - v y)
  have hUMeas :=
    hU.isOpen.measurableSet
  have hεr : 0 < ε * r := by
    positivity
  have hkContinuous : Continuous k := by
    exact
      continuous_scaledConvexApproxKernel
        hρ.continuous (ε * r)
  have hkCompact : HasCompactSupport k := by
    exact
      hasCompactSupport_scaledConvexApproxKernel
        hρ.compactSupport hεr
  have huIndicator :
      MemLp (Set.indicator U u) p volume := by
    rw [memLp_indicator_iff_restrict hUMeas]
    exact hu
  have hvIndicator :
      MemLp (Set.indicator U v) p volume := by
    rw [memLp_indicator_iff_restrict hUMeas]
    exact hv
  have hnegvLocallyIntegrable :
      LocallyIntegrable
        ((-1 : ℝ) • Set.indicator U v) volume := by
    simpa using (hvIndicator.locallyIntegrable hp).smul (-1 : ℝ)
  have hconvU :=
    hkCompact.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hkContinuous (huIndicator.locallyIntegrable hp)
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
      hconvU.distrib_add (hkCompact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hkContinuous hnegvLocallyIntegrable), convolution_smul]
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
    {d : ℕ} {U : Set (Vec d)}
    {ρ u v : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
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
          p (volume.restrict U) := by
  calc
    eLpNorm
        (fun x =>
          convexApproxSmoothing ρ u x0 r ε x -
            convexApproxSmoothing ρ v x0 r ε x)
        p (volume.restrict U) =
      eLpNorm
        (convexApproxSmoothing ρ
          (fun y => u y - v y) x0 r ε)
        p (volume.restrict U) := by
      exact
        eLpNorm_congr_ae
          (convexApproxSmoothing_sub_ae_eq
            hU hρ hpOne hu hv
            hball hr hε hεOne).symm
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm (fun x => u x - v x)
            p (volume.restrict U) :=
      eLpNorm_convexApproxSmoothing_le
        hU hρ hpOne hpTop (hu.sub hv) hball hr hε hεOne



namespace HasWeakPartialDerivOn

/-- Translate a weak partial derivative from `U` to `z + U`. -/
theorem translate {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u gi : Vec d → ℝ} (h : HasWeakPartialDerivOn U i u gi)
    (z : Vec d) :
    HasWeakPartialDerivOn (translateSet z U) i
      (fun x => u (x - z)) (fun x => gi (x - z)) := by
  intro φ hφSmooth hφCompact hφSubset
  let V := translateSet z U
  let ψ : Vec d → ℝ := fun x => φ (x + z)
  have hψSmooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ] using!
      hφSmooth.comp (contDiff_id.add contDiff_const)
  have hψCompact : HasCompactSupport ψ := by
    show HasCompactSupport (φ ∘ Homeomorph.addRight z)
    simpa [ψ, Function.comp] using
      hφCompact.comp_homeomorph (Homeomorph.addRight z)
  have hψSubset : tsupport ψ ⊆ U := by
    intro x hx
    have hx' : x + z ∈ tsupport φ := by
      rw [show ψ = φ ∘ Homeomorph.addRight z by rfl,
        tsupport_comp_eq_preimage φ (Homeomorph.addRight z)] at hx
      exact hx
    simpa [V, mem_translateSet_iff_sub_mem, sub_eq_add_neg,
      add_assoc] using (hφSubset hx')
  have hMain :
      ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i)
          ∂MeasureTheory.volume =
        -∫ x in U, gi x * φ (x + z) ∂MeasureTheory.volume := by
    have hfun :
        (fun x => u x * (fderiv ℝ φ (x + z)) (basisVec i)) =
          fun x => u x * (fderiv ℝ ψ x) (basisVec i) := by
      funext x
      have hderiv :
          fderiv ℝ (fun y => φ (y + z)) x =
            fderiv ℝ φ (x + z) := by
        simpa using
          (fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := x) z)
      simp [ψ, hderiv]
    calc
      ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i)
          ∂MeasureTheory.volume =
          ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec i)
            ∂MeasureTheory.volume := by
              rw [hfun]
      _ = -∫ x in U, gi x * ψ x ∂MeasureTheory.volume := (h ψ hψSmooth hψCompact hψSubset)
      _ = -∫ x in U, gi x * φ (x + z)
          ∂MeasureTheory.volume := rfl
  have hChangeLeft :
      ∫ x in V, u (x - z) * (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume =
        ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i)
          ∂MeasureTheory.volume := by
    symm
    simpa [V, sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) z U
        (fun x => u (x - z) * (fderiv ℝ φ x) (basisVec i)))
  have hChangeRight :
      ∫ x in U, gi x * φ (x + z) ∂MeasureTheory.volume =
        ∫ x in V, gi (x - z) * φ x ∂MeasureTheory.volume := by
    simpa [V, sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) z U
        (fun x => gi (x - z) * φ x))
  calc
    ∫ x in V, u (x - z) * (fderiv ℝ φ x) (basisVec i)
        ∂MeasureTheory.volume =
        ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i)
          ∂MeasureTheory.volume := hChangeLeft
    _ = -∫ x in U, gi x * φ (x + z)
        ∂MeasureTheory.volume := hMain
    _ = -∫ x in V, gi (x - z) * φ x
        ∂MeasureTheory.volume := by rw [hChangeRight]

/-- Push a weak partial derivative to `a • U` by the amplitude-normalized
dilation

`v(x) = a * u(a⁻¹ • x)`, `Dᵢv(x) = gi(a⁻¹ • x)`.

The positivity hypothesis fixes the geometric orientation and every
change-of-variables factor. -/
theorem dilate_of_pos {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u gi : Vec d → ℝ} (h : HasWeakPartialDerivOn U i u gi)
    {a : ℝ} (ha : 0 < a) :
    HasWeakPartialDerivOn (a • U) i
      (fun x => a * u (a⁻¹ • x))
      (fun x => gi (a⁻¹ • x)) := by
  intro φ hφSmooth hφCompact hφSubset
  let V := a • U
  let T : Vec d → Vec d := fun x => a⁻¹ • x
  have haNe := ha.ne'
  let ψ : Vec d → ℝ := fun y => φ (a • y)
  have hψSmooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ] using! hφSmooth.comp (contDiff_const_smul a)
  have hψCompact : HasCompactSupport ψ := by
    show HasCompactSupport (φ ∘ Homeomorph.smulOfNeZero a haNe)
    simpa [ψ, Function.comp] using
      hφCompact.comp_homeomorph (Homeomorph.smulOfNeZero a haNe)
  have hψSubset : tsupport ψ ⊆ U := by
    intro y hy
    have hy' : a • y ∈ tsupport φ := by
      rw [show ψ = φ ∘ Homeomorph.smulOfNeZero a haNe by rfl,
        tsupport_comp_eq_preimage φ
          (Homeomorph.smulOfNeZero a haNe)] at hy
      exact hy
    simpa [V, Set.mem_smul_set_iff_inv_smul_mem, haNe] using (hφSubset hy')
  have hWeak := h ψ hψSmooth hψCompact hψSubset
  have hDerivψ :
      ∀ y : Vec d,
        (fderiv ℝ ψ y) (basisVec i) =
          a * (fderiv ℝ φ (a • y)) (basisVec i) := by
    intro y
    have hderiv :
        fderiv ℝ (fun z => φ (a • z)) y =
          a • fderiv ℝ φ (a • y) := by
      simpa [ψ] using
        (fderiv_comp_smul (𝕜 := ℝ) (f := φ) (x := y) a)
    simpa [smul_eq_mul] using
      congrArg (fun L => L (basisVec i)) hderiv
  have hWeakScaled :
      a * ∫ y in U,
          u y * (fderiv ℝ φ (a • y)) (basisVec i)
            ∂MeasureTheory.volume =
        -∫ y in U, gi y * φ (a • y) ∂MeasureTheory.volume := by
    have hfun :
        (fun y => u y * (fderiv ℝ ψ y) (basisVec i)) =
          fun y =>
            a * (u y * (fderiv ℝ φ (a • y)) (basisVec i)) := by
      funext y
      rw [hDerivψ y]
      ring
    rw [hfun, MeasureTheory.integral_const_mul] at hWeak
    simpa [ψ] using hWeak
  have hChangeLeft :
      ∫ y in U,
          a * (u y * (fderiv ℝ φ (a • y)) (basisVec i))
            ∂MeasureTheory.volume =
        (a ^ d)⁻¹ * ∫ x in V,
          a * u (T x) * (fderiv ℝ φ x) (basisVec i)
            ∂MeasureTheory.volume := by
    simpa [V, T, smul_smul, inv_mul_cancel₀ haNe, Module.finrank_fin_fun, mul_assoc] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume)
        (f := fun x =>
          a * u (T x) * (fderiv ℝ φ x) (basisVec i))
        (s := U) ha)
  have hChangeRight :
      ∫ y in U, gi y * φ (a • y) ∂MeasureTheory.volume =
        (a ^ d)⁻¹ * ∫ x in V, gi (T x) * φ x
          ∂MeasureTheory.volume := by
    simpa [V, T, smul_smul, inv_mul_cancel₀ haNe, Module.finrank_fin_fun] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume)
        (f := fun x => gi (T x) * φ x)
        (s := U) ha)
  have hScaleLeft :
      ∫ y in U,
          a * (u y * (fderiv ℝ φ (a • y)) (basisVec i))
            ∂MeasureTheory.volume =
        a * ∫ y in U,
          u y * (fderiv ℝ φ (a • y)) (basisVec i)
            ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_const_mul]
  calc
    ∫ x in V, a * u (T x) * (fderiv ℝ φ x) (basisVec i)
        ∂MeasureTheory.volume =
        (a ^ d) * ∫ y in U,
          a * (u y * (fderiv ℝ φ (a • y)) (basisVec i))
            ∂MeasureTheory.volume := by
          have hpow := (pow_pos ha d).ne'
          rw [hChangeLeft]
          field_simp [hpow]
    _ = (a ^ d) *
        (a * ∫ y in U,
          u y * (fderiv ℝ φ (a • y)) (basisVec i)
            ∂MeasureTheory.volume) := by
          rw [hScaleLeft]
    _ = (a ^ d) *
        (-∫ y in U, gi y * φ (a • y)
          ∂MeasureTheory.volume) := by
          rw [hWeakScaled]
    _ = -((a ^ d) * ∫ y in U, gi y * φ (a • y)
          ∂MeasureTheory.volume) := by
          ring
    _ = -∫ x in V, gi (T x) * φ x
        ∂MeasureTheory.volume := by
          rw [hChangeRight]
          field_simp [((pow_pos ha d).ne')]

end HasWeakPartialDerivOn

namespace HasWeakGradientOn

end HasWeakGradientOn


namespace HasWeakPartialDerivOn

/-- Precomposition by the affine convex-approximation sample multiplies a
weak partial derivative by the exact linear factor `1 - ε`. -/
theorem comp_convexApproxSample
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (hu : HasWeakPartialDerivOn U i u gi)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (fun x => u (convexApproxSample x0 z r ε x))
      (fun x =>
        (1 - ε) * gi (convexApproxSample x0 z r ε x)) := by
  let a : ℝ := 1 - ε
  let b := ε • (x0 - r • z)
  let V := translateSet b (a • U)
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have hVU : V ⊆ U := by
    exact
      translateSet_smul_subset_of_convexApproxSample_mapsTo
        (x0 := x0) (z := z) (r := r) (ε := ε) (convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain hU hball hr hz hε0 hε1.le)
  have hV :
      IsOpenBoundedConvexDomain V := by
    simpa using
      (hU.smul_of_pos ha).translateSet b
  have hTranslated :
      HasWeakPartialDerivOn (a • U) i
        (fun x => u (x + b)) (fun x => gi (x + b)) := by
    simpa only [V, translateSet_translateSet, add_neg_cancel,
      translateSet_zero, sub_neg_eq_add] using
      (hu.restrict hV.isOpen hVU).translate (-b)
  have hDilated :
      HasWeakPartialDerivOn U i
        (fun x => a⁻¹ * u (a • x + b))
        (fun x => gi (a • x + b)) := by
    simpa [inv_inv, smul_smul, inv_mul_cancel₀ ha.ne'] using (hTranslated.dilate_of_pos (inv_pos.mpr ha))
  have hScaled := hDilated.smul a
  change
    HasWeakPartialDerivOn U i
      (fun x => a * (a⁻¹ * u (a • x + b)))
      (fun x => a * gi (a • x + b)) at hScaled
  simpa [← mul_assoc, mul_inv_cancel₀ ha.ne', a, b, convexApproxSample] using hScaled

end HasWeakPartialDerivOn

namespace HasWeakGradientOn

end HasWeakGradientOn

end PDE

