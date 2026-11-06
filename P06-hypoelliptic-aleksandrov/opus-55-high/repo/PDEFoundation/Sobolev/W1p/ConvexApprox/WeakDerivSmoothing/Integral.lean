module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.WeakDerivSmoothing.Affine

/-!
# Averaging weak derivatives over a convex smoothing kernel

Compact local integrability and Fubini give the exact smoothing derivative identity.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

variable {d : ℕ} {U : Set (Vec d)}

private theorem integrableOn_comp_smul_add_for_weakSmoothing
     {K : Set (Vec d)} {u : Vec d → ℝ}
    {a : ℝ} (ha : 0 < a) (b : Vec d)
    (hK : MeasurableSet K)
    (hu : MeasureTheory.IntegrableOn u
      (translateSet b (a • K)) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      (fun x => u (a • x + b)) K MeasureTheory.volume := by
  have haNe  := ha.ne'
  let V  := translateSet b (a • K)
  have hV : MeasurableSet V := by
    have hpre :
        ⇑(Homeomorph.subRight b) ⁻¹' (a • K) = V := by
      ext x
      simp [V, mem_translateSet_iff_sub_mem]
    rw [← hpre]
    have haK : MeasurableSet (a • K) :=
      ((Homeomorph.smulOfNeZero a haNe).toMeasurableEquiv.measurableSet_image).2
        hK
    exact
      ((Homeomorph.subRight b).toMeasurableEquiv.measurableSet_preimage).2
        haK
  have hIndicator :
      MeasureTheory.Integrable
        (Set.indicator V u) MeasureTheory.volume :=
    hu.integrable_indicator hV
  have hTranslated :
      MeasureTheory.Integrable
        (fun x => Set.indicator V u (x + b))
        MeasureTheory.volume := by
    exact
      (MeasureTheory.measurePreserving_add_right
        _ b).integrable_comp_of_integrable
            hIndicator
  have hScaled :
      MeasureTheory.Integrable
        (fun x => Set.indicator V u (a • x + b))
        MeasureTheory.volume := by
    let g  :=
      fun x => Set.indicator V u (x + b)
    have hg :
        MeasureTheory.Integrable g MeasureTheory.volume := by
      omega
    simpa using
      hg.comp_smul haNe
  have hIndicatorEq :
      Set.indicator K (fun x => u (a • x + b)) =
        fun x => Set.indicator V u (a • x + b) := by
    funext x
    by_cases hx : x ∈ K
    · have hyV : a • x + b ∈ V :=
        ⟨a • x, Set.smul_mem_smul_set hx, rfl⟩
      simp_all
    · have hyV : a • x + b ∉ V := by
        intro hyV
        rcases hyV with ⟨w, hw, hyw⟩
        aesop
      simp_all
  refine
    (MeasureTheory.integrable_indicator_iff hK).1 ?_
  simp_all

private theorem
    integrableOn_comp_convexApproxSample_of_locallyIntegrableOn_for_weakSmoothing
     {U K : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hKU : K ⊆ U) (hK : IsCompact K)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    MeasureTheory.IntegrableOn
      (fun x => u (convexApproxSample x0 z r ε x))
      K MeasureTheory.volume := by
  let a  := 1 - ε
  let b  := ε • (x0 - r • z)
  let V  := translateSet b (a • K)
  have ha : 0 < a := by
    linarith
  have hmap  :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr hz hε0 hε1.le
  have hVU : V ⊆ U := by
    intro y hy
    rcases hy with ⟨w, hw, hyw⟩
    rcases Set.mem_smul_set.mp hw with ⟨x, hx, rfl⟩
    aesop
  have hV : IsCompact V := by
    have hImage :
        (fun x : Vec d => a • x + b) '' K = V := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact
          ⟨a • x, Set.smul_mem_smul_set hx, rfl⟩
      · rintro ⟨w, hw, hyw⟩
        aesop
    rw [← hImage]
    exact
      hK.image (by fun_prop)
  have huV  :=
    hu.integrableOn_compact_subset hVU hV
  simpa using
    (integrableOn_comp_smul_add_for_weakSmoothing
      (d := d) (u := u) (a := a) ha b
      hK.measurableSet huV)

private theorem
    integrableOn_kernel_mul_indicator_comp_convexApproxSample_mul
     {U K : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u ρ ψ : Vec d → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hψ : Continuous ψ) (hKU : K ⊆ U)
    (hK : IsCompact K)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    MeasureTheory.IntegrableOn
      (fun x =>
        ρ z *
          Set.indicator U u
            (convexApproxSample x0 z r ε x) *
          ψ x)
      K MeasureTheory.volume := by
  have hcomp  :=
    integrableOn_comp_convexApproxSample_of_locallyIntegrableOn_for_weakSmoothing
      hU hu hKU hK hball hr hz hε0 hε1
  have hmap  :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr hz hε0 hε1.le
  have hmul :
      MeasureTheory.IntegrableOn
        (fun x =>
          u _ * ψ x)
        K MeasureTheory.volume :=
    hcomp.mul_continuousOn hψ.continuousOn hK
  have hIndicator :
      MeasureTheory.IntegrableOn
        (fun x =>
          Set.indicator U u
              (convexApproxSample x0 z r ε x) *
            ψ x)
        K MeasureTheory.volume := by
    refine hmul.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem hK.measurableSet]
        with x hx
    rw [Set.indicator_of_mem (hmap (hKU hx))]
  rw [MeasureTheory.IntegrableOn]
  simpa only [mul_assoc] using
    hIndicator.integrable.const_mul _

private theorem quasiMeasurePreserving_convexApproxSample_prod
    
    {ρ : Vec d → ℝ} (x0 : Vec d)
    (r ε : ℝ) (hε1 : ε < 1) :
    MeasureTheory.Measure.QuasiMeasurePreserving
      (fun p : Vec d × Vec d =>
        convexApproxSample x0 p.2 r ε p.1)
      ((MeasureTheory.volume.restrict U).prod
        (MeasureTheory.volume.restrict (tsupport ρ)))
      MeasureTheory.volume := by
  refine
    MeasureTheory.QuasiMeasurePreserving.prod_of_left
      ?_ ?_
  · unfold convexApproxSample
    fun_prop
  · refine Filter.Eventually.of_forall ?_
    intro z
    let a : ℝ := 1 - ε
    let b : Vec d := ε • (x0 - r • z)
    have haNe : a ≠ 0 := by
      linarith
    have hsmul :
        MeasureTheory.Measure.QuasiMeasurePreserving
          (fun x : Vec d => a • x)
          MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.Measure.quasiMeasurePreserving_smul
        (μ := MeasureTheory.volume) haNe
    have hadd :
        MeasureTheory.MeasurePreserving
          (fun x : Vec d => x + b)
          MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.measurePreserving_add_right
        MeasureTheory.volume b
    have hsample :
        MeasureTheory.Measure.QuasiMeasurePreserving
          (convexApproxSample x0 z r ε)
          MeasureTheory.volume MeasureTheory.volume := by
      have h := hadd.quasiMeasurePreserving.comp hsmul
      aesop
    exact
      hsample.mono_left
        MeasureTheory.Measure.absolutelyContinuous_restrict

private theorem
    aestronglyMeasurable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
    
    (hU : MeasurableSet U)
    {u ρ ψ : Vec d → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hρ : IsConvexApproxKernel ρ)
    (hψ : Continuous ψ) (hψU : tsupport ψ ⊆ U)
    {x0 : Vec d} {r ε : ℝ} (hε1 : ε < 1) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : Vec d × Vec d =>
        ρ p.2 *
          Set.indicator U u
            (convexApproxSample x0 p.2 r ε p.1) *
          ψ p.1)
      ((MeasureTheory.volume.restrict (tsupport ψ)).prod
        (MeasureTheory.volume.restrict (tsupport ρ))) := by
  let μψ : MeasureTheory.Measure (Vec d) :=
    MeasureTheory.volume.restrict (tsupport ψ)
  let μρ : MeasureTheory.Measure (Vec d) :=
    MeasureTheory.volume.restrict (tsupport ρ)
  have huIndicator :
      MeasureTheory.AEStronglyMeasurable
        (Set.indicator U u) MeasureTheory.volume := by
    exact
      (aestronglyMeasurable_indicator_iff
        hU).2 hu.aestronglyMeasurable
  have hbase :
      MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d =>
          Set.indicator U u
            (convexApproxSample x0 p.2 r ε p.1))
        ((MeasureTheory.volume.restrict U).prod μρ) := by
    exact
      huIndicator.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_convexApproxSample_prod
          (U := U) (ρ := ρ) x0 r ε hε1)
  have hμψ :
      μψ ≤ MeasureTheory.volume.restrict U :=
    MeasureTheory.Measure.restrict_mono_set
      MeasureTheory.volume hψU
  have hprod :
      μψ.prod μρ ≤
        (MeasureTheory.volume.restrict U).prod μρ := by
    refine MeasureTheory.Measure.le_iff.2 ?_
    intro s hs
    rw [MeasureTheory.Measure.prod_apply hs,
      MeasureTheory.Measure.prod_apply hs]
    exact MeasureTheory.lintegral_mono' hμψ le_rfl
  have hcomp :
      MeasureTheory.AEStronglyMeasurable
        _
        (μψ.prod μρ) :=
    hbase.mono_measure hprod
  have hρMeas :
      MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d => ρ p.2)
        (μψ.prod μρ) :=
    (hρ.continuous.comp continuous_snd).aestronglyMeasurable
  have hψMeas :
      MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d => ψ p.1)
        (μψ.prod μρ) :=
    (hψ.comp continuous_fst).aestronglyMeasurable
  have h := hρMeas.mul (hcomp.mul hψMeas)
  convert h using 1
  funext p
  simp only [Pi.mul_apply, mul_assoc]

private theorem integrableOn_comp_convexApproxSample_for_weakSmoothing
    
    (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ}
    (hu : MeasureTheory.IntegrableOn
      u U MeasureTheory.volume)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    MeasureTheory.IntegrableOn
      (fun x => u (convexApproxSample x0 z r ε x))
      U MeasureTheory.volume := by
  let a  := 1 - ε
  let b  := ε • (x0 - r • z)
  let V  := translateSet b (a • U)
  have ha : 0 < a := by
    linarith
  have hmap  :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr hz hε0 hε1.le
  have hVU : V ⊆ U :=
    translateSet_smul_subset_of_convexApproxSample_mapsTo
      (x0 := x0) (z := z) (r := r) (ε := ε) hmap
  have huV  :=
    hu.mono_set hVU
  simpa using
    (integrableOn_comp_smul_add_for_weakSmoothing
      (d := d) (u := u) (a := a) ha b
      hU.measurableSet huV)

private theorem
    integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul_of_integrableOn
    
    (hU : IsOpenBoundedConvexDomain U)
    {u ρ ψ : Vec d → ℝ}
    (hu : MeasureTheory.IntegrableOn
      u U MeasureTheory.volume)
    (hρ : IsConvexApproxKernel ρ)
    (hψ : Continuous ψ)
    (hψCompact : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    MeasureTheory.Integrable
      (fun p : Vec d × Vec d =>
        ρ p.2 *
          Set.indicator U u
            (convexApproxSample x0 p.2 r ε p.1) *
          ψ p.1)
      ((MeasureTheory.volume.restrict (tsupport ψ)).prod
        (MeasureTheory.volume.restrict (tsupport ρ))) := by
  let μψ : MeasureTheory.Measure (Vec d) :=
    MeasureTheory.volume.restrict (tsupport ψ)
  let μρ : MeasureTheory.Measure (Vec d) :=
    MeasureTheory.volume.restrict (tsupport ρ)
  let a  := 1 - ε
  have ha : 0 < a := by
    linarith
  have huLoc  :=
    hu.locallyIntegrableOn
  have hmeas :
      MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d =>
          ρ p.2 *
            Set.indicator U u
              (convexApproxSample x0 p.2 r ε p.1) *
            ψ p.1)
        (μψ.prod μρ) := by
    simpa using
      aestronglyMeasurable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
        hU.measurableSet huLoc hρ hψ hψU hε1
  refine (MeasureTheory.integrable_prod_iff' hmeas).2 ?_
  constructor
  · filter_upwards
      [MeasureTheory.ae_restrict_mem
        hρ.compactSupport.isCompact.measurableSet]
        with z hz
    have hzNorm : ‖z‖ ≤ 1 := by
      simpa using
          hρ.support_subset_closedBall hz
    simpa using
      (integrableOn_kernel_mul_indicator_comp_convexApproxSample_mul
        hU huLoc hψ hψU hψCompact.isCompact
        hball hr hzNorm hε0 hε1).integrable
  · obtain ⟨C0, hC0⟩ :=
      hψCompact.exists_bound_of_continuous hψ
    let Cψ : ℝ := max C0 0
    have hCψNonneg : 0 ≤ Cψ := by
      positivity
    have hψBound : ∀ x, ‖ψ x‖ ≤ Cψ := by
      grind
    let Cu : ℝ :=
      ∫ y in U, |u y| ∂MeasureTheory.volume
    have hCuNonneg : 0 ≤ Cu := by
      positivity
    let bound : Vec d → ℝ :=
      fun z => ρ z * (Cψ * ((a ^ d)⁻¹ * Cu))
    have hbound :
        MeasureTheory.Integrable bound μρ := by
      have hboundVolume :
          MeasureTheory.Integrable
            bound MeasureTheory.volume := by
        have hcont : Continuous bound := hρ.continuous.mul continuous_const
        have hcompact : HasCompactSupport bound := hρ.compactSupport.mul_right
        exact
          hcont.integrable_of_hasCompactSupport hcompact
      simpa using
        (MeasureTheory.Integrable.restrict
          (s := tsupport ρ) hboundVolume)
    have hinnerMeas :
        MeasureTheory.AEStronglyMeasurable
          (fun z =>
            ∫ x,
              ‖ρ z *
                Set.indicator U u
                  (convexApproxSample x0 z r ε x) *
                ψ x‖ ∂μψ)
          μρ := hmeas.norm.prod_swap.integral_prod_right'
    refine
      MeasureTheory.Integrable.mono
        hbound hinnerMeas ?_
    filter_upwards with z
    by_cases hzρ : z ∈ tsupport ρ
    · let V : Set (Vec d) :=
        translateSet
          (ε • (x0 - r • z)) (a • U)
      have hzNorm : ‖z‖ ≤ 1 := by
        simpa using
            hρ.support_subset_closedBall hzρ
      have hmap :
          Set.MapsTo
            (convexApproxSample x0 z r ε) U U :=
        convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
          hU hball hr hzNorm hε0 hε1.le
      have hsampleψ :
          MeasureTheory.IntegrableOn
            (fun x =>
              |u (convexApproxSample x0 z r ε x)|)
            (tsupport ψ) MeasureTheory.volume := by
        have huNorm :
            MeasureTheory.IntegrableOn
              (fun y => ‖u y‖) U
              MeasureTheory.volume :=
          hu.norm
        simpa using
          integrableOn_comp_convexApproxSample_of_locallyIntegrableOn_for_weakSmoothing
            hU huNorm.locallyIntegrableOn hψU
            hψCompact.isCompact hball hr hzNorm
            hε0 hε1
      have hsampleU :
          MeasureTheory.IntegrableOn
            (fun x =>
              |u (convexApproxSample x0 z r ε x)|)
            U MeasureTheory.volume := by
        have huNorm :
            MeasureTheory.IntegrableOn
              (fun y => ‖u y‖) U
              MeasureTheory.volume :=
          hu.norm
        simpa using
          integrableOn_comp_convexApproxSample_for_weakSmoothing
            hU huNorm hball hr hzNorm hε0 hε1
      have hdom :
          MeasureTheory.Integrable
            (fun x =>
              ρ z *
                (|u (convexApproxSample x0 z r ε x)| *
                  Cψ))
            μψ := by
        simpa using
          ((hsampleψ.integrable.mul_const Cψ).const_mul
            _)
      have hinner :
          MeasureTheory.Integrable
            (fun x =>
              ρ z *
                Set.indicator U u
                  (convexApproxSample x0 z r ε x) *
                ψ x)
            μψ := by
        simpa using
          (integrableOn_kernel_mul_indicator_comp_convexApproxSample_mul
            hU huLoc hψ hψU hψCompact.isCompact
            hball hr hzNorm hε0 hε1).integrable
      have hpointwise :
          (fun x =>
            ‖ρ z *
              Set.indicator U u
                (convexApproxSample x0 z r ε x) *
              ψ x‖) ≤ᵐ[μψ]
            (fun x =>
              ρ z *
                (|u (convexApproxSample x0 z r ε x)| *
                  Cψ)) := by
        filter_upwards
          [MeasureTheory.ae_restrict_mem
            hψCompact.isCompact.measurableSet]
            with x hx
        have hxU  := hψU hx
        have hsampleU  :=
          hmap hxU
        calc
          ‖ρ z *
              Set.indicator U u
                _ *
              ψ x‖ =
              ρ z *
                (|u _| *
                  ‖ψ x‖) := by
            rw [Set.indicator_of_mem hsampleU]
            simp only [Real.norm_eq_abs, norm_mul,
              abs_of_nonneg (hρ.nonneg z)]
            ring
          _ ≤ ρ z *
              (|u _| *
                Cψ) := by
            refine mul_le_mul_of_nonneg_left ?_
              (hρ.nonneg z)
            exact mul_le_mul_of_nonneg_left
              (hψBound x) (abs_nonneg _)
      have hsampleBound :
          ∫ x,
              |u (convexApproxSample x0 z r ε x)|
              ∂μψ ≤
            (a ^ d)⁻¹ * Cu := by
        have hmono :
            (∫ x in tsupport ψ,
                |u (convexApproxSample x0 z r ε x)|
                ∂MeasureTheory.volume) ≤
              ∫ x in U,
                |u (convexApproxSample x0 z r ε x)|
                ∂MeasureTheory.volume := by
          exact
            MeasureTheory.setIntegral_mono_set
              hsampleU
              (Filter.Eventually.of_forall
                fun x => abs_nonneg _)
              (Filter.Eventually.of_forall hψU)
        have hVU : V ⊆ U :=
          translateSet_smul_subset_of_convexApproxSample_mapsTo
            (x0 := x0) (z := z) (r := r)
            (ε := ε) hmap
        have hchange :
            (∫ x in U,
                |u (convexApproxSample x0 z r ε x)|
                ∂MeasureTheory.volume) =
              (a ^ d)⁻¹ *
                ∫ y in V, |u y|
                  ∂MeasureTheory.volume := by
          simpa using
            (setIntegral_comp_smul_add_of_pos
              (d := d) (E := ℝ) ha
              _ U
              (fun y => |u y|))
        have hVBound :
            (∫ y in V, |u y|
                ∂MeasureTheory.volume) ≤ Cu := by
          exact
            MeasureTheory.setIntegral_mono_set
              hu.norm
              (Filter.Eventually.of_forall
                fun y => abs_nonneg _)
              (Filter.Eventually.of_forall hVU)
        calc
          (∫ x,
              |u _|
              ∂μψ) =
              ∫ x in tsupport ψ,
                |u _|
                ∂MeasureTheory.volume := by
            rfl
          _ ≤ ∫ x in U,
              |u _|
              ∂MeasureTheory.volume :=
            hmono
          _ = (a ^ d)⁻¹ *
              ∫ y in V, |u y|
                ∂MeasureTheory.volume :=
            hchange
          _ ≤ (a ^ d)⁻¹ * Cu := by
            simp_all
      show
        ‖∫ x,
            ‖ρ z *
              Set.indicator U u
                (convexApproxSample x0 z r ε x) *
              ψ x‖ ∂μψ‖ ≤
          ‖bound z‖
      calc
        ‖∫ x,
            ‖ρ z *
              Set.indicator U u
                _ *
              ψ x‖ ∂μψ‖ =
            ∫ x,
              ‖ρ z *
                Set.indicator U u
                  _ *
                ψ x‖ ∂μψ := by
          have hnonneg :
              0 ≤
                ∫ x,
                  ‖ρ z *
                    Set.indicator U u
                      (convexApproxSample x0 z r ε x) *
                    ψ x‖ ∂μψ :=
            MeasureTheory.integral_nonneg_of_ae
              (Filter.Eventually.of_forall
                fun x => norm_nonneg _)
          simp_all
        _ ≤ ∫ x,
            ρ z *
              (|u _| *
                Cψ) ∂μψ :=
          MeasureTheory.integral_mono_ae
            hinner.norm hdom hpointwise
        _ = ρ z *
            (Cψ *
              ∫ x,
                |u _|
                ∂μψ) := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_mul_const]
          ring
        _ ≤ ρ z * (Cψ * ((a ^ d)⁻¹ * Cu)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (hρ.nonneg z)
          exact mul_le_mul_of_nonneg_left
            hsampleBound hCψNonneg
        _ = bound z := by
          rfl
        _ = ‖bound z‖ := by
          have hboundNonneg : 0 ≤ bound z := by
            exact
              mul_nonneg (hρ.nonneg z)
                (mul_nonneg hCψNonneg
                  (mul_nonneg (by positivity) hCuNonneg))
          rw [Real.norm_eq_abs,
            abs_of_nonneg hboundNonneg]
    · have hρz : ρ z = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := ρ) hzρ
      simp_all

private theorem
    integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
    
    (hU : IsOpenBoundedConvexDomain U)
    {u ρ ψ : Vec d → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hρ : IsConvexApproxKernel ρ)
    (hψ : Continuous ψ)
    (hψCompact : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    MeasureTheory.Integrable
      (fun p : Vec d × Vec d =>
        ρ p.2 *
          Set.indicator U u
            (convexApproxSample x0 p.2 r ε p.1) *
          ψ p.1)
      ((MeasureTheory.volume.restrict (tsupport ψ)).prod
        (MeasureTheory.volume.restrict (tsupport ρ))) := by
  let K  :=
    tsupport ψ ×ˢ tsupport ρ
  let W  :=
    (fun p : Vec d × Vec d =>
      convexApproxSample x0 p.2 r ε p.1) '' K
  let uW  := Set.indicator W u
  have hK : IsCompact K :=
    hψCompact.isCompact.prod hρ.compactSupport.isCompact
  have hKMeas  :=
    hK.measurableSet
  have hsampleContinuous :
      Continuous
        (fun p : Vec d × Vec d =>
          convexApproxSample x0 p.2 r ε p.1) := by
    unfold convexApproxSample
    fun_prop
  have hW : IsCompact W :=
    hK.image hsampleContinuous
  have hWU : W ⊆ U := by
    rintro y ⟨p, hp, rfl⟩
    have hzNorm : ‖p.2‖ ≤ 1 := by
      simpa using
          hρ.support_subset_closedBall hp.2
    exact
      convexApproxSample_mem_of_isOpenBoundedConvexDomain
        hU (hψU hp.1) hball hr hzNorm hε0 hε1.le
  have huWOnW  :=
    hu.integrableOn_compact_subset hWU hW
  have huW :
      MeasureTheory.Integrable
        uW MeasureTheory.volume :=
    huWOnW.integrable_indicator hW.measurableSet
  have huWOnU :
      MeasureTheory.IntegrableOn
        uW U MeasureTheory.volume :=
    huW.integrableOn
  have htrunc  :=
    integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul_of_integrableOn
      hU huWOnU hρ hψ hψCompact hψU
      hball hr hε0 hε1
  have hcongr :
      (fun p : Vec d × Vec d =>
        ρ p.2 *
          Set.indicator U uW
            (convexApproxSample x0 p.2 r ε p.1) *
          ψ p.1) =ᵐ[
          (MeasureTheory.volume.restrict (tsupport ψ)).prod
            (MeasureTheory.volume.restrict (tsupport ρ))]
        (fun p : Vec d × Vec d =>
          ρ p.2 *
            Set.indicator U u
              (convexApproxSample x0 p.2 r ε p.1) *
            ψ p.1) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact
      (MeasureTheory.ae_restrict_iff' hKMeas).2
        (Filter.Eventually.of_forall fun p hp => by
          let y  :=
            convexApproxSample x0 p.2 r ε p.1
          have hyW : y ∈ W :=
            Set.mem_image_of_mem
              _ hp
          have hyU  := hWU hyW
          aesop)
  exact htrunc.congr hcongr

namespace HasWeakPartialDerivOn

variable {d : ℕ} {U : Set (Vec d)}

/-- Convex-domain smoothing commutes with a weak partial derivative, with the
exact factor `1 - ε` contributed by the affine sampling map. -/
theorem convexApproxSmoothing
    
    (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn
      gi U MeasureTheory.volume)
    (hu : HasWeakPartialDerivOn U i u gi)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (PDE.convexApproxSmoothing ρ u x0 r ε)
      (fun x =>
        (1 - ε) *
          PDE.convexApproxSmoothing ρ gi x0 r ε x) := by
  intro φ hφSmooth hφCompact hφU
  let dφ  :=
    fun x => (fderiv ℝ φ x) (basisVec i)
  let F  :=
    fun x z =>
      ρ z *
        Set.indicator U u
          (convexApproxSample x0 z r ε x) *
        dφ x
  let G  :=
    fun x z =>
      ρ z *
        Set.indicator U gi
          (convexApproxSample x0 z r ε x) *
        φ x
  have hdφContinuous : Continuous dφ := by
    simpa only [dφ] using
      (hφSmooth.continuous_fderiv (by simp)).clm_apply
        continuous_const
  have hdφCompact : HasCompactSupport dφ := by
    simpa only [dφ] using
      hφCompact.fderiv_apply
        (𝕜 := ℝ) _
  have hdφSupport :
      Function.support dφ ⊆ tsupport φ := by
    intro x hx
    apply support_fderiv_subset (𝕜 := ℝ)
    intro hzero
    apply hx
    simp only [dφ, hzero,
      zero_apply]
  have hdφTSupport : tsupport dφ ⊆ tsupport φ :=
    closure_minimal hdφSupport
      (isClosed_tsupport (f := φ))
  have hdφU : tsupport dφ ⊆ U :=
    hdφTSupport.trans hφU
  have hprodLeft :
      MeasureTheory.Integrable
        (fun p : Vec d × Vec d => F p.1 p.2)
        ((MeasureTheory.volume.restrict (tsupport dφ)).prod
          (MeasureTheory.volume.restrict
            (tsupport ρ))) := by
    simpa only [F] using
      integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
        hU huLoc hρ hdφContinuous hdφCompact
        hdφU hball hr hε0 hε1
  have hprodRight :
      MeasureTheory.Integrable
        (fun p : Vec d × Vec d => G p.1 p.2)
        ((MeasureTheory.volume.restrict (tsupport φ)).prod
          (MeasureTheory.volume.restrict
            (tsupport ρ))) := by
    simpa only [G] using
      integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
        hU hgiLoc hρ hφSmooth.continuous hφCompact
        hφU hball hr hε0 hε1
  have hswapLeft :
      (∫ x in tsupport dφ,
          ∫ z in tsupport ρ, F x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume) =
        ∫ z in tsupport ρ,
          ∫ x in tsupport dφ, F x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    simpa only using
      (MeasureTheory.integral_integral_swap
        (μ := MeasureTheory.volume.restrict
          _)
        (ν := MeasureTheory.volume.restrict
          _)
        (f := F) hprodLeft)
  have hswapRight :
      (∫ x in tsupport φ,
          ∫ z in tsupport ρ, G x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume) =
        ∫ z in tsupport ρ,
          ∫ x in tsupport φ, G x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    simpa only using
      (MeasureTheory.integral_integral_swap
        (μ := MeasureTheory.volume.restrict
          _)
        (ν := MeasureTheory.volume.restrict
          _)
        (f := G) hprodRight)
  have hrestrict :
      ∀ (v ψ : Vec d → ℝ),
        tsupport ψ ⊆ U →
        (∫ x in U,
            PDE.convexApproxSmoothing ρ v x0 r ε x * ψ x
              ∂MeasureTheory.volume) =
          ∫ x in tsupport ψ,
            PDE.convexApproxSmoothing ρ v x0 r ε x * ψ x
              ∂MeasureTheory.volume := by
    intro v ψ hψU
    exact
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hU.measurableSet hψU (fun x hx => by
          simp only [
            image_eq_zero_of_notMem_tsupport hx.2,
            mul_zero])
  have hinner :
      ∀ (v ψ : Vec d → ℝ),
        tsupport ψ ⊆ U →
        (∫ x in tsupport ψ,
            PDE.convexApproxSmoothing ρ v x0 r ε x * ψ x
              ∂MeasureTheory.volume) =
          ∫ x in tsupport ψ,
            ∫ z in tsupport ρ,
              ρ z *
                Set.indicator U v
                  (convexApproxSample x0 z r ε x) *
                ψ x
              ∂MeasureTheory.volume
            ∂MeasureTheory.volume := by
    intro v ψ hψU
    refine MeasureTheory.setIntegral_congr_fun
      (isClosed_tsupport (f := ψ)).measurableSet ?_
    intro x hx
    have hxU  := hψU hx
    have hsample :
        ∀ z ∈ tsupport ρ,
          convexApproxSample x0 z r ε x ∈ U := by
      intro z hz
      have hzNorm : ‖z‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,
          dist_zero_right] using
            hρ.support_subset_closedBall hz
      exact
        convexApproxSample_mem_of_isOpenBoundedConvexDomain
          hU hxU hball hr hzNorm hε0 hε1.le
    calc
      PDE.convexApproxSmoothing ρ v x0 r ε x * ψ x =
          (∫ z in tsupport ρ,
            ρ z *
              v _
              ∂MeasureTheory.volume) * ψ x := by
        rfl
      _ = ∫ z in tsupport ρ,
            (ρ z *
              v _) *
              ψ x
            ∂MeasureTheory.volume := by
        rw [← MeasureTheory.integral_mul_const]
      _ = ∫ z in tsupport ρ,
            ρ z *
              Set.indicator U v
                _ *
              ψ x
            ∂MeasureTheory.volume := by
        refine MeasureTheory.setIntegral_congr_fun
          hρ.compactSupport.isCompact.measurableSet ?_
        intro z hz
        change
          ρ z * v _ * ψ x =
            ρ z *
              Set.indicator U v
                _ *
              ψ x
        rw [Set.indicator_of_mem (hsample z hz)]
  have hfactor :
      ∀ (v ψ : Vec d → ℝ) (z : Vec d),
        tsupport ψ ⊆ U →
        z ∈ tsupport ρ →
        (∫ x in tsupport ψ,
            ρ z *
              Set.indicator U v
                (convexApproxSample x0 z r ε x) *
              ψ x
              ∂MeasureTheory.volume) =
          ρ z *
            ∫ x in U,
              v (convexApproxSample x0 z r ε x) *
                ψ x
              ∂MeasureTheory.volume := by
    intro v ψ z hψU hz
    have hzNorm : ‖z‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall,
        dist_zero_right] using
          hρ.support_subset_closedBall hz
    have hmap  :=
      convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
        hU hball hr hzNorm hε0 hε1.le
    calc
      (∫ x in tsupport ψ,
          ρ z *
            Set.indicator U v
              _ *
            ψ x
            ∂MeasureTheory.volume) =
          ∫ x in U,
            ρ z *
              Set.indicator U v
                _ *
              ψ x
            ∂MeasureTheory.volume := by
        symm
        exact
          MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
            hU.measurableSet hψU (fun x hx => by
              simp only [
                image_eq_zero_of_notMem_tsupport hx.2,
                mul_zero])
      _ = ∫ x in U,
            ρ z *
              (v _ *
                ψ x)
            ∂MeasureTheory.volume := by
        refine MeasureTheory.setIntegral_congr_fun
          hU.measurableSet ?_
        intro x hx
        change
          ρ z *
              Set.indicator U v
                _ *
              ψ x =
            ρ z *
              (v _ * ψ x)
        rw [Set.indicator_of_mem (hmap hx)]
        ring
      _ = ρ z *
          ∫ x in U,
            v _ *
              ψ x
            ∂MeasureTheory.volume := by
        rw [MeasureTheory.integral_const_mul]
  have hfixed :
      ∀ z ∈ tsupport ρ,
        (∫ x in tsupport dφ, F x z
            ∂MeasureTheory.volume) =
          -(1 - ε) *
            ∫ x in tsupport φ, G x z
              ∂MeasureTheory.volume := by
    intro z hz
    have hweak :
        (∫ x in U,
            u (convexApproxSample x0 z r ε x) *
              dφ x
            ∂MeasureTheory.volume) =
          -∫ x in U,
            ((1 - ε) *
                gi (convexApproxSample x0 z r ε x)) *
              φ x
            ∂MeasureTheory.volume := by
      simpa only [dφ] using
        ((hu.comp_convexApproxSample
          hU hball hr
          (by
            simpa only [Metric.mem_closedBall,
              dist_zero_right] using
                hρ.support_subset_closedBall hz)
          hε0 hε1) φ hφSmooth hφCompact hφU)
    have hscaled :
        (∫ x in U,
            ((1 - ε) *
                gi (convexApproxSample x0 z r ε x)) *
              φ x
            ∂MeasureTheory.volume) =
          (1 - ε) *
            ∫ x in U,
              gi (convexApproxSample x0 z r ε x) *
                φ x
              ∂MeasureTheory.volume := by
      calc
        (∫ x in U,
            ((1 - ε) *
                gi _) *
              φ x
            ∂MeasureTheory.volume) =
            ∫ x in U,
              (1 - ε) *
                (gi _ *
                  φ x)
              ∂MeasureTheory.volume := by
          apply MeasureTheory.setIntegral_congr_fun
            hU.measurableSet
          intro x _hx
          ring
        _ = (1 - ε) *
            ∫ x in U,
              gi _ *
                φ x
              ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_const_mul]
    calc
      (∫ x in tsupport dφ, F x z
          ∂MeasureTheory.volume) =
          ρ z *
            ∫ x in U,
              u _ *
                dφ x
              ∂MeasureTheory.volume := by
        simpa only [F] using
          hfactor u dφ z hdφU hz
      _ = ρ z *
          (-((1 - ε) *
            ∫ x in U,
              gi _ *
                φ x
              ∂MeasureTheory.volume)) := by
        rw [hweak, hscaled]
      _ = -(1 - ε) *
          (ρ z *
            ∫ x in U,
              gi _ *
                φ x
              ∂MeasureTheory.volume) := by
        ring
      _ = -(1 - ε) *
          ∫ x in tsupport φ, G x z
            ∂MeasureTheory.volume := by
        rw [← hfactor gi φ z hφU hz]
  have hintegrated :
      (∫ z in tsupport ρ,
          ∫ x in tsupport dφ, F x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume) =
        ∫ z in tsupport ρ,
          -(1 - ε) *
            ∫ x in tsupport φ, G x z
              ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      hρ.compactSupport.isCompact.measurableSet ?_
    exact hfixed
  calc
    (∫ x in U,
        PDE.convexApproxSmoothing ρ u x0 r ε x *
          (fderiv ℝ φ x) _
        ∂MeasureTheory.volume) =
        ∫ x in U,
          PDE.convexApproxSmoothing ρ u x0 r ε x * dφ x
          ∂MeasureTheory.volume := by
      rfl
    _ = ∫ x in tsupport dφ,
          PDE.convexApproxSmoothing ρ u x0 r ε x * dφ x
          ∂MeasureTheory.volume :=
      hrestrict u dφ hdφU
    _ = ∫ x in tsupport dφ,
          ∫ z in tsupport ρ, F x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
      simpa only [F] using hinner u dφ hdφU
    _ = ∫ z in tsupport ρ,
          ∫ x in tsupport dφ, F x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume :=
      hswapLeft
    _ = ∫ z in tsupport ρ,
          -(1 - ε) *
            ∫ x in tsupport φ, G x z
              ∂MeasureTheory.volume
          ∂MeasureTheory.volume :=
      hintegrated
    _ = -(1 - ε) *
        ∫ z in tsupport ρ,
          ∫ x in tsupport φ, G x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
      rw [MeasureTheory.integral_const_mul]
    _ = -(1 - ε) *
        ∫ x in tsupport φ,
          ∫ z in tsupport ρ, G x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
      rw [← hswapRight]
    _ = -(1 - ε) *
        ∫ x in tsupport φ,
          PDE.convexApproxSmoothing ρ gi x0 r ε x * φ x
          ∂MeasureTheory.volume := by
      rw [← hinner gi φ hφU]
    _ = -(1 - ε) *
        ∫ x in U,
          PDE.convexApproxSmoothing ρ gi x0 r ε x * φ x
          ∂MeasureTheory.volume := by
      rw [← hrestrict gi φ hφU]
    _ = -∫ x in U,
        ((1 - ε) *
            PDE.convexApproxSmoothing ρ gi x0 r ε x) *
          φ x
        ∂MeasureTheory.volume := by
      have hscale :
          (∫ x in U,
            ((1 - ε) *
                PDE.convexApproxSmoothing ρ gi x0 r ε x) *
              φ x
            ∂MeasureTheory.volume) =
            (1 - ε) *
              ∫ x in U,
                PDE.convexApproxSmoothing ρ gi x0 r ε x * φ x
                ∂MeasureTheory.volume := by
        calc
          (∫ x in U,
              ((1 - ε) *
                  PDE.convexApproxSmoothing ρ gi x0 r ε x) *
                φ x
              ∂MeasureTheory.volume) =
              ∫ x in U,
                (1 - ε) *
                  (PDE.convexApproxSmoothing ρ gi x0 r ε x * φ x)
                ∂MeasureTheory.volume := by
            refine MeasureTheory.setIntegral_congr_fun
              hU.measurableSet ?_
            intro x _hx
            ring
          _ = (1 - ε) *
              ∫ x in U,
                PDE.convexApproxSmoothing ρ gi x0 r ε x * φ x
                ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
      rw [hscale]
      ring

/-- The globally smooth representative has the same weak partial derivative
as convex-approximation smoothing on the domain. -/
theorem convexApproxSmoothRepresentative
    
    (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn
      gi U MeasureTheory.volume)
    (hu : HasWeakPartialDerivOn U i u gi)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (PDE.convexApproxSmoothRepresentative U ρ u x0 r ε)
      (fun x =>
        (1 - ε) *
          PDE.convexApproxSmoothRepresentative
            U ρ gi x0 r ε x) := by
  intro φ hφSmooth hφCompact hφU
  have hweak  :=
    hu.convexApproxSmoothing
      hU huLoc hgiLoc hρ hball hr.le hε0.le hε1
  have hleft :
      (∫ x in U,
          PDE.convexApproxSmoothRepresentative
              U ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume) =
        ∫ x in U,
          PDE.convexApproxSmoothing ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      hU.measurableSet ?_
    intro x hx
    change
      PDE.convexApproxSmoothRepresentative
            U ρ u x0 r ε x *
          (fderiv ℝ φ x) _ =
        PDE.convexApproxSmoothing ρ u x0 r ε x *
          (fderiv ℝ φ x) _
    rw [
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        hU hρ hx hball hr hε0 hε1]
  have hright :
      (∫ x in U,
          ((1 - ε) *
              PDE.convexApproxSmoothing ρ gi x0 r ε x) *
            φ x
          ∂MeasureTheory.volume) =
        ∫ x in U,
          ((1 - ε) *
              PDE.convexApproxSmoothRepresentative
                U ρ gi x0 r ε x) *
            φ x
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      hU.measurableSet ?_
    intro x hx
    change
      ((1 - ε) *
          PDE.convexApproxSmoothing ρ gi x0 r ε x) *
          φ x =
        ((1 - ε) *
            PDE.convexApproxSmoothRepresentative
              U ρ gi x0 r ε x) *
          φ x
    rw [
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        hU hρ hx hball hr hε0 hε1]
  calc
    (∫ x in U,
        PDE.convexApproxSmoothRepresentative U ρ u x0 r ε x *
          (fderiv ℝ φ x) _
        ∂MeasureTheory.volume) =
        ∫ x in U,
          PDE.convexApproxSmoothing ρ u x0 r ε x *
            (fderiv ℝ φ x) _
          ∂MeasureTheory.volume :=
      hleft
    _ = -∫ x in U,
          ((1 - ε) *
              PDE.convexApproxSmoothing ρ gi x0 r ε x) *
            φ x
          ∂MeasureTheory.volume :=
      hweak φ hφSmooth hφCompact hφU
    _ = -∫ x in U,
          ((1 - ε) *
              PDE.convexApproxSmoothRepresentative
                U ρ gi x0 r ε x) *
            φ x
          ∂MeasureTheory.volume := by
      simp_all

end HasWeakPartialDerivOn

namespace HasWeakGradientOn

end HasWeakGradientOn

end PDE
