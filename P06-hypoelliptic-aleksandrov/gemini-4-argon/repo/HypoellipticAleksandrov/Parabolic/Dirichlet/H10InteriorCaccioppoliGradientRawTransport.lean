module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10InteriorCaccioppoli
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGradientProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimePlateauCutoffDerivativeBound
import HypoellipticAleksandrov.Measure.LpProductRepresentative
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductMeasure
import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
import HypoellipticAleksandrov.Parabolic.Dirichlet.TimePlateauCutoff

/-! Transport of raw gradient representatives into interior Caccioppoli estimates. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
private theorem ae_prod_of_ae_ae_of_nullMeasurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {p : α × β → Prop}
    (hp : NullMeasurableSet {z | p z} (μ.prod ν))
    (h : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x, y)) :
    ∀ᵐ z ∂μ.prod ν, p z := by
  let s : Set (α × β) := toMeasurable (μ.prod ν) {z | p z}
  have hs : MeasurableSet s := measurableSet_toMeasurable _ _
  have hsp : ∀ᵐ z ∂μ.prod ν, z ∈ s ↔ p z := by
    filter_upwards [hp.toMeasurable_ae_eq] with z hz
    exact iff_of_eq hz
  have hsp' := Measure.ae_ae_of_ae_prod hsp
  have hsae : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, (x, y) ∈ s := by
    filter_upwards [h, hsp'] with x hx hxs
    filter_upwards [hx, hxs] with y hy hys
    exact hys.symm.mp hy
  have hsprod : ∀ᵐ z ∂μ.prod ν, z ∈ s :=
    (Measure.ae_prod_mem_iff_ae_ae_mem hs).mpr hsae
  filter_upwards [hsp, hsprod] with z hz hs'
  exact hz.mp hs'

private theorem exists_parabolicMemLpOn_of_product_ae_eq_restrict
    {d : ℕ} {I J : Set ℝ} {Ω O : Set (PDE.Vec d)}
    {f g : TimeVelocity d → ℝ}
    (hf : ParabolicMemLpOn (I ×ˢ Ω) (2 : ℝ≥0∞) f)
    (hJI : J ⊆ I) (hOΩ : O ⊆ Ω)
    (hfg : f =ᵐ[timeVelocityVolumeOn (J ×ˢ O)] g) :
    ∃ hg : ParabolicMemLpOn (J ×ˢ O) (2 : ℝ≥0∞) g,
      ‖hg.toLp g‖ ≤ ‖hf.toLp f‖ := by
  have hsub := Set.prod_mono hJI hOΩ
  let hg := (hf.mono_measure (Measure.restrict_mono_set volume hsub)).ae_eq hfg
  refine ⟨hg, ?_⟩
  rw [Lp.norm_toLp, Lp.norm_toLp, ← eLpNorm_congr_ae hfg]
  refine ENNReal.toReal_mono hf.eLpNorm_ne_top ?_
  exact eLpNorm_mono_measure f (Measure.restrict_mono_set volume hsub)

private theorem norm_uncurry_toLp_eq_of_ae_slice
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν ) [SFinite ν]
    (q : Lp (Lp ℝ (2 : ℝ≥0∞) ν) (2 : ℝ≥0∞) μ)
    (Q : α × β → ℝ)
    (hQ : MemLp Q (2 : ℝ≥0∞) (μ.prod ν))
    (hslice : ∀ᵐ x ∂μ,
      (fun y => Q (x, y)) =ᵐ[ν] fun y => q x y) :
    ‖hQ.toLp Q‖ = ‖q‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0)
  calc
    eLpNorm Q (2 : ℝ≥0∞) (μ.prod ν) ^ (2 : ℝ) =
        ∫⁻ z, ‖Q z‖ₑ ^ (2 : ℝ) ∂μ.prod ν := by
      simpa using (eLpNorm_nnreal_pow_eq_lintegral
        (f := Q) (μ := μ.prod ν) (p := (2 : NNReal)) (by norm_num) hQ.aestronglyMeasurable)
    _ = ∫⁻ x, ∫⁻ y, ‖Q (x, y)‖ₑ ^ (2 : ℝ) ∂ν ∂μ :=
      lintegral_prod _ (hQ.aestronglyMeasurable.enorm.pow aemeasurable_const)
    _ = ∫⁻ x, ‖q x‖ₑ ^ (2 : ℝ) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hslice] with x hx
      rw [Lp.enorm_def, ← eLpNorm_congr_ae hx]
      exact (eLpNorm_nnreal_pow_eq_lintegral
        (f := fun y => Q (x, y)) (μ := ν) (p := (2 : NNReal)) (by norm_num)
          ((Lp.memLp (q x)).aestronglyMeasurable.congr hx.symm)).symm
    _ = eLpNorm q (2 : ℝ≥0∞) μ ^ (2 : ℝ) := by
      simpa using (eLpNorm_nnreal_pow_eq_lintegral
        (f := q) (μ := μ) (p := (2 : NNReal)) (by norm_num)
        (Lp.memLp q).aestronglyMeasurable).symm

private theorem exists_raw_gradientCoord_spatialDifferenceQuotient_memLp_norm_sq_le
    {d Ω inner O Kη}
    (hΩ : IsOpen Ω) (T )
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (hOopen : IsOpen O) (hOinner : O ⊆ inner)
    (J : Set ℝ) (hJmeas : MeasurableSet J)
    (hJ : J ⊆ reverseTimeOpenInterval T)
    (u : ReverseTimeL2V hΩ T)
    (G : Fin d → TimeVelocity d → ℝ)
    (hGmem : ∀ i, MemLp (G i) (2 : ℝ≥0∞)
      (timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω)))
    (hGslice : ∀ᵐ τ ∂reverseTimeVolume T, ∀ i,
      (fun y => G i (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => gradientCLM hΩ (u τ) y i)
    (j k : Fin d) (h : ℝ)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ∃ hD : ParabolicMemLpOn (J ×ˢ O) (2 : ℝ≥0∞)
        (spatialDifferenceQuotient k h (G j)),
      ‖hD.toLp (spatialDifferenceQuotient k h (G j))‖ ^ 2 ≤
        ∫ τ,
          ‖gradientCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM hΩ η k h
              η.tsupport_subset hηshift (u τ))‖ ^ 2
          ∂volume.restrict J := by
  let A :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h
      η.tsupport_subset hηshift
  let qFull :=
    ((gradientCLM hΩ).comp A).compLpL (2 : ℝ≥0∞) (reverseTimeVolume T) u
  have hμJ : (reverseTimeVolume T).restrict J = volume.restrict J := by
    rw [reverseTimeVolume, Measure.restrict_restrict_of_subset hJ]
  let Dloc : TimeVelocity d → ℝ := fun z =>
    localizedSpatialDifferenceQuotient η k h (fun y => G j (z.1, y)) z.2
  have hqFull := ContinuousLinearMap.coeFn_compLpL ((gradientCLM hΩ).comp A) u
  have hqMem : MemLp (fun τ => qFull τ) (2 : ℝ≥0∞) (volume.restrict J) := by
    rw [← hμJ]
    exact (Lp.memLp qFull).restrict J
  let q := hqMem.toLp (fun τ => qFull τ)
  obtain ⟨Q, hQ, hQslice⟩ :=
    HypoellipticAleksandrov.exists_uncurry_memLp_two
      (volume.restrict J) (PDE.volumeOn Ω)
      ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).compLpL
        (2 : ℝ≥0∞) (volume.restrict J) q)
  have hq : ∀ᵐ τ ∂volume.restrict J,
      q τ = gradientCLM hΩ (A (u τ)) := by
    have hqFullJ : ∀ᵐ τ ∂volume.restrict J,
        qFull τ = gradientCLM hΩ (A (u τ)) := by
      rw [← hμJ]
      exact ae_restrict_of_ae hqFull
    filter_upwards [hqMem.coeFn_toLp, hqFullJ] with τ hR hF
    exact hR.trans hF
  have hGsliceJ : ∀ᵐ τ ∂volume.restrict J,
      (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
          (gradientCLM hΩ (u τ)) y := by
    rw [← hμJ]
    filter_upwards [ae_restrict_of_ae hGslice] with τ hτ
    filter_upwards [hτ j,
      PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
        (gradientCLM hΩ (u τ))] with y hG hcoord
    exact hG.trans hcoord.symm
  have hDslice : ∀ᵐ τ ∂volume.restrict J,
      (fun y => Dloc (τ, y)) =ᵐ[PDE.volumeOn O]
        fun y => ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).compLpL
          (2 : ℝ≥0∞) (volume.restrict J) q) τ y := by
    filter_upwards [hq, hGsliceJ,
      ContinuousLinearMap.coeFn_compLpL
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j) q] with τ hqτ hGτ hcoord
    have hs : (fun y => PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
        (gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift (u τ))) y)
      =ᵐ[PDE.volumeOn O]
        fun y => ((fun y => G j (τ, y)) (y + h • PDE.basisVec k) - (fun y => G j (τ, y)) y) / h := by
      let hηΩ := η.tsupport_subset
      let u := (u τ)
      let g := (fun y => G j (τ, y))
      have hg := hGτ.symm
      have hclass : PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
            (gradientCLM hΩ
              (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u)) =
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
              (valueCLM hΩ u) +
            localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)) := by
        have hgradient := congrArg (fun T : H10HilbertGraph hΩ →L[ℝ]
            PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) =>
            PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (T u))
          (gradientCLM_comp_localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h hηΩ hηshift)
        simpa only [ContinuousLinearMap.comp_apply,
          localizedSpatialDifferenceQuotientSmoothGradientCLM,
          ContinuousLinearMap.add_apply,
          PDE.hilbertVectorLpCoord_hilbertVectorLpAssemble] using hgradient
      have hadd := MeasureTheory.Lp.coeFn_add
        (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h (valueCLM hΩ u))
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
      have hcutoff := cutoffGradientSpatialDifferenceQuotientL2_apply_ae
        hΩ.measurableSet η j k h (valueCLM hΩ u)
      have hlocalized := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
        hΩ.measurableSet η k h
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u))
          g hg hηshift
      have hOΩ : O ⊆ Ω := fun y hy =>
        hηΩ (subset_tsupport η.toFun (by
          change η.toFun y ≠ 0
          rw [η.eq_one_on_inner y (hOinner hy)]
          exact one_ne_zero))
      have hmain : ∀ᵐ y ∂PDE.volumeOn Ω,
          y ∈ O →
            PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
                (gradientCLM hΩ
                  (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u)) y =
              (g (y + h • PDE.basisVec k) - g y) / h := by
        rw [hclass]
        filter_upwards [hadd, hcutoff, hlocalized] with y ha hc hl hyO
        rw [ha]
        simp only [Pi.add_apply]
        rw [hc, hl]
        rw [localizedSpatialDifferenceQuotient_apply,
          η.classicalGradient_eq_zero_of_mem_inner (hOinner hyO)]
        simp only [Pi.zero_apply, zero_mul, zero_add,
          η.eq_one_on_inner y (hOinner hyO), one_mul]
      have hrestricted := hmain.filter_mono
        (ae_mono (Measure.restrict_mono hOΩ le_rfl))
      filter_upwards [hrestricted, ae_restrict_mem hOopen.measurableSet] with y hy hyO
      exact hy hyO
    filter_upwards [hs, ae_restrict_mem hOopen.measurableSet] with y hs hyO
    change localizedSpatialDifferenceQuotient η k h
        (fun y => G j (τ, y)) y = _
    rw [localizedSpatialDifferenceQuotient_apply,
      η.eq_one_on_inner y (hOinner hyO)]
    simp only [one_mul]
    rw [hcoord, hqτ]
    exact hs.symm
  have hDmeas : AEStronglyMeasurable
      (fun z => localizedSpatialDifferenceQuotient η k h
        (fun y => (G j) (z.1, y)) z.2)
      (timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω)) := by
    let U := (G j)
    have hU := (hGmem j)
    let S := reverseTimeOpenInterval T ×ˢ Ω
    have hS : MeasurableSet S := measurableSet_Ioo.prod hΩ.measurableSet
    let E : Lp ℝ (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) :=
      Lp.zeroExtendLinearIsometry hS (hU.toLp U)
    have hE :=
      Lp.memLp E |>.aestronglyMeasurable
    have hshift : MeasurePreserving (spatialShift k h)
        (volume : Measure (TimeVelocity d)) (volume : Measure (TimeVelocity d)) := by
      exact measurePreserving_add_right volume (0, h • PDE.basisVec k)
    have hEshift : AEStronglyMeasurable (fun z => E (spatialShift k h z))
        (volume : Measure (TimeVelocity d)) := by
      simpa only [Function.comp_def] using! hE.comp_quasiMeasurePreserving
        hshift.quasiMeasurePreserving
    have hEU : (fun z => E z) =ᵐ[timeVelocityVolumeOn S] U := by
      have hzero := Lp.coeFn_zeroExtendLinearIsometry hS (hU.toLp U)
      have hto := hU.coeFn_toLp
      have hmem : ∀ᵐ z ∂timeVelocityVolumeOn S, z ∈ S :=
        (ae_restrict_iff' hS).mpr (ae_of_all _ fun z hz => hz)
      filter_upwards [hzero.restrict, hto, hmem] with z hz hto hzS
      rw [hz, Set.indicator_of_mem hzS, hto]
    have hEUglobal : ∀ᵐ z ∂(volume : Measure (TimeVelocity d)),
        z ∈ S → E z = U z :=
      (ae_restrict_iff' hS).mp hEU
    have hEUshiftglobal : ∀ᵐ z ∂(volume : Measure (TimeVelocity d)),
        spatialShift k h z ∈ S → E (spatialShift k h z) = U (spatialShift k h z) := by
      simpa only [Function.comp_apply] using
        hshift.quasiMeasurePreserving.ae hEUglobal
    have hraw : (fun z => localizedSpatialDifferenceQuotient η k h
        (fun y => U (z.1, y)) z.2) =ᵐ[timeVelocityVolumeOn S]
        (fun z => localizedSpatialDifferenceQuotient η k h
          (fun y => E (z.1, y)) z.2) := by
      have hmem : ∀ᵐ z ∂timeVelocityVolumeOn S, z ∈ S :=
        (ae_restrict_iff' hS).mpr (ae_of_all _ fun z hz => hz)
      have hshiftOn : ∀ᵐ z ∂timeVelocityVolumeOn S,
          spatialShift k h z ∈ S → E (spatialShift k h z) = U (spatialShift k h z) :=
        (ae_restrict_iff' hS).mpr
          (hEUshiftglobal.mono fun z hz _ => hz)
      filter_upwards [hEU, hshiftOn, hmem] with z hEU hshift hzS
      rcases z with ⟨t, y⟩
      by_cases hη : η.toFun y = 0
      · simp [hη]
      have hzsupport := subset_tsupport η.toFun hη
      have hzshift : spatialShift k h (t, y) ∈ S := by
        rcases hzS with ⟨hztime, hzspace⟩
        refine ⟨?_, ?_⟩
        · change t + 0 ∈ reverseTimeOpenInterval T
          simpa using hztime
        simpa only [spatialShift_apply] using hηshift hzsupport
      simp only [localizedSpatialDifferenceQuotient_apply]
      change η.toFun y * ((U (t, y + h • PDE.basisVec k) - U (t, y)) / h) =
        η.toFun y * ((E (t, y + h • PDE.basisVec k) - E (t, y)) / h)
      have hshift' : E (t, y + h • PDE.basisVec k) =
          U (t, y + h • PDE.basisVec k) := by
        simpa only [spatialShift, Prod.mk_add_mk, add_zero] using hshift hzshift
      rw [← hEU, ← hshift']
    have hcoef : AEStronglyMeasurable (fun z : TimeVelocity d => η.toFun z.2)
        (volume : Measure (TimeVelocity d)) :=
      (η.smooth.continuous.comp continuous_snd).aestronglyMeasurable
    have hEraw : AEStronglyMeasurable
        (fun z => localizedSpatialDifferenceQuotient η k h
          (fun y => E (z.1, y)) z.2)
        (volume : Measure (TimeVelocity d)) := by
      have hmul := hcoef.mul (hEshift.sub hE)
      have hinv := hmul.mul_const h⁻¹
      apply hinv.congr
      filter_upwards with z
      simp only [localizedSpatialDifferenceQuotient_apply,
        Pi.sub_apply, Pi.mul_apply, div_eq_mul_inv]
      rw [← spatialShift_apply k h z.1 z.2]
      ring
    exact (hEraw.mono_measure Measure.restrict_le_self).congr hraw.symm
  have hOΩ : O ⊆ Ω := fun y hy =>
    η.tsupport_subset (subset_tsupport η.toFun (by
      change η.toFun y ≠ 0
      rw [η.eq_one_on_inner y (hOinner hy)]
      exact one_ne_zero))
  have hJO :=
    Set.prod_mono hJ hOΩ
  have hmO : (volume : Measure (TimeVelocity d)).restrict (J ×ˢ O) =
      (volume.restrict J).prod (PDE.volumeOn O) := by
    rw [volume_timeVelocity_eq_prod]
    simpa only [PDE.volumeOn] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (PDE.Vec d))) J O).symm
  have hDmeasProdO : AEStronglyMeasurable Dloc
      ((volume.restrict J).prod (PDE.volumeOn O)) := by
    rw [← hmO]
    exact hDmeas.mono_measure (Measure.restrict_mono_set volume hJO)
  have hQmeasProdO : AEStronglyMeasurable Q
      ((volume.restrict J).prod (PDE.volumeOn O)) := by
    have hmΩ : (volume : Measure (TimeVelocity d)).restrict (J ×ˢ Ω) =
        (volume.restrict J).prod (PDE.volumeOn Ω) := by
      rw [volume_timeVelocity_eq_prod]
      simpa only [PDE.volumeOn] using
        (Measure.prod_restrict (μ := (volume : Measure ℝ))
          (ν := (volume : Measure (PDE.Vec d))) J Ω).symm
    have hQmeasTVΩ : AEStronglyMeasurable Q
        ((volume : Measure (TimeVelocity d)).restrict (J ×ˢ Ω)) := by
      rw [hmΩ]
      exact hQ.aestronglyMeasurable
    rw [← hmO]
    exact hQmeasTVΩ.mono_measure
      (Measure.restrict_mono_set volume (Set.prod_mono subset_rfl hOΩ))
  have hQD : Q =ᵐ[timeVelocityVolumeOn (J ×ˢ O)]
      spatialDifferenceQuotient k h (G j) := by
    have hQDlocProd : Q =ᵐ[(volume.restrict J).prod (PDE.volumeOn O)] Dloc := by
      apply ae_prod_of_ae_ae_of_nullMeasurable
        (volume.restrict J) (PDE.volumeOn O)
      · exact hQmeasProdO.nullMeasurableSet_eq_fun hDmeasProdO
      · filter_upwards [hQslice, hDslice] with τ hQτ hDτ
        have hQτO := hQτ.filter_mono
          (ae_mono (Measure.restrict_mono hOΩ le_rfl))
        filter_upwards [hQτO, hDτ] with y hQy hDy
        exact hQy.trans hDy.symm
    rw [← hmO] at hQDlocProd
    have hplateau : Dloc =ᵐ[timeVelocityVolumeOn (J ×ˢ O)]
        spatialDifferenceQuotient k h (G j) := by
      apply (ae_restrict_iff' (hJmeas.prod hOopen.measurableSet)).mpr
      filter_upwards [] with z hz
      rcases z with ⟨τ, y⟩
      simp only [Dloc, localizedSpatialDifferenceQuotient_apply,
        η.eq_one_on_inner y (hOinner hz.2), one_mul,
        spatialDifferenceQuotient_apply, spatialTranslate_apply, spatialShift_apply]
    exact hQDlocProd.trans hplateau
  obtain ⟨hD, hDle⟩ : ∃ hD : ParabolicMemLpOn (J ×ˢ O) (2 : ℝ≥0∞) (spatialDifferenceQuotient k h (G j)),
      ‖hD.toLp (spatialDifferenceQuotient k h (G j))‖ ^ 2 ≤ ∫ τ, ‖q τ‖ ^ 2 ∂volume.restrict J := by
    let D := (spatialDifferenceQuotient k h (G j))
    have hQpar : ParabolicMemLpOn (J ×ˢ Ω) (2 : ℝ≥0∞) Q := by
      have hm : (volume : Measure (TimeVelocity d)).restrict (J ×ˢ Ω) =
          (volume.restrict J).prod (PDE.volumeOn Ω) := by
        rw [volume_timeVelocity_eq_prod]
        simpa only [PDE.volumeOn] using
          (Measure.prod_restrict (μ := (volume : Measure ℝ))
            (ν := (volume : Measure (PDE.Vec d))) J Ω).symm
      change MemLp Q (2 : ℝ≥0∞)
        ((volume : Measure (TimeVelocity d)).restrict (J ×ˢ Ω))
      rw [hm]
      exact hQ
    obtain ⟨hD, hDle⟩ :=
      exists_parabolicMemLpOn_of_product_ae_eq_restrict hQpar
        subset_rfl hOΩ hQD
    refine ⟨hD, ?_⟩
    have hQnorm : ‖hQ.toLp Q‖ =
        ‖(PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).compLpL
          (2 : ℝ≥0∞) (volume.restrict J) q‖ :=
      norm_uncurry_toLp_eq_of_ae_slice
        (volume.restrict J) (PDE.volumeOn Ω) _ Q hQ hQslice
    have hcoord : ‖(PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).compLpL
        (2 : ℝ≥0∞) (volume.restrict J) q‖ ≤ ‖q‖ := by
      calc
        _ ≤ ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j‖ * ‖q‖ :=
          ContinuousLinearMap.norm_compLp_le _ _
        _ ≤ 1 * ‖q‖ := by
          gcongr
          apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          intro G
          have _h_inl_13 : ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G‖ ≤ ‖G‖ := by
            rw [PDE.hilbertVectorLpCoord]
            calc
              ‖(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).compLpL
                  (2 : ℝ≥0∞) (PDE.volumeOn Ω) G‖ ≤
                  ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j‖ * ‖G‖ := by
                exact ContinuousLinearMap.norm_compLp_le _ _
              _ ≤ 1 * ‖G‖ := by
                gcongr
                apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
                intro x
                simpa only [ContinuousLinearMap.coe_coe, Function.comp_apply, one_mul] using!
                  PiLp.norm_apply_le x j
              _ = ‖G‖ := one_mul _
          simpa only [one_mul] using _h_inl_13
        _ = ‖q‖ := one_mul _
    have hDq : ‖hD.toLp D‖ ≤ ‖q‖ := by
      calc
        _ ≤ ‖hQpar.toLp Q‖ := hDle
        _ = ‖hQ.toLp Q‖ := by
          rw [Lp.norm_toLp, Lp.norm_toLp]
          congr 2
          change (volume : Measure (TimeVelocity d)).restrict (J ×ˢ Ω) = _
          rw [volume_timeVelocity_eq_prod]
          simpa only [PDE.volumeOn] using (Measure.prod_restrict
            (μ := (volume : Measure ℝ))
            (ν := (volume : Measure (PDE.Vec d))) J Ω).symm
        _ = _ := hQnorm
        _ ≤ _ := hcoord
    calc
      ‖hD.toLp D‖ ^ 2 ≤ ‖q‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hDq 2
      _ = ∫ τ, ‖q τ‖ ^ 2 ∂volume.restrict J := by
        have hto : (Lp.memLp q).toLp (fun τ => q τ) = q := by
          apply Lp.ext
          exact (Lp.memLp q).coeFn_toLp
        calc
          ‖q‖ ^ 2 = ‖(Lp.memLp q).toLp (fun τ => q τ)‖ ^ 2 := by rw [hto]
          _ = ∫ τ, ‖q τ‖ ^ 2 ∂volume.restrict J :=
            (integral_norm_sq_eq_norm_sq_toLp
              (fun τ => q τ) (Lp.memLp q)).symm
  refine ⟨hD, hDle.trans_eq ?_⟩
  apply integral_congr_ae
  filter_upwards [hq] with τ hqτ
  rw [hqτ]

private theorem integrable_norm_sq_timewise_clm_apply
    {d } {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T )
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : H10HilbertGraph hΩ →L[ℝ] E) (u : ReverseTimeL2V hΩ T) :
    Integrable (fun τ => ‖L (u τ)‖ ^ 2) (reverseTimeVolume T) := by
  let Lu := L.compLpL (2 : ℝ≥0∞) (reverseTimeVolume T) u
  have hLu :=
    ContinuousLinearMap.coeFn_compLpL L u
  refine (show Integrable (fun τ => ‖Lu τ‖ ^ 2) (reverseTimeVolume T) by
    simpa only [real_inner_self_eq_norm_sq] using
      L2.integrable_inner (𝕜 := ℝ) Lu Lu).congr ?_
  filter_upwards [hLu] with τ hτ
  rw [hτ]

/-! Raw gradient-coordinate representatives satisfy the uniform interior Caccioppoli bound. -/
namespace IsReverseTimeVariationalEnergySolution

/- Supplies raw gradient-coordinate representatives with uniform interior Caccioppoli bounds. -/
theorem exists_gradientCoord_representatives_uniform_interiorSpatialDifferenceQuotient_caccioppoli
    {d } {Ω inner O : Set (PDE.Vec d)} {Kη Kχ }
    (hd : 0 < d)
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (hOopen : IsOpen O) (hOnonempty : O.Nonempty) (hOinner : O ⊆ inner)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    ∃ (δ : ℝ) (hδ : 0 < δ)
        (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω),
      ∀ (τ₀ τ₁ τ₂ τ₃ : ℝ)
        (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁)
        (hτ₁τ₂ : τ₁ < τ₂) (hτ₂τ₃ : τ₂ < τ₃)
        (hτ₃ : τ₃ < r₁ - r₀),
      ∀ (lam Lam M : ℝ) (hlam : 0 < lam)
        (hlamLam : lam ≤ Lam) (hM : 0 ≤ M),
        ∃ C_cac : ℝ, 0 ≤ C_cac ∧
          ∀ (a : CoefficientField d)
            (b : ℝ → PDE.Vec d → PDE.Vec d)
            (c F : ℝ → PDE.Vec d → ℝ),
          ∀ (haSmooth : IsSmoothOnNeighborhood
                (fun z : TimeVelocity d => a z.1 z.2)
                (scalarParabolicClosedCylinder r₀ r₁ Ω))
            (hbSmooth : IsSmoothOnNeighborhood
                (fun z : TimeVelocity d => b z.1 z.2)
                (scalarParabolicClosedCylinder r₀ r₁ Ω))
            (hcSmooth : IsSmoothOnNeighborhood
                (fun z : TimeVelocity d => c z.1 z.2)
                (scalarParabolicClosedCylinder r₀ r₁ Ω))
            (hFSmooth : IsSmoothOnNeighborhood
                (fun z : TimeVelocity d => F z.1 z.2)
                (scalarParabolicClosedCylinder r₀ r₁ Ω))
            (hLower : ∀ z : TimeVelocity d,
                z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                  lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
            (hUpper : ∀ z : TimeVelocity d,
                z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                  a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
            (hcNonpos : ∀ z : TimeVelocity d,
                z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                  c z.1 z.2 ≤ 0)
            (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                spatialMatrixFDerivFrobeniusNorm
                  (fun w : TimeVelocity d =>
                    reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
            (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                PDE.vecEuclideanNorm
                  (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
            (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                spatialVectorFDerivFrobeniusNorm
                  (fun w : TimeVelocity d =>
                    reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
            (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
            (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                spatialScalarFDerivEuclideanNorm
                  (fun w : TimeVelocity d =>
                    -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
            (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                spatialScalarFDerivEuclideanNorm
                  (fun w : TimeVelocity d =>
                    -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
          ∀ (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
            (u : ReverseTimeL2V hΩ (r₁ - r₀))
            (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
            (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
              (sub_pos.mpr h₀₁) u g)
            (hu : IsReverseTimeVariationalEnergySolution
              r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
            ∃ G : Fin d → TimeVelocity d → ℝ,
              (∀ j, MemLp (G j) (2 : ℝ≥0∞)
                (timeVelocityVolumeOn
                  (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) ∧
              (∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ j,
                (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
                  fun y => gradientCLM hΩ (u τ) y j) ∧
              ∃ hDQmem : ∀ (j k : Fin d) (h : ℝ), 0 < h → h < δ →
                  ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O)
                    (2 : ℝ≥0∞) (spatialDifferenceQuotient k h (G j)),
                (∀ (j k : Fin d) (h : ℝ) (hh0 : 0 < h) (hhδ : h < δ),
                  ‖(hDQmem j k h hh0 hhδ).toLp
                      (spatialDifferenceQuotient k h (G j))‖ ^ 2 ≤
                    C_cac *
                      ((r₁ - r₀) +
                        (reverseTimeGalerkinPrimalRadius
                          r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
                          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
                          initial) ^ 2)) ∧
                ∀ (j k : Fin d) (h : ℝ) (hh0 : 0 < h) (hhδ : h < δ),
                  ‖(hDQmem j k h hh0 hhδ).toLp
                      (spatialDifferenceQuotient k h (G j))‖ ≤
                    Real.sqrt
                      (C_cac *
                        ((r₁ - r₀) +
                          (reverseTimeGalerkinPrimalRadius
                            r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
                            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
                            initial) ^ 2)) := by
  obtain ⟨δ, hδ, hcarrier, hcac⟩ :=
    exists_uniform_interiorSpatialDifferenceQuotient_caccioppoli
      hd r₀ r₁ h₀₁ hΩ hΩbounded η χ
  refine ⟨δ, hδ, hcarrier, ?_⟩
  intro τ₀ τ₁ τ₂ τ₃ hτ₀ hτ₀τ₁ hτ₁τ₂ hτ₂τ₃ hτ₃
  obtain ⟨ζ, Kζ, hKζ, hζnonneg, hζleOne, hζplateau, hζsupport, hζderiv⟩ : ∃ (ζ : ReverseTimeScalarTest (r₁ - r₀)) (Kζ : ℝ),
      0 ≤ Kζ ∧
      (∀ τ : ℝ, 0 ≤ ζ τ) ∧
      (∀ τ : ℝ, ζ τ ≤ 1) ∧
      (∀ τ ∈ Set.Icc τ₁ τ₂, ζ τ = 1) ∧
      tsupport (ζ : ℝ → ℝ) ⊆ Set.Ioo τ₀ τ₃ ∧
      ∀ τ : ℝ, |ζ.deriv τ| ≤ Kζ := by
    let T := (r₁ - r₀)
    have ha0 := hτ₀.le
    have hbc := hτ₁τ₂.le
    have hdT := hτ₃.le
    obtain ⟨ζ, hζnonneg, hζle_one, hζplateau, hζsupport⟩ :=
      exists_reverseTimeScalarTest_plateau T τ₀ τ₁ τ₂ τ₃ ha0 hτ₀τ₁ hbc hτ₂τ₃ hdT
    obtain ⟨C, hC⟩ := ζ.exists_norm_deriv_le
    refine ⟨ζ, max C 0, le_max_right C 0, hζnonneg, hζle_one, hζplateau, hζsupport, ?_⟩
    intro τ
    simpa only [Real.norm_eq_abs] using (hC τ).trans (le_max_left C 0)
  intro lam Lam M hlam hlamLam hM
  obtain ⟨C_cac, hC_cac, hcac'⟩ := hcac Kζ hKζ lam Lam M hlam hlamLam hM
  refine ⟨C_cac, hC_cac, ?_⟩
  intro a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
    hA hB hBD hq hqD hfD initial u g hdu hu
  obtain ⟨G, hGmem, hGslice⟩ : ∃ G : Fin d → TimeVelocity d → ℝ,
      (∀ j, MemLp (G j) (2 : ℝ≥0∞)
        (timeVelocityVolumeOn (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) ∧
      ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ j,
        (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
          fun y => gradientCLM hΩ (u τ) y j := by
    let T := (r₁ - r₀)
    letI : SFinite (PDE.volumeOn Ω) := by infer_instance
    choose G hG_memLp hG_slice using fun j =>
      HypoellipticAleksandrov.exists_uncurry_memLp_two
        (reverseTimeVolume T) (PDE.volumeOn Ω)
        (reverseTimeGradientCoordCLM hΩ T j u)
    refine ⟨G, ?_, ?_⟩
    · intro j
      rw [← reverseTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn T Ω]
      exact hG_memLp j
    · apply ae_all_iff.mpr
      intro j
      have _h_inl_10 : reverseTimeGradientCoordCLM hΩ T j u =ᵐ[reverseTimeVolume T]
        fun τ => PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
          (gradientCLM hΩ (u τ)) := by
          exact (
        ContinuousLinearMap.coeFn_compLpL
            ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).comp (gradientCLM hΩ)) u

        /- The scalar coordinates of a reverse-time `H¹₀` gradient have joint
        product representatives with a common almost-everywhere time-slice event. -/
        )
      filter_upwards [hG_slice j, _h_inl_10]
        with τ hG hcoord
      rw [hcoord] at hG
      exact hG.trans (PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
        (gradientCLM hΩ (u τ)))
  refine ⟨G, hGmem, hGslice, ?_⟩
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  let hDQmem : ∀ (j k : Fin d) (h : ℝ), 0 < h → h < δ →
      ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O) (2 : ℝ≥0∞)
        (spatialDifferenceQuotient k h (G j)) := by
    intro j k h hh0 hhδ
    have habs : |h| ≤ δ := by rw [abs_of_pos hh0]; exact hhδ.le
    have hχshift :=
      mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset
        hcarrier k habs
    have hηshift := hχshift.mono_left hηχ
    exact (exists_raw_gradientCoord_spatialDifferenceQuotient_memLp_norm_sq_le
      hΩ (r₁ - r₀) η hOopen hOinner (Set.Ioo τ₁ τ₂) measurableSet_Ioo
      (fun τ hτ => ⟨hτ₀.trans (hτ₀τ₁.trans hτ.1),
        hτ.2.trans (hτ₂τ₃.trans hτ₃)⟩)
      u G hGmem hGslice j k h hηshift).choose
  refine ⟨hDQmem, ?_⟩
  have hsqBound : ∀ (j k : Fin d) (h : ℝ) (hh0 : 0 < h) (hhδ : h < δ),
      ‖(hDQmem j k h hh0 hhδ).toLp
          (spatialDifferenceQuotient k h (G j))‖ ^ 2 ≤
        C_cac * ((r₁ - r₀) +
          (reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
            a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial) ^ 2) := by
    intro j k h hh0 hhδ
    have habs : |h| ≤ δ := by rw [abs_of_pos hh0]; exact hhδ.le
    have hχshift :=
      mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset
        hcarrier k habs
    have hηshift := hχshift.mono_left hηχ
    have hraw := (exists_raw_gradientCoord_spatialDifferenceQuotient_memLp_norm_sq_le
      hΩ (r₁ - r₀) η hOopen hOinner (Set.Ioo τ₁ τ₂) measurableSet_Ioo
      (fun τ hτ => ⟨hτ₀.trans (hτ₀τ₁.trans hτ.1),
        hτ.2.trans (hτ₂τ₃.trans hτ₃)⟩)
      u G hGmem hGslice j k h hηshift).choose_spec
    have henergy := hcac' ζ hζnonneg hζleOne hζderiv a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
      hA hB hBD hq hqD hfD initial u g hdu hu k h (by simpa [abs_of_pos hh0]) habs
    let A :=
      localizedSpatialDifferenceQuotientH10CLM hΩ η k h
        η.tsupport_subset hηshift
    let e : ℝ → ℝ := fun τ => ‖gradientCLM hΩ (A (u τ))‖ ^ 2
    have heInt : Integrable e (reverseTimeVolume (r₁ - r₀)) := by
      exact integrable_norm_sq_timewise_clm_apply
        hΩ (r₁ - r₀) ((gradientCLM hΩ).comp A) u
    have hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1 := by
      intro τ
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [hζnonneg τ], hζleOne τ⟩
    have hweightedInt :=
      heInt.bdd_mul ζ.contDiff.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hζunit)
    have hlocalWeighted : (∫ τ, e τ ∂volume.restrict (Set.Ioo τ₁ τ₂)) =
        ∫ τ in Set.Ioo τ₁ τ₂, ζ τ * e τ
          ∂reverseTimeVolume (r₁ - r₀) := by
      have hμ : (reverseTimeVolume (r₁ - r₀)).restrict (Set.Ioo τ₁ τ₂) =
          volume.restrict (Set.Ioo τ₁ τ₂) := by
        rw [reverseTimeVolume, Measure.restrict_restrict_of_subset]
        intro τ hτ
        exact ⟨hτ₀.trans (hτ₀τ₁.trans hτ.1),
          hτ.2.trans (hτ₂τ₃.trans hτ₃)⟩
      rw [← hμ]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
      rw [hζplateau τ ⟨hτ.1.le, hτ.2.le⟩, one_mul]
    have hlocalLe : (∫ τ, e τ ∂volume.restrict (Set.Ioo τ₁ τ₂)) ≤
        ∫ τ, ζ τ * e τ ∂reverseTimeVolume (r₁ - r₀) := by
      rw [hlocalWeighted]
      exact MeasureTheory.setIntegral_le_integral hweightedInt
        (Filter.Eventually.of_forall fun τ => mul_nonneg (hζnonneg τ) (sq_nonneg _))
    exact hraw.trans (hlocalLe.trans henergy)
  refine ⟨hsqBound, ?_⟩
  intro j k h hh0 hhδ
  let B := C_cac * ((r₁ - r₀) +
    (reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial) ^ 2)
  have hsq := hsqBound j k h hh0 hhδ
  have hB : 0 ≤ B := (sq_nonneg _).trans hsq
  exact (Real.le_sqrt (norm_nonneg _) hB).mpr hsq

end IsReverseTimeVariationalEnergySolution

end HypoellipticAleksandrov.Parabolic.Dirichlet
