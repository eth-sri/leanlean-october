module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10InteriorCaccioppoli
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGradientProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimePlateauCutoffDerivativeBound
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.H10CommutatorSmoothCore
import all HypoellipticAleksandrov.Parabolic.Dirichlet.H10IntegratedCoerciveConsequence
import all HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import HypoellipticAleksandrov.Measure.TimeVelocity


open private HypoellipticAleksandrov.Parabolic.Dirichlet.gradientCoord_localizedSpatialDifferenceQuotientH10CLM_eq from HypoellipticAleksandrov.Parabolic.Dirichlet.H10CommutatorSmoothCore
open private HypoellipticAleksandrov.Parabolic.Dirichlet.IsReverseTimeVariationalEnergySolution.integrable_norm_sq_timewise_apply from HypoellipticAleksandrov.Parabolic.Dirichlet.H10IntegratedCoerciveConsequence
open private HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds


/-! Transport of raw gradient representatives into interior Caccioppoli estimates. -/

 public section

open MeasureTheory Set
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise



namespace HypoellipticAleksandrov.Parabolic.Dirichlet
variable {d : ℕ}




private theorem gradientCoord_localizedSpatialDifferenceQuotientH10CLM_ae_eq_raw_on
     {Ω inner outer O : PDE.VelocityRegion d} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (hOopen : IsOpen O)
    (hOinner : O ⊆ inner)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
    (j : Fin d) (u : H10HilbertGraph hΩ) (g : PDE.ScalarField d)
    (hg : ⇑(PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
      =ᵐ[PDE.volumeOn Ω] g) :
    (fun y => PDE.hilbertVectorLpCoord Ω (2 ) j
        (gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u)) y)
      =ᵐ[PDE.volumeOn O]
        fun y => (g (y + h • PDE.basisVec k) - g y) / h := by
  have hclass := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.gradientCoord_localizedSpatialDifferenceQuotientH10CLM_eq
    hΩ η k h hηΩ hηshift j u
  have hadd := MeasureTheory.Lp.coeFn_add
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h (valueCLM hΩ u))
    (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
  have hcutoff := cutoffGradientSpatialDifferenceQuotientL2_apply_ae
    hΩ.measurableSet η j k h (valueCLM hΩ u)
  have hlocalized := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η k h
      _
      g hg hηshift
  have hOΩ : O ⊆ Ω := fun y hy =>
    hηΩ (subset_tsupport η.toFun (by
      change η.toFun y ≠ 0
      rw [η.eq_one_on_inner y (hOinner hy)]
      exact one_ne_zero))

  have hrestricted := (show ∀ᵐ y ∂PDE.volumeOn Ω,
      y ∈ O →
        PDE.hilbertVectorLpCoord Ω (2 ) j
            (gradientCLM hΩ
              (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u)) y =
          (g (y + h • PDE.basisVec k) - g y) / h by
      rw [hclass]
      filter_upwards [hadd, hcutoff, hlocalized] with y ha hc hl hyO
      rw [ha]
      simp only [Pi.add_apply]
      rw [hc, hl]
      rw [localizedSpatialDifferenceQuotient_apply,
        η.classicalGradient_eq_zero_of_mem_inner (hOinner hyO)]
      simp only [Pi.zero_apply, zero_mul, zero_add,
        η.eq_one_on_inner y (hOinner hyO), one_mul]).filter_mono
    (ae_mono (Measure.restrict_mono hOΩ le_rfl))
  filter_upwards [hrestricted, ae_restrict_mem hOopen.measurableSet] with y hy hyO
  exact hy hyO

private theorem ae_prod_of_ae_ae_of_nullMeasurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {p : α × β → Prop}
    (hp : NullMeasurableSet {z | p z} (μ.prod ν))
    (h : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x, y)) :
    ∀ᵐ z ∂μ.prod ν, p z := by


  have hsp : ∀ᵐ z ∂μ.prod ν, z ∈ (toMeasurable (μ.prod ν) {z | p z}) ↔ p z := by
    filter_upwards [hp.toMeasurable_ae_eq] with z hz
    exact iff_of_eq hz


  have hsprod  :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_toMeasurable _ _)).mpr (by
        filter_upwards [h, (Measure.ae_ae_of_ae_prod hsp)] with x hx hxs
        filter_upwards [hx, hxs] with y hy hys
        exact hys.symm.mp hy)
  filter_upwards [hsp, hsprod] with z hz hs'
  exact hz.mp hs'

variable {d : ℕ}

private theorem exists_parabolicMemLpOn_of_product_ae_eq_restrict
     {I J : Set ℝ} {Ω O : PDE.VelocityRegion d}
    {f g : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hf : ParabolicMemLpOn (I ×ˢ Ω) (2 ) f)
    (hJI : J ⊆ I) (hOΩ : O ⊆ Ω)
    (hfg : f =ᵐ[timeVelocityVolumeOn (J ×ˢ O)] g) :
    ∃ hg : ParabolicMemLpOn (J ×ˢ O) (2 ) g,
      ‖hg.toLp g‖ ≤ ‖hf.toLp f‖ := by
  have hsub  := Set.prod_mono hJI hOΩ


  refine ⟨((hf.mono_measure (Measure.restrict_mono_set volume hsub)).ae_eq hfg), ?_⟩
  rw [Lp.norm_toLp, Lp.norm_toLp, ← eLpNorm_congr_ae hfg]
  refine ENNReal.toReal_mono hf.eLpNorm_ne_top ?_
  exact eLpNorm_mono_measure f (Measure.restrict_mono_set volume hsub)

variable {Ω : PDE.VelocityRegion d}




private theorem norm_timeCoordinate_le
      {μ : Measure ℝ}
    (j : Fin d)
    (q : Lp (PDE.HilbertVectorLp Ω (2 )) (2 ) μ) :
    ‖(PDE.hilbertVectorLpCoord Ω (2 ) j).compLpL
        (2 ) μ q‖ ≤ ‖q‖ := by
  calc
    _ ≤ ‖PDE.hilbertVectorLpCoord Ω (2 ) j‖ * ‖q‖ :=
      ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ 1 * ‖q‖ := by
      gcongr
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro G
      simpa only [one_mul] using _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le j G
    _ = ‖q‖ := one_mul _

private theorem norm_uncurry_toLp_eq_of_ae_slice
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (q : Lp (Lp ℝ (2 ) ν) (2 ) μ)
    (Q : α × β → ℝ)
    (hQ : MemLp Q (2 ) (μ.prod ν))
    (hslice : ∀ᵐ x ∂μ,
      (fun y => Q (x, y)) =ᵐ[ν] fun y => q x y) :
    ‖hQ.toLp Q‖ = ‖q‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0)
  calc
    eLpNorm Q (2 ) (μ.prod ν) ^ (2 : ℝ) =
        ∫⁻ z, ‖Q z‖ₑ ^ (2 : ℝ) ∂μ.prod ν := by
      simpa using (eLpNorm_nnreal_pow_eq_lintegral
        (f := Q) (μ := μ.prod ν) (p := (2 )) (by norm_num) hQ.aestronglyMeasurable)
    _ = ∫⁻ x, ∫⁻ y, ‖Q (x, y)‖ₑ ^ (2 : ℝ) ∂ν ∂μ :=
      lintegral_prod _ (hQ.aestronglyMeasurable.enorm.pow aemeasurable_const)
    _ = ∫⁻ x, ‖q x‖ₑ ^ (2 : ℝ) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hslice] with x hx
      rw [Lp.enorm_def, ← eLpNorm_congr_ae hx]
      exact (eLpNorm_nnreal_pow_eq_lintegral
        (f := fun y => Q (x, y)) (μ := ν) (p := (2 )) (by norm_num)
          ((Lp.memLp (q x)).aestronglyMeasurable.congr hx.symm)).symm
    _ = eLpNorm q (2 ) μ ^ (2 : ℝ) := by
      simpa using (eLpNorm_nnreal_pow_eq_lintegral
        (f := q) (μ := μ) (p := (2 )) (by norm_num)
        (Lp.memLp q).aestronglyMeasurable).symm

variable {d : ℕ}

private theorem exists_raw_restrict_norm_sq_le_integral_vector
     {Ω O : PDE.VelocityRegion d}
    (J : Set ℝ) (hOΩ : O ⊆ Ω)
    (q : Lp (PDE.HilbertVectorLp Ω (2 )) (2 )
      (volume.restrict J))
    (j : Fin d)
    (Q D : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hQ : MemLp Q (2 )
      ((volume.restrict J).prod (PDE.volumeOn Ω)))
    (hQslice : ∀ᵐ τ ∂volume.restrict J,
      (fun y => Q (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => ((PDE.hilbertVectorLpCoord Ω (2 ) j).compLpL
          (2 ) (volume.restrict J) q) τ y)
    (hQD : Q =ᵐ[timeVelocityVolumeOn (J ×ˢ O)] D) :
    ∃ hD : ParabolicMemLpOn (J ×ˢ O) (2 ) D,
      ‖hD.toLp D‖ ^ 2 ≤ ∫ τ, ‖q τ‖ ^ 2 ∂volume.restrict J := by
  let sharedTerm_4c4965a92f := (∫ τ, ‖q τ‖ ^ 2 ∂volume.restrict J)
  have hQpar : ParabolicMemLpOn (J ×ˢ Ω) (2 ) Q := by
    have hm : (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict (J ×ˢ Ω) =
        (volume.restrict J).prod (PDE.volumeOn Ω) := by
      rw [timeVelocityVolume, volume_timeVelocity_eq_prod]
      simpa only [PDE.volumeOn] using
        (Measure.prod_restrict (μ := (volume : Measure ℝ))
          (ν := (volume : Measure (PDE.Vec d))) J Ω).symm
    change MemLp Q (2 )
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict (J ×ˢ Ω))
    rw [hm]
    exact hQ
  obtain ⟨hD, hDle⟩ :=
    exists_parabolicMemLpOn_of_product_ae_eq_restrict hQpar
      subset_rfl hOΩ hQD
  refine ⟨hD, ?_⟩
  have hQnorm : ‖hQ.toLp Q‖ =
      ‖(PDE.hilbertVectorLpCoord Ω (2 ) j).compLpL
        (2 ) (volume.restrict J) q‖ :=
    norm_uncurry_toLp_eq_of_ae_slice
      _ _ _ Q hQ hQslice


  calc
    ‖hD.toLp D‖ ^ 2 ≤ ‖q‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (by
          calc
            _ ≤ ‖hQpar.toLp Q‖ := hDle
            _ = ‖hQ.toLp Q‖ := by
              rw [Lp.norm_toLp, Lp.norm_toLp]
              congr 2
              change (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict (J ×ˢ Ω) = _
              rw [timeVelocityVolume, volume_timeVelocity_eq_prod]
              exact (Measure.prod_restrict
                (μ := (volume : Measure ℝ))
                (ν := (volume : Measure (PDE.Vec d))) J Ω).symm
            _ = _ := hQnorm
            _ ≤ _ := (norm_timeCoordinate_le j q)) 2
    _ = sharedTerm_4c4965a92f := by
      let sharedTerm_ef836d38de := ((Lp.memLp q).toLp (fun τ => q τ))
      have hto : sharedTerm_ef836d38de = q := by
        apply Lp.ext
        exact (Lp.memLp q).coeFn_toLp
      calc
        ‖q‖ ^ 2 = ‖sharedTerm_ef836d38de‖ ^ 2 := by rw [hto]
        _ = sharedTerm_4c4965a92f :=
          (integral_norm_sq_eq_norm_sq_toLp
            (fun τ => q τ) (Lp.memLp q)).symm

private theorem localizedSpatialDifferenceQuotient_aestronglyMeasurable
     {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (hΩ : IsOpen Ω) (T : ℝ)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (U : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hU : ParabolicMemLpOn (reverseTimeOpenInterval T ×ˢ Ω)
      (2 ) U)
    (k : Fin d) (h : ℝ)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    AEStronglyMeasurable
      (fun z => localizedSpatialDifferenceQuotient η k h
        (fun y => U (z.1, y)) z.2)
      (timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω)) := by
  let sharedTerm_4bf0c9395d := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  let S  := reverseTimeOpenInterval T ×ˢ Ω
  have hS : MeasurableSet S := measurableSet_Ioo.prod hΩ.measurableSet
  let E : Lp ℝ (2 ) sharedTerm_4bf0c9395d :=
    Lp.zeroExtendLinearIsometry hS (hU.toLp U)
  have hE : AEStronglyMeasurable (fun z => E z)
      sharedTerm_4bf0c9395d :=
    Lp.memLp E |>.aestronglyMeasurable
  have hshift : MeasurePreserving (spatialShift k h)
      sharedTerm_4bf0c9395d sharedTerm_4bf0c9395d := by
    change MeasurePreserving (fun z : TimeVelocity d => z + (0, h • PDE.basisVec k))
      volume volume
    exact measurePreserving_add_right volume _
  have hEshift : AEStronglyMeasurable (fun z => E (spatialShift k h z))
      sharedTerm_4bf0c9395d := by
    simpa only [Function.comp_def] using! hE.comp_quasiMeasurePreserving
      hshift.quasiMeasurePreserving
  have hEU : (fun z => E z) =ᵐ[timeVelocityVolumeOn S] U := by
    have hzero := Lp.coeFn_zeroExtendLinearIsometry hS (hU.toLp U)
    have hto := hU.coeFn_toLp

    filter_upwards [hzero.restrict, hto, ((ae_restrict_iff' hS).mpr (ae_of_all _ fun z hz => hz))] with z hz hto hzS
    rw [hz, Set.indicator_of_mem hzS, hto]
  have hEUglobal : ∀ᵐ z ∂sharedTerm_4bf0c9395d,
      z ∈ S → E z = U z :=
    (ae_restrict_iff' hS).mp hEU


  have hcoef : AEStronglyMeasurable (fun z : TimeVelocity d => η.toFun z.2)
      sharedTerm_4bf0c9395d :=
    (η.smooth.continuous.comp continuous_snd).aestronglyMeasurable
  have hEraw : AEStronglyMeasurable
      (fun z => localizedSpatialDifferenceQuotient η k h
        (fun y => E (z.1, y)) z.2)
      sharedTerm_4bf0c9395d := by


    apply ((hcoef.mul (hEshift.sub hE)).mul_const h⁻¹).congr
    filter_upwards with z
    simp only [localizedSpatialDifferenceQuotient_apply,
      Pi.sub_apply, Pi.mul_apply, div_eq_mul_inv]
    rw [← spatialShift_apply k h z.1 z.2]
    ring
  exact (hEraw.mono_measure Measure.restrict_le_self).congr (show (fun z => localizedSpatialDifferenceQuotient η k h
      (fun y => U (z.1, y)) z.2) =ᵐ[timeVelocityVolumeOn S]
      (fun z => localizedSpatialDifferenceQuotient η k h
        (fun y => E (z.1, y)) z.2) by

      have hshiftOn  :=
        (ae_restrict_iff' hS).mpr
          ((show ∀ᵐ z ∂sharedTerm_4bf0c9395d,
        spatialShift k h z ∈ S → E (spatialShift k h z) = U (spatialShift k h z) by
              simpa only using hshift.quasiMeasurePreserving.ae hEUglobal).mono fun z hz _ => hz)
      filter_upwards [hEU, hshiftOn, ((ae_restrict_iff' hS).mpr (ae_of_all _ fun z hz => hz))] with z hEU hshift hzS
      rcases z with ⟨t, y⟩
      by_cases hη : η.toFun y = 0
      · simp [hη]
      have hzsupport  := subset_tsupport η.toFun hη

      simp only [localizedSpatialDifferenceQuotient_apply]
      change η.toFun y * ((U (t, y + h • PDE.basisVec k) - U (t, y)) / h) =
        η.toFun y * ((E (t, y + h • PDE.basisVec k) - E (t, y)) / h)
      have hshift' : E (t, y + h • PDE.basisVec k) =
          U (t, y + h • PDE.basisVec k) := by
        simpa only [spatialShift, Prod.mk_add_mk, add_zero] using hshift (by
            rcases hzS with ⟨hztime, hzspace⟩
            refine ⟨?_, ?_⟩
            · simp_all [reverseTimeOpenInterval]
            exact hηshift hzsupport)
      rw [← hEU, ← hshift']).symm

private theorem exists_raw_gradientCoord_spatialDifferenceQuotient_memLp_norm_sq_le
     {Ω inner O : PDE.VelocityRegion d} {Kη : ℝ}
    (hΩ : IsOpen Ω) (T : ℝ)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (hOopen : IsOpen O) (hOinner : O ⊆ inner)
    (J : Set ℝ) (hJmeas : MeasurableSet J)
    (hJ : J ⊆ reverseTimeOpenInterval T)
    (u : ReverseTimeL2V hΩ T)
    (G : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hGmem : ∀ i, MemLp (G i) (2 )
      (timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω)))
    (hGslice : ∀ᵐ τ ∂reverseTimeVolume T, ∀ i,
      (fun y => G i (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => gradientCLM hΩ (u τ) y i)
    (j k : Fin d) (h : ℝ)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ∃ hD : ParabolicMemLpOn (J ×ˢ O) (2 )
        (spatialDifferenceQuotient k h (G j)),
      ‖hD.toLp (spatialDifferenceQuotient k h (G j))‖ ^ 2 ≤
        ∫ τ,
          ‖gradientCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM hΩ η k h
              η.tsupport_subset hηshift (u τ))‖ ^ 2
          ∂volume.restrict J := by
  let sharedTerm_820fcebc6a := (((volume.restrict J).prod (PDE.volumeOn O)))
  let sharedTerm_828870c7da := ((PDE.hilbertVectorLpCoord Ω (2 ) j))
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h
      η.tsupport_subset hηshift
  let qFull : Lp (PDE.HilbertVectorLp Ω (2 )) (2 )
      (reverseTimeVolume T) :=
    ((gradientCLM hΩ).comp A).compLpL (2 ) (reverseTimeVolume T) u
  have hμJ : (reverseTimeVolume T).restrict J = volume.restrict J := by
    rw [reverseTimeVolume, Measure.restrict_restrict_of_subset hJ]
  let Dloc : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z =>
    localizedSpatialDifferenceQuotient η k h (fun y => G j (z.1, y)) z.2

  have hqMem : MemLp (fun τ => qFull τ) (2 ) (volume.restrict J) := by
    rw [← hμJ]
    exact (Lp.memLp qFull).restrict J
  let q : Lp (PDE.HilbertVectorLp Ω (2 )) (2 )
      (volume.restrict J) := hqMem.toLp (fun τ => qFull τ)
  obtain ⟨Q, hQ, hQslice⟩ :=
    HypoellipticAleksandrov.exists_uncurry_memLp_two
      (volume.restrict J) (PDE.volumeOn Ω)
      (sharedTerm_828870c7da.compLpL
        (2 ) (volume.restrict J) q)
  have hq : ∀ᵐ τ ∂volume.restrict J,
      q τ = gradientCLM hΩ (A (u τ)) := by

    filter_upwards [hqMem.coeFn_toLp, (by
        rw [← hμJ]
        exact ae_restrict_of_ae (show ∀ᵐ τ ∂reverseTimeVolume T,
        qFull τ = gradientCLM hΩ (A (u τ)) by
            exact ContinuousLinearMap.coeFn_compLpL ((gradientCLM hΩ).comp A) u))] with τ hR hF
    exact hR.trans hF


  have hDmeas  :=
    localizedSpatialDifferenceQuotient_aestronglyMeasurable
      hΩ T η (G j) (hGmem j) k h hηshift
  have hOΩ : O ⊆ Ω := fun y hy =>
    η.tsupport_subset (subset_tsupport η.toFun (by
      change η.toFun y ≠ 0
      rw [η.eq_one_on_inner y (hOinner hy)]
      exact one_ne_zero))
  have hJO  :=
    Set.prod_mono hJ hOΩ
  have hmO : (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict (J ×ˢ O) =
      sharedTerm_820fcebc6a := by
    rw [timeVelocityVolume, volume_timeVelocity_eq_prod]
    simpa only [PDE.volumeOn] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (PDE.Vec d))) J O).symm

  have hQmeasProdO : AEStronglyMeasurable Q
      sharedTerm_820fcebc6a := by
    have hmΩ : (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict (J ×ˢ Ω) =
        (volume.restrict J).prod (PDE.volumeOn Ω) := by
      rw [timeVelocityVolume, volume_timeVelocity_eq_prod]
      exact (Measure.prod_restrict (μ := (volume : Measure ℝ))
          (ν := (volume : Measure (PDE.Vec d))) J Ω).symm

    rw [← hmO]
    exact (show AEStronglyMeasurable Q
        ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict (J ×ˢ Ω)) by
        rw [hmΩ]
        exact hQ.aestronglyMeasurable).mono_measure
      (Measure.restrict_mono_set volume (Set.prod_mono subset_rfl hOΩ))
  have hQD : Q =ᵐ[timeVelocityVolumeOn (J ×ˢ O)]
      spatialDifferenceQuotient k h (G j) := by
    have hQDlocProd : Q =ᵐ[sharedTerm_820fcebc6a] Dloc := by
      apply ae_prod_of_ae_ae_of_nullMeasurable
        (volume.restrict J) (PDE.volumeOn O)
      · exact hQmeasProdO.nullMeasurableSet_eq_fun (show AEStronglyMeasurable Dloc
      sharedTerm_820fcebc6a by
          rw [← hmO]
          exact hDmeas.mono_measure (Measure.restrict_mono_set volume hJO))
      · filter_upwards [hQslice, (show ∀ᵐ τ ∂volume.restrict J,
      (fun y => Dloc (τ, y)) =ᵐ[PDE.volumeOn O]
        fun y => (sharedTerm_828870c7da.compLpL
          (2 ) (volume.restrict J) q) τ y by
          filter_upwards [hq, (show ∀ᵐ τ ∂volume.restrict J,
      (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => PDE.hilbertVectorLpCoord Ω (2 ) j
          (gradientCLM hΩ (u τ)) y by
              rw [← hμJ]
              filter_upwards [ae_restrict_of_ae hGslice] with τ hτ
              filter_upwards [hτ j,
                PDE.coeFn_hilbertVectorLpCoord Ω _ j
                  (gradientCLM hΩ (u τ))] with y hG hcoord
              exact hG.trans hcoord.symm),
            ContinuousLinearMap.coeFn_compLpL
              sharedTerm_828870c7da q] with τ hqτ hGτ hcoord
          have hs := gradientCoord_localizedSpatialDifferenceQuotientH10CLM_ae_eq_raw_on
            hΩ η hOopen hOinner k h η.tsupport_subset hηshift j (u τ)
            (fun y => G j (τ, y)) hGτ.symm
          filter_upwards [hs, ae_restrict_mem hOopen.measurableSet] with y hs hyO
          change localizedSpatialDifferenceQuotient η k h
              (fun y => G j (τ, y)) y = _
          rw [localizedSpatialDifferenceQuotient_apply,
            η.eq_one_on_inner y (hOinner hyO)]
          simp only [one_mul]
          rw [hcoord, hqτ]
          exact hs.symm)] with τ hQτ hDτ
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
  obtain ⟨hD, hDle⟩ := exists_raw_restrict_norm_sq_le_integral_vector
    J hOΩ q j Q
      _ hQ hQslice hQD
  refine ⟨hD, hDle.trans_eq ?_⟩
  apply integral_congr_ae
  filter_upwards [hq] with τ hqτ
  rw [hqτ]




/-! Raw gradient-coordinate representatives satisfy the uniform interior Caccioppoli bound. -/
namespace IsReverseTimeVariationalEnergySolution

/-- Supplies raw gradient-coordinate representatives with uniform interior Caccioppoli bounds. -/
theorem exists_gradientCoord_representatives_uniform_interiorSpatialDifferenceQuotient_caccioppoli
    {d : ℕ} {Ω inner O : PDE.VelocityRegion d} {Kη Kχ : ℝ}
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
            (b : PDE.TimeVectorField d)
            (c F : PDE.TimeScalarField d),
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
                  (fun w  =>
                    reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
            (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                PDE.vecEuclideanNorm
                  (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
            (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                spatialVectorFDerivFrobeniusNorm
                  (fun w  =>
                    reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
            (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
            (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                spatialScalarFDerivEuclideanNorm
                  (fun w  =>
                    -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
            (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                spatialScalarFDerivEuclideanNorm
                  (fun w  =>
                    -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
          ∀ (initial : PDE.ScalarLp Ω (2 ))
            (u : ReverseTimeL2V hΩ (r₁ - r₀))
            (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
            (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
              (sub_pos.mpr h₀₁) u g)
            (hu : IsReverseTimeVariationalEnergySolution
              r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
            ∃ G : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d,
              (∀ j, MemLp (G j) (2 )
                (timeVelocityVolumeOn
                  (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) ∧
              (∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ j,
                (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
                  fun y => gradientCLM hΩ (u τ) y j) ∧
              ∃ hDQmem : ∀ (j k : Fin d) (h : ℝ), 0 < h → h < δ →
                  ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O)
                    (2 ) (spatialDifferenceQuotient k h (G j)),
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
  obtain ⟨ζ, Kζ, hKζ, hζnonneg, hζleOne, hζplateau, hζsupport, hζderiv⟩ :=
    exists_reverseTimeScalarTest_plateau_with_deriv_bound
      (r₁ - r₀) τ₀ τ₁ τ₂ τ₃ hτ₀.le hτ₀τ₁ hτ₁τ₂.le hτ₂τ₃ hτ₃.le
  intro lam Lam M hlam hlamLam hM
  obtain ⟨C_cac, hC_cac, hcac'⟩ := hcac Kζ hKζ lam Lam M hlam hlamLam hM
  refine ⟨C_cac, hC_cac, ?_⟩
  intro a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
    hA hB hBD hq hqD hfD initial u g hdu hu
  obtain ⟨G, hGmem, hGslice⟩ :=
    exists_reverseTimeL2V_gradient_coord_product_representatives
      hΩ (r₁ - r₀) u
  refine ⟨G, hGmem, hGslice, ?_⟩
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  let hDQmem : ∀ (j k : Fin d) (h : ℝ), 0 < h → h < δ →
      ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O) (2 )
        (spatialDifferenceQuotient k h (G j)) := by
    intro j k h hh0 hhδ
    have habs : |h| ≤ δ := by rw [abs_of_pos hh0]; exact hhδ.le
    have hχshift :=
      mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset
        hcarrier k habs
    have hηshift  := hχshift.mono_left hηχ
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
    have hηshift  := hχshift.mono_left hηχ
    have hraw := (exists_raw_gradientCoord_spatialDifferenceQuotient_memLp_norm_sq_le
      hΩ (r₁ - r₀) η hOopen hOinner (Set.Ioo τ₁ τ₂) measurableSet_Ioo
      (fun τ hτ => ⟨hτ₀.trans (hτ₀τ₁.trans hτ.1),
        hτ.2.trans (hτ₂τ₃.trans hτ₃)⟩)
      u G hGmem hGslice j k h hηshift).choose_spec
    have henergy := hcac' ζ hζnonneg hζleOne hζderiv a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
      hA hB hBD hq hqD hfD initial u g hdu hu k h (by simpa [abs_of_pos hh0]) habs
    let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
      localizedSpatialDifferenceQuotientH10CLM hΩ η k h
        η.tsupport_subset hηshift
    let e : ℝ → ℝ := fun τ => ‖gradientCLM hΩ (A (u τ))‖ ^ 2


    have hweightedInt  :=
      (show Integrable e (reverseTimeVolume (r₁ - r₀)) by
          exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.IsReverseTimeVariationalEnergySolution.integrable_norm_sq_timewise_apply
            hΩ (r₁ - r₀) ((gradientCLM hΩ).comp A) u).bdd_mul ζ.contDiff.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall (by
            intro τ
            rw [Real.norm_eq_abs]
            exact abs_le.2 ⟨by linarith [hζnonneg τ], hζleOne τ⟩))
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

    exact hraw.trans ((show (∫ τ, e τ ∂volume.restrict (Set.Ioo τ₁ τ₂)) ≤
        ∫ τ, ζ τ * e τ ∂reverseTimeVolume (r₁ - r₀) by
        rw [hlocalWeighted]
        exact MeasureTheory.setIntegral_le_integral hweightedInt
          (Filter.Eventually.of_forall fun τ => mul_nonneg (hζnonneg τ) (sq_nonneg _))).trans henergy)
  refine ⟨hsqBound, ?_⟩
  intro j k h hh0 hhδ

  have hsq  := hsqBound j k h hh0 hhδ

  exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans hsq)).mpr hsq

end IsReverseTimeVariationalEnergySolution

end HypoellipticAleksandrov.Parabolic.Dirichlet
