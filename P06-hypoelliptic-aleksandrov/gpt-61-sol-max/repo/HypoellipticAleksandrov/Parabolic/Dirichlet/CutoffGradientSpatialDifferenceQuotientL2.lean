module

public import PDEFoundation.Sobolev.Cutoff.Basic
public import HypoellipticAleksandrov.Measure.LpZeroExtension
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Multiplier
public import PDEFoundation.Measure.AffineVolume

/-!
# Cutoff-gradient spatial difference quotients on restricted `L²`

This module constructs the representative-independent scalar restricted-`L²`
operator `(D_j η) Δ_{k,h}` using ambient zero extension, global translation,
restriction, and the bounded scalar multiplier.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A cutoff gradient coordinate is measurable for restricted volume. -/
theorem cutoffGradient_aestronglyMeasurable
    {d : ℕ} {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (j : Fin d) :
    AEStronglyMeasurable (fun y => PDE.classicalGradient η.toFun y j)
      (PDE.volumeOn Ω) := by

  exact (show Continuous (fun y => PDE.classicalGradient η.toFun y j) by
      simpa only [PDE.classicalGradient_apply] using
        (η.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable

variable {d : ℕ}

/-- A cutoff gradient coordinate obeys the cutoff bound almost everywhere. -/
theorem cutoffGradient_norm_le
     {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (j : Fin d) :
    ∀ᵐ y ∂PDE.volumeOn Ω, ‖PDE.classicalGradient η.toFun y j‖ ≤ K :=
  ae_of_all _ fun y => by
    rw [Real.norm_eq_abs]
    exact η.abs_classicalGradient_apply_le y j

private theorem cutoffGradient_eq_zero_of_not_mem_tsupport
     {inner outer : PDE.VelocityRegion d} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (j : Fin d)
    {y : PDE.Vec d} (hy : y ∉ tsupport η.toFun) :
    PDE.classicalGradient η.toFun y j = 0 := by
  rw [PDE.classicalGradient_apply, fderiv_of_notMem_tsupport ℝ hy]
  exact ContinuousLinearMap.zero_apply _

variable {Ω inner outer : PDE.VelocityRegion d} {K : ℝ} (hΩ : MeasurableSet Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K) (j k : Fin d) (h : ℝ)

/-- The cutoff-coordinate-gradient times forward spatial difference quotient
on restricted-volume scalar `L²`, totalized at zero increment. -/
def cutoffGradientSpatialDifferenceQuotientL2
       :=
  let μ : Measure (PDE.Vec d) := volume
  let z : PDE.Vec d := h • PDE.basisVec k
  let T : PDE.VectorField d := fun y => y + z
  let hT : MeasurePreserving T μ μ :=
    measurePreserving_add_right μ z
  let E : PDE.ScalarLp Ω (2 ) →L[ℝ]
      Lp ℝ (2 ) μ :=
    (Lp.zeroExtendLinearIsometry (μ := μ) hΩ).toContinuousLinearMap
  let P : Lp ℝ (2 ) μ →L[ℝ]
      Lp ℝ (2 ) μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap
  let R : Lp ℝ (2 ) μ →L[ℝ]
      PDE.ScalarLp Ω (2 ) :=
    LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ μ _ Ω
  let M : PDE.ScalarLp Ω (2 ) →L[ℝ]
      PDE.ScalarLp Ω (2 ) :=
    scalarL2Multiplier (fun y => PDE.classicalGradient η.toFun y j)
      (cutoffGradient_aestronglyMeasurable η j) K η.gradient_bound_nonneg
      (cutoffGradient_norm_le η j)
  h⁻¹ • M.comp (R.comp (P.comp E - E))

variable (f : PDE.ScalarLp Ω (2 ))

/-- The cutoff-gradient quotient uses the canonical global zero extension. -/
theorem cutoffGradientSpatialDifferenceQuotientL2_apply_ae
       :
    ⇑(cutoffGradientSpatialDifferenceQuotientL2 hΩ η j k h f)
      =ᵐ[PDE.volumeOn Ω] fun y =>
        PDE.classicalGradient η.toFun y j *
          ((⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)
              (y + h • PDE.basisVec k) -
            ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y) / h) := by
  let sharedTerm_d649a1aca8 := ((measurePreserving_add_right (volume : Measure (PDE.Vec d)) (h • PDE.basisVec k)))
  let sharedTerm_5a5c88f953 := ((fun y : PDE.Vec d => y + h • PDE.basisVec k))
  let sharedTerm_96fadcb221 := ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω))
  unfold cutoffGradientSpatialDifferenceQuotientL2
  dsimp only
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, LinearIsometry.coe_toContinuousLinearMap]
  have hP :
      ⇑((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        sharedTerm_5a5c88f953
        sharedTerm_d649a1aca8)
        ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)) =ᵐ[volume]
        (⇑((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) ∘
          sharedTerm_5a5c88f953) := by
    change MeasureTheory.Lp.compMeasurePreserving
      sharedTerm_5a5c88f953
      sharedTerm_d649a1aca8 ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) =ᵐ[volume]
        (⇑((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) ∘
          sharedTerm_5a5c88f953)
    exact MeasureTheory.Lp.coeFn_compMeasurePreserving
      _
      sharedTerm_d649a1aca8
  have hR := LpToLpRestrictCLM_coeFn ℝ Ω
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      sharedTerm_5a5c88f953
      sharedTerm_d649a1aca8) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
      (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
  have hM := scalarL2Multiplier_apply_ae
    (fun y => PDE.classicalGradient η.toFun y j)
    (cutoffGradient_aestronglyMeasurable η j) K η.gradient_bound_nonneg
    (cutoffGradient_norm_le η j)
    (sharedTerm_96fadcb221
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        sharedTerm_5a5c88f953
        sharedTerm_d649a1aca8) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
  have hsub := MeasureTheory.Lp.coeFn_sub
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      sharedTerm_5a5c88f953
      sharedTerm_d649a1aca8) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
    ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
  have hsmul := MeasureTheory.Lp.coeFn_smul h⁻¹
    ((scalarL2Multiplier (fun y => PDE.classicalGradient η.toFun y j)
      (cutoffGradient_aestronglyMeasurable η j) K η.gradient_bound_nonneg
      (cutoffGradient_norm_le η j)
      (sharedTerm_96fadcb221
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          sharedTerm_5a5c88f953
          sharedTerm_d649a1aca8) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))))
  filter_upwards [hsmul, hM, hR, hsub.restrict, hP.restrict] with y hsmul hM hR hsub hP
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hM, hR, hsub]
  simp only [Pi.sub_apply]
  rw [hP]
  simp only [Function.comp_apply, div_eq_mul_inv]
  ring

/-- A supplied representative gives the literal cutoff-gradient quotient
under the forward active-support collar. -/
theorem cutoffGradientSpatialDifferenceQuotientL2_apply_ae_of_ae_eq

    (g : PDE.ScalarField d)
    (hfg : ⇑f =ᵐ[PDE.volumeOn Ω] g)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ⇑(cutoffGradientSpatialDifferenceQuotientL2 hΩ η j k h f)
      =ᵐ[PDE.volumeOn Ω] fun y =>
        PDE.classicalGradient η.toFun y j *
          ((g (y + h • PDE.basisVec k) - g y) / h) := by
  have hzero := MeasureTheory.Lp.coeFn_zeroExtendLinearIsometry hΩ f

  have hambient : ∀ᵐ y : PDE.Vec d,
      y ∈ Ω → ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y = g y := by
    filter_upwards [hzero, (ae_imp_of_ae_restrict hfg)] with y hzero hfg hy
    rw [hzero, Set.indicator_of_mem hy]
    exact hfg hy
  have hshifted := (measurePreserving_add_right (volume : Measure (PDE.Vec d))
    (h • PDE.basisVec k)).quasiMeasurePreserving.ae hambient



  filter_upwards [cutoffGradientSpatialDifferenceQuotientL2_apply_ae hΩ η j k h f,
    ((ae_restrict_iff' hΩ).mpr (hambient.mono fun _ hy _ => hy)), ((ae_restrict_iff' hΩ).mpr (hshifted.mono fun _ hy _ => hy)), ((ae_restrict_iff' hΩ).mpr (ae_of_all _ fun y hy => hy))] with y hq hy hyshift hymem
  rw [hq]
  by_cases hgradient : PDE.classicalGradient η.toFun y j = 0
  · have hgradient' : (fderiv ℝ η.toFun y) (PDE.basisVec j) = 0 := by
      exact hgradient
    simp [hgradient']

  have hyshiftmem  := hηshift (by
      by_contra hytsupport
      exact hgradient (cutoffGradient_eq_zero_of_not_mem_tsupport η j hytsupport))
  rw [hy hymem, hyshift hyshiftmem]

/-- The cutoff-gradient quotient has the totalized `L²` application bound. -/
theorem norm_cutoffGradientSpatialDifferenceQuotientL2_apply_le
       :
    ‖cutoffGradientSpatialDifferenceQuotientL2 hΩ η j k h f‖ ≤
      (2 * K / |h|) * ‖f‖ := by
  let sharedTerm_2575f76162 := ((measurePreserving_add_right (volume : Measure (PDE.Vec d)) (h • PDE.basisVec k)))
  let sharedTerm_046808c315 := ((fun y : PDE.Vec d => y + h • PDE.basisVec k))
  let sharedTerm_b3743d7017 := ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω))
  by_cases hh : h = 0
  · subst h
    simp [cutoffGradientSpatialDifferenceQuotientL2]
  unfold cutoffGradientSpatialDifferenceQuotientL2
  dsimp only
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, LinearIsometry.coe_toContinuousLinearMap]
  have hM := norm_scalarL2Multiplier_apply_le
    (fun y => PDE.classicalGradient η.toFun y j)
    (cutoffGradient_aestronglyMeasurable η j) K η.gradient_bound_nonneg
    (cutoffGradient_norm_le η j)
    (sharedTerm_b3743d7017
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        sharedTerm_046808c315
        sharedTerm_2575f76162) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))


  rw [norm_smul, norm_inv, Real.norm_eq_abs]

  have hR' := (show ‖sharedTerm_b3743d7017
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        sharedTerm_046808c315
        sharedTerm_2575f76162) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ ≤
      ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        sharedTerm_046808c315
        sharedTerm_2575f76162) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ by
      exact norm_Lp_toLp_restrict_le Ω _).trans (by
      calc
        _ ≤ ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
            sharedTerm_046808c315
            sharedTerm_2575f76162) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ +
            ‖(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ := norm_sub_le _ _
        _ = 2 * ‖f‖ := by
          rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
          ring)

  calc
    _ ≤ |h|⁻¹ * (K * ‖sharedTerm_b3743d7017
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          sharedTerm_046808c315
          sharedTerm_2575f76162) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖) :=
      mul_le_mul_of_nonneg_left (hM) (inv_nonneg.mpr (abs_nonneg h))
    _ ≤ |h|⁻¹ * (K * (2 * ‖f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR' η.gradient_bound_nonneg) (inv_nonneg.mpr (abs_nonneg h))
    _ = (2 * K / |h|) * ‖f‖ := by
      rw [div_eq_mul_inv]
      ring

end HypoellipticAleksandrov.Parabolic.Dirichlet
