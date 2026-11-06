module

public import HypoellipticAleksandrov.Measure.LpZeroExtension
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Multiplier
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientPointwise

/-!
# Localized spatial difference quotients on restricted `L²`

This module constructs the representative-independent cutoff-weighted forward
spatial difference quotient using ambient zero extension, translation,
restriction, and multiplication on quotient `L²` spaces.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A smooth cutoff is almost everywhere strongly measurable on restricted volume. -/
theorem cutoff_aestronglyMeasurable
    {d : ℕ} {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) :
    AEStronglyMeasurable η.toFun (PDE.volumeOn Ω) :=
  η.smooth.continuous.aestronglyMeasurable

variable {d : ℕ} {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}

/-- A quantitative smooth cutoff has norm at most one almost everywhere. -/
theorem cutoff_norm_le_one

    (η : PDE.QuantitativeSmoothCutoff inner outer K) :
    ∀ᵐ y ∂PDE.volumeOn Ω, ‖η.toFun y‖ ≤ (1 : ℝ) :=
  ae_of_all _ fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
    exact η.le_one y

variable (hΩ : MeasurableSet Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)

/-- The representative-independent cutoff-weighted forward spatial difference
quotient on restricted-volume scalar `L²`. -/
def localizedSpatialDifferenceQuotientL2

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
    scalarL2Multiplier η.toFun (cutoff_aestronglyMeasurable η) 1 zero_le_one
      (cutoff_norm_le_one η)
  h⁻¹ • M.comp (R.comp (P.comp E - E))

variable (f : PDE.ScalarLp Ω (2 ))

/-- The restricted-space quotient agrees almost everywhere with the canonical
zero-extension representative formula. -/
theorem localizedSpatialDifferenceQuotientL2_apply_ae

      :
    ⇑(localizedSpatialDifferenceQuotientL2 hΩ η k h f) =ᵐ[PDE.volumeOn Ω]
      fun y => localizedSpatialDifferenceQuotient η k h
        (⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)) y := by
  let sharedTerm_dc607f5186 := ((measurePreserving_add_right (volume : Measure (PDE.Vec d)) (h • PDE.basisVec k)))
  let sharedTerm_2d2cc0e8e6 := ((fun y : PDE.Vec d => y + h • PDE.basisVec k))
  let sharedTerm_c81010c3fe := ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω))
  unfold localizedSpatialDifferenceQuotientL2
  dsimp
  have hP :
      ⇑((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        sharedTerm_2d2cc0e8e6
        sharedTerm_dc607f5186)
        ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)) =ᵐ[volume]
        (⇑((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) ∘
          sharedTerm_2d2cc0e8e6) := by
    change MeasureTheory.Lp.compMeasurePreserving
      sharedTerm_2d2cc0e8e6
      sharedTerm_dc607f5186 ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) =ᵐ[volume]
        (⇑((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) ∘
          sharedTerm_2d2cc0e8e6)
    exact MeasureTheory.Lp.coeFn_compMeasurePreserving
      _
      sharedTerm_dc607f5186
  have hR := LpToLpRestrictCLM_coeFn ℝ Ω
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      sharedTerm_2d2cc0e8e6
      sharedTerm_dc607f5186) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
      (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
  have hM := scalarL2Multiplier_apply_ae η.toFun
    (cutoff_aestronglyMeasurable η) 1 zero_le_one
    (cutoff_norm_le_one η)
    (sharedTerm_c81010c3fe
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        sharedTerm_2d2cc0e8e6
        sharedTerm_dc607f5186) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
  have hsub := MeasureTheory.Lp.coeFn_sub
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      sharedTerm_2d2cc0e8e6
      sharedTerm_dc607f5186) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
    ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
  have hsmul := MeasureTheory.Lp.coeFn_smul h⁻¹
    ((scalarL2Multiplier η.toFun (cutoff_aestronglyMeasurable η) 1 zero_le_one
      (cutoff_norm_le_one η)
      (sharedTerm_c81010c3fe
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          sharedTerm_2d2cc0e8e6
          sharedTerm_dc607f5186) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))))
  filter_upwards [hsmul, hM, hR, hsub.restrict, hP.restrict] with y hsmul hM hR hsub hP
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    sub_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hM, hR, hsub]
  simp only [Pi.sub_apply]
  rw [hP]
  simp only [Function.comp_apply, div_eq_mul_inv]
  ring

/-- A supplied restricted-space representative may replace the canonical zero
extension on the cutoff's forward active collar. -/
theorem localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq


    (g : PDE.ScalarField d)
    (hfg : ⇑f =ᵐ[PDE.volumeOn Ω] g)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ⇑(localizedSpatialDifferenceQuotientL2 hΩ η k h f) =ᵐ[PDE.volumeOn Ω]
      localizedSpatialDifferenceQuotient η k h g := by
  have hzero := MeasureTheory.Lp.coeFn_zeroExtendLinearIsometry hΩ f

  have hambient : ∀ᵐ y : PDE.Vec d,
      y ∈ Ω → ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y = g y := by
    filter_upwards [hzero, (ae_imp_of_ae_restrict hfg)] with y hzero hfg hy
    rw [hzero, Set.indicator_of_mem hy]
    exact hfg hy
  have hshifted := (measurePreserving_add_right (volume : Measure (PDE.Vec d))
    (h • PDE.basisVec k)).quasiMeasurePreserving.ae hambient



  filter_upwards [localizedSpatialDifferenceQuotientL2_apply_ae hΩ η k h f,
    ((ae_restrict_iff' hΩ).mpr (hambient.mono fun _ hy _ => hy)), ((ae_restrict_iff' hΩ).mpr (hshifted.mono fun _ hy _ => hy)), ((ae_restrict_iff' hΩ).mpr (ae_of_all _ fun y hy => hy))] with y hq hy hyshift hymem
  rw [hq, localizedSpatialDifferenceQuotient_apply]
  by_cases hη : η.toFun y = 0
  · simp [hη]


  rw [hy hymem, hyshift (hηshift (subset_tsupport η.toFun hη))]
  rfl

/-- The localized quotient has the sharp totalized `L²` application bound. -/
theorem norm_localizedSpatialDifferenceQuotientL2_apply_le

      :
    ‖localizedSpatialDifferenceQuotientL2 hΩ η k h f‖ ≤
      (2 / |h|) * ‖f‖ := by
  let sharedTerm_8b28d64384 := ((measurePreserving_add_right (volume : Measure (PDE.Vec d)) (h • PDE.basisVec k)))
  let sharedTerm_bb20140e2e := ((fun y : PDE.Vec d => y + h • PDE.basisVec k))
  let sharedTerm_cf8f31a10c := ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω))
  by_cases hh : h = 0
  · subst h
    simp [localizedSpatialDifferenceQuotientL2]
  unfold localizedSpatialDifferenceQuotientL2
  dsimp
  have hM := norm_scalarL2Multiplier_apply_le η.toFun
    (cutoff_aestronglyMeasurable η) 1 zero_le_one (cutoff_norm_le_one η)
    (sharedTerm_cf8f31a10c
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        sharedTerm_bb20140e2e
        sharedTerm_8b28d64384) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))


  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    sub_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [norm_smul, norm_inv, Real.norm_eq_abs]

  have hR' := (show ‖sharedTerm_cf8f31a10c
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        sharedTerm_bb20140e2e
        sharedTerm_8b28d64384) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ ≤
      ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        sharedTerm_bb20140e2e
        sharedTerm_8b28d64384) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ by
      exact norm_Lp_toLp_restrict_le Ω _).trans (by
      calc
        _ ≤ ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
            sharedTerm_bb20140e2e
            sharedTerm_8b28d64384) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ +
            ‖(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ := norm_sub_le _ _
        _ = 2 * ‖f‖ := by
          rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
          ring)
  calc
    _ ≤ |h|⁻¹ * ‖sharedTerm_cf8f31a10c
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          sharedTerm_bb20140e2e
          sharedTerm_8b28d64384) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ :=
      mul_le_mul_of_nonneg_left (by
          simpa using hM) (inv_nonneg.mpr (abs_nonneg h))
    _ ≤ |h|⁻¹ * (2 * ‖f‖) :=
      mul_le_mul_of_nonneg_left hR' (inv_nonneg.mpr (abs_nonneg h))
    _ = (2 / |h|) * ‖f‖ := by
      rw [div_eq_mul_inv]
      ring

end HypoellipticAleksandrov.Parabolic.Dirichlet
