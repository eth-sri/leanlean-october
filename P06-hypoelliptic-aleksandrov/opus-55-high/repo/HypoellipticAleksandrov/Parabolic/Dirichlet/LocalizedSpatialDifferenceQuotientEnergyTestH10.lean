module

public import Mathlib.Analysis.Normed.Operator.Extend
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientPointwise
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothH10DenseRange
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientEnergyWeakTest
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientSmoothCore

/-!
# Localized spatial difference-quotient energy-test operator on `H¹₀`

This module constructs the bounded extension of the literal localized
backward energy test and proves its canonical value-space pivot.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The quotient-safe unweighted restricted scalar `L²` difference quotient. -/
private def unweightedSpatialDifferenceQuotientL2
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : MeasurableSet Ω) (k : Fin d) (s : ℝ) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  let μ : Measure (PDE.Vec d) := volume
  let z : PDE.Vec d := s • PDE.basisVec k
  let T : PDE.Vec d → PDE.Vec d := fun y => y + z
  let hT : MeasurePreserving T μ μ := measurePreserving_add_right μ z
  let E : PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ] Lp ℝ (2 : ℝ≥0∞) μ :=
    (Lp.zeroExtendLinearIsometry (μ := μ) hΩ).toContinuousLinearMap
  let P : Lp ℝ (2 : ℝ≥0∞) μ →L[ℝ] Lp ℝ (2 : ℝ≥0∞) μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap
  let R : Lp ℝ (2 : ℝ≥0∞) μ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ μ (2 : ℝ≥0∞) Ω
  s⁻¹ • R.comp (P.comp E - E)

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : MeasurableSet Ω) (k : Fin d) (s : ℝ) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞))

/-- The outer quotient has its canonical ambient zero-extension formula. -/
private theorem unweightedSpatialDifferenceQuotientL2_apply_ae
     :
    ⇑(unweightedSpatialDifferenceQuotientL2 hΩ k s f) =ᵐ[PDE.volumeOn Ω]
      fun y =>
        (⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)
            (y + s • PDE.basisVec k) -
          ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y) / s := by
  unfold unweightedSpatialDifferenceQuotientL2
  have hP :
      ⇑((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        _
        (measurePreserving_add_right volume
          (s • PDE.basisVec k)))
        ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)) =ᵐ[volume]
        (⇑((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) ∘
          fun y : PDE.Vec d => y + s • PDE.basisVec k) := MeasureTheory.Lp.coeFn_compMeasurePreserving
      _
      _
  have hR := LpToLpRestrictCLM_coeFn ℝ Ω
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      _
      (measurePreserving_add_right volume
        (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
      (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
  have hsub := MeasureTheory.Lp.coeFn_sub
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      _
      (measurePreserving_add_right volume
        (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
    ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
  have hsmul := MeasureTheory.Lp.coeFn_smul s⁻¹
    ((LpToLpRestrictCLM _ ℝ ℝ volume 2 Ω)
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        _
        (measurePreserving_add_right volume
          (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
  filter_upwards [hsmul, hR, hsub.restrict, hP.restrict] with y hsmul hR hsub hP
  simp only [smul_apply, ContinuousLinearMap.comp_apply, sub_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hR, hsub]
  simp only [Pi.sub_apply]
  grind

/-- A representative supported in the raw domain may replace the canonical
zero extension in the unweighted quotient, with no collar premise. -/
private theorem unweightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
     (g : PDE.Vec d → ℝ)
    (hfg : ⇑f =ᵐ[PDE.volumeOn Ω] g)
    (hgsupp : Function.support g ⊆ Ω) :
    ⇑(unweightedSpatialDifferenceQuotientL2 hΩ k s f) =ᵐ[PDE.volumeOn Ω]
      fun y => (g (y + s • PDE.basisVec k) - g y) / s := by
  have hzero := MeasureTheory.Lp.coeFn_zeroExtendLinearIsometry hΩ f
  have hfg' := ae_imp_of_ae_restrict hfg
  have hambient : ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) =ᵐ[volume] g := by
    filter_upwards [hzero, hfg'] with y hzero hfg
    by_cases hy : y ∈ Ω
    · simp_all
    · have hgzero : g y = 0 := by
        by_contra hgne
        simp_all
      simp_all
  have hshifted := (measurePreserving_add_right volume
    (s • PDE.basisVec k)).quasiMeasurePreserving.ae hambient
  have hambientOn : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω,
      ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y = g y :=
    (ae_restrict_iff' hΩ).mpr (hambient.mono fun _ hy _ => hy)
  have hshiftedOn : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω,
      ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)
        _ = g _ :=
    (ae_restrict_iff' hΩ).mpr (hshifted.mono fun _ hy _ => hy)
  filter_upwards [unweightedSpatialDifferenceQuotientL2_apply_ae hΩ k s f,
    hambientOn, hshiftedOn] with y hq hambient hshifted
  simp_all



/-- The unweighted outer quotient has the totalized scalar `L²` bound. -/
private theorem norm_unweightedSpatialDifferenceQuotientL2_apply_le
     :
    ‖unweightedSpatialDifferenceQuotientL2 hΩ k s f‖ ≤ (2 / |s|) * ‖f‖ := by
  by_cases hs : s = 0
  · subst s
    simp [unweightedSpatialDifferenceQuotientL2]
  unfold unweightedSpatialDifferenceQuotientL2
  have hR : ‖(LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        (fun y : PDE.Vec d => y + s • PDE.basisVec k)
        (measurePreserving_add_right (volume : Measure (PDE.Vec d))
          (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ ≤
      ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        (fun y : PDE.Vec d => y + s • PDE.basisVec k)
        (measurePreserving_add_right (volume : Measure (PDE.Vec d))
          (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ :=
    norm_Lp_toLp_restrict_le Ω _
  have hD : ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      (fun y : PDE.Vec d => y + s • PDE.basisVec k)
      (measurePreserving_add_right (volume : Measure (PDE.Vec d))
        (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
      (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ ≤ 2 * ‖f‖ := by
    calc
      _ ≤ ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          _
          _) _‖ +
          ‖(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ := norm_sub_le _ _
      _ = 2 * ‖f‖ := by
        rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
        ring
  simp only [smul_apply, ContinuousLinearMap.comp_apply, sub_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [norm_smul, norm_inv, Real.norm_eq_abs]
  calc
    _ ≤ |s|⁻¹ * ‖(LpToLpRestrictCLM _ ℝ ℝ volume 2 Ω)
        _‖ := by rfl
    _ ≤ |s|⁻¹ * (2 * ‖f‖) :=
      mul_le_mul_of_nonneg_left (hR.trans hD) (inv_nonneg.mpr (abs_nonneg s))
    _ = (2 / |s|) * ‖f‖ := by
      ring

/-- The literal smooth B core is linear before any completion argument. -/
def energyTestSmoothCoreLinearMap
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    PDE.WeakTestFunction Ω →ₗ[ℝ] H10HilbertGraph hΩ where
  toFun φ := smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ
    (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift)
  map_add' φ ψ := by
    rw [← map_add]
    congr 1
    apply PDE.WeakTestFunction.ext
    funext y
    simpa only [localizedSpatialDifferenceQuotientEnergyWeakTest,
      PDE.WeakTestFunction.add_toFun, Pi.add_def] using
      congrFun (localizedSpatialDifferenceQuotientEnergyTest_add η k h
        _ _) y
  map_smul' c φ := by
    rw [← map_smul]
    congr 1
    apply PDE.WeakTestFunction.ext
    funext y
    simpa only [localizedSpatialDifferenceQuotientEnergyWeakTest, PDE.WeakTestFunction.smul_toFun,
      Pi.smul_def, smul_eq_mul, RingHom.id_apply] using
      congrFun (localizedSpatialDifferenceQuotientEnergyTest_smul c η k h
        _) y

/-- The quotient-safe scalar receiver dictated by the literal B test. -/
private def energyTestValueReceiver
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) :
    H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  (-1 : ℝ) • (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)).comp
    ((localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
      (valueCLM hΩ))

/-- Each B gradient coordinate has the forced outer-quotient receiver. -/
private def energyTestGradientReceiver
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (j k : Fin d) (h : ℝ) :
    H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  (-1 : ℝ) • (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)).comp
    ((cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq j k h).comp
        (valueCLM hΩ) +
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
        ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).comp (gradientCLM hΩ)))

private def energyTestGradientVectorReceiver
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) :
    H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
  PDE.hilbertVectorLpAssemble fun j => energyTestGradientReceiver hΩ η j k h

private theorem energyTestSmoothCore_value_eq_receiver
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    valueCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ) =
      energyTestValueReceiver hΩ η k h
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  have hcore : energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) := by
    apply Subtype.ext
    rfl
  have hinput : smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
    apply Subtype.ext
    rfl
  rw [hcore, hinput]
  change valueCLM hΩ
      _ =
    (-1 : ℝ) • unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k _
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
        (valueCLM hΩ
          _))
  apply MeasureTheory.Lp.ext
  have hleft := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift)
  have hinputAE := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ
  have hsqshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      _ Ω := fun y hy => hηshift (sq_tsupport_subset η hy)
  have hA := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η.sq k h
    _
    φ hinputAE hsqshift
  have hAsupp : Function.support (localizedSpatialDifferenceQuotient η.sq k h φ) ⊆ Ω := by
    intro y hy
    exact hηΩ (sq_tsupport_subset η
      (tsupport_localizedSpatialDifferenceQuotient_subset η.sq k h φ
        (subset_tsupport _ hy)))
  have houter := unweightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet k (-h)
    _
    _ hA hAsupp
  have hsmul := MeasureTheory.Lp.coeFn_smul (-1 : ℝ)
    (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))))
  filter_upwards [hleft, houter, hsmul] with y hleft houter hsmul
  rw [hleft, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [houter]
  change localizedSpatialDifferenceQuotientEnergyTest η k h φ y = _
  simp only [
    localizedSpatialDifferenceQuotientEnergyTest_apply,
    localizedSpatialDifferenceQuotient_apply,
    PDE.QuantitativeSmoothCutoff.sq_toFun, pow_two]
  rw [sub_eq_add_neg, neg_smul]
  ring

private theorem energyTestSmoothCore_gradientCoord_eq_receiver
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (j k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
      (gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ)) =
      energyTestGradientReceiver hΩ η j k h
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  let ψ := localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
    ((sq_tsupport_subset η).trans hηΩ)
  let F  :=
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq j k h
        (valueCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)) +
      localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
        (PDE.hilbertVectorLpCoord Ω _ j
          (gradientCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)))
  have hcore : energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) := by
    apply Subtype.ext
    rfl
  have hinput : smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
    apply Subtype.ext
    rfl
  have hsqshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      _ Ω := fun y hy => hηshift (sq_tsupport_subset η hy)
  have hcoord : PDE.hilbertVectorLpCoord Ω _ j
      (gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)) = F := localizedSpatialDifferenceQuotientWeakTest_gradientCoord_eq
      hΩ η.sq k h φ _ hsqshift j
  rw [hcore, hinput]
  change PDE.hilbertVectorLpCoord Ω _ j
      _ =
    (-1 : ℝ) • unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k _ F
  apply MeasureTheory.Lp.ext
  have hleftCoord := PDE.coeFn_hilbertVectorLpCoord Ω _ j
    (gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift)))
  have hleftJet := ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) j
  have hinnerAE : ⇑F =ᵐ[PDE.volumeOn Ω] fun y => ψ.partialDeriv j y := by
    rw [← hcoord]
    exact (PDE.coeFn_hilbertVectorLpCoord Ω _ j
      _).trans
      (ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ j)
  have hψsupport : Function.support (fun y => ψ.partialDeriv j y) ⊆ Ω := by
    intro y hy
    apply ψ.tsupport_subset
    by_contra hynot
    apply hy
    change (fderiv ℝ ψ.toFun y) _ = 0
    rw [fderiv_of_notMem_tsupport ℝ hynot]
    exact ContinuousLinearMap.zero_apply _
  have houter := unweightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet k (-h) F _ hinnerAE hψsupport
  have hsmul := MeasureTheory.Lp.coeFn_smul (-1 : ℝ)
    (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h) F)
  filter_upwards [hleftCoord, hleftJet, houter, hsmul] with y hleftCoord hleftJet houter hsmul
  rw [hleftCoord, hleftJet, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [houter]
  have hraw := energyWeakTest_partialDeriv_eq_backwardSquare
    η k h φ hηΩ hηshift j y
  rw [hraw]
  ring

private theorem energyTestSmoothCore_gradient_eq_receiver
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ) =
      energyTestGradientVectorReceiver hΩ η k h
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  let L  := fun j =>
    energyTestGradientReceiver hΩ η j k h
  have hcoord (j : Fin d) :
      PDE.hilbertVectorLpCoord Ω _ j
        (gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ)) =
      L j (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := energyTestSmoothCore_gradientCoord_eq_receiver
      hΩ η j k h φ hηΩ hηshift
  change gradientCLM hΩ _ =
    PDE.hilbertVectorLpAssemble L
      _
  apply MeasureTheory.Lp.ext
  have hcoords : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω, ∀ j : Fin d,
      gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ) y j =
        L j (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) y := by
    apply ae_all_iff.mpr
    intro j
    have hleft := PDE.coeFn_hilbertVectorLpCoord Ω _ j
      (gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ))
    filter_upwards [hleft] with y hleft
    exact hleft.symm.trans (congrArg (fun z : PDE.ScalarLp Ω _ => z y)
      (hcoord j))
  have hassemble := PDE.hilbertVectorLpAssemble_apply_ae L
    (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)
  filter_upwards [hcoords, hassemble] with y hcoords hassemble
  aesop

private theorem norm_energyTestValueReceiver_apply_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (u : H10HilbertGraph hΩ) :
    ‖energyTestValueReceiver hΩ η k h u‖ ≤ (4 / |h| ^ 2) * ‖u‖ := by
  have hvalue : ‖valueCLM hΩ u‖ ≤ ‖u‖ := by
    let z  := (u : PDE.H1HilbertGraph Ω).1
    exact WithLp.norm_fst_le _ z
  change ‖(-1 : ℝ) • unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k _
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
        (valueCLM hΩ u))‖ ≤ _
  calc
    _ = ‖unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k _
        _‖ := by simp
    _ ≤ (2 / |-h|) * ‖localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
        (valueCLM hΩ u)‖ := norm_unweightedSpatialDifferenceQuotientL2_apply_le _ _ _ _
    _ ≤ (2 / |h|) * ((2 / |h|) * ‖valueCLM hΩ u‖) := by
      rw [abs_neg]
      exact mul_le_mul_of_nonneg_left
        (norm_localizedSpatialDifferenceQuotientL2_apply_le
          hΩ.measurableSet η.sq k h _)
        (div_nonneg (by norm_num) (abs_nonneg h))
    _ ≤ (2 / |h|) * ((2 / |h|) * ‖u‖) := by
      gcongr
    _ = (4 / |h| ^ 2) * ‖u‖ := by ring

private theorem norm_energyTestGradientReceiver_apply_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (j k : Fin d) (h : ℝ) (u : H10HilbertGraph hΩ) :
    ‖energyTestGradientReceiver hΩ η j k h u‖ ≤
      (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by
  have hvalue : ‖valueCLM hΩ u‖ ≤ ‖u‖ := by
    let z  := (u : PDE.H1HilbertGraph Ω).1
    exact WithLp.norm_fst_le _ z
  have hgradient : ‖gradientCLM hΩ u‖ ≤ ‖u‖ := by
    let z  := (u : PDE.H1HilbertGraph Ω).1
    exact WithLp.norm_snd_le _ z
  have hfirst : ‖(cutoffGradientSpatialDifferenceQuotientL2
      hΩ.measurableSet η.sq j k h).comp (valueCLM hΩ) u‖ ≤
      (4 * K / |h|) * ‖valueCLM hΩ u‖ := by
    calc
      _ ≤ (2 * (2 * K) / |h|) * ‖valueCLM hΩ u‖ :=
        norm_cutoffGradientSpatialDifferenceQuotientL2_apply_le
          hΩ.measurableSet η.sq j k h _
      _ = (4 * K / |h|) * ‖valueCLM hΩ u‖ := by ring
  have hsecond : ‖(localizedSpatialDifferenceQuotientL2
      hΩ.measurableSet η.sq k h).comp
      ((PDE.hilbertVectorLpCoord Ω _ j).comp (gradientCLM hΩ)) u‖ ≤
      (2 / |h|) * ‖PDE.hilbertVectorLpCoord Ω _ j
        (gradientCLM hΩ u)‖ := norm_localizedSpatialDifferenceQuotientL2_apply_le
      hΩ.measurableSet η.sq k h
        _
  change ‖(-1 : ℝ) • unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k _
      ((cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq j k h).comp
          (valueCLM hΩ) u +
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
          ((PDE.hilbertVectorLpCoord Ω _ j).comp (gradientCLM hΩ)) u)‖ ≤ _
  calc
    _ = ‖unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k _
        _‖ := by
      simp only [neg_one_smul]
      exact norm_neg _
    _ ≤ (2 / |-h|) * ‖(cutoffGradientSpatialDifferenceQuotientL2
        hΩ.measurableSet η.sq j k h).comp _ u +
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
          _ u‖ :=
      norm_unweightedSpatialDifferenceQuotientL2_apply_le _ _ _ _
    _ ≤ (2 / |h|) * ((4 * K / |h|) * ‖valueCLM hΩ u‖ +
        (2 / |h|) * ‖PDE.hilbertVectorLpCoord Ω _ j
          _‖) := by
      rw [abs_neg]
      apply mul_le_mul_of_nonneg_left
      · exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
      · exact div_nonneg (by norm_num) (abs_nonneg h)
    _ ≤ (2 / |h|) * ((4 * K / |h|) * ‖u‖ + (2 / |h|) * ‖u‖) := by
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add
        · apply mul_le_mul_of_nonneg_left hvalue
          exact div_nonneg (mul_nonneg (by norm_num) η.gradient_bound_nonneg) (abs_nonneg h)
        · apply mul_le_mul_of_nonneg_left
            ((norm_hilbertVectorLpCoord_le j _).trans hgradient)
          exact div_nonneg (by norm_num) (abs_nonneg h)
      positivity
    _ = (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by ring

private theorem norm_energyTestGradientVectorReceiver_apply_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (u : H10HilbertGraph hΩ) :
    ‖energyTestGradientVectorReceiver hΩ η k h u‖ ≤
      (d : ℝ) * (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by
  let L  := fun j =>
    energyTestGradientReceiver hΩ η j k h
  calc
    _ ≤ ∑ j, ‖L j u‖ := PDE.norm_hilbertVectorLpAssemble_apply_le L u
    _ ≤ ∑ _ : Fin d, (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact norm_energyTestGradientReceiver_apply_le hΩ η j k h u
    _ = d * (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring


private theorem norm_energyTestSmoothCoreLinearMap_apply_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ‖energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ‖ ≤
      (4 * (1 + (d : ℝ) * (2 * K + 1)) / |h| ^ 2) *
        ‖smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ‖ := by
  let x  := smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ
  let q  := energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ
  have hvalue : valueCLM hΩ q = energyTestValueReceiver hΩ η k h x := by
    simpa using energyTestSmoothCore_value_eq_receiver
      hΩ η k h φ hηΩ hηshift
  have hgradient : gradientCLM hΩ q = energyTestGradientVectorReceiver hΩ η k h x := by
    simpa using energyTestSmoothCore_gradient_eq_receiver
      hΩ η k h φ hηΩ hηshift
  calc
    ‖energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ‖ = ‖q‖ := rfl
    _ ≤ ‖valueCLM hΩ q‖ + ‖gradientCLM hΩ q‖ :=
      norm_h10HilbertGraph_le_value_add_gradient hΩ q
    _ = ‖energyTestValueReceiver hΩ η k h x‖ +
        ‖energyTestGradientVectorReceiver hΩ η k h x‖ := by simp_all
    _ ≤ (4 / |h| ^ 2) * ‖x‖ +
        (d * (4 * (2 * K + 1) / |h| ^ 2)) * ‖x‖ :=
      add_le_add (norm_energyTestValueReceiver_apply_le hΩ η k h x)
        (norm_energyTestGradientVectorReceiver_apply_le hΩ η k h x)
    _ = (4 * (1 + d * (2 * K + 1)) / |h| ^ 2) * ‖x‖ := by ring

private theorem exists_energyTestSmoothCoreLinearMap_bound
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ∃ C : ℝ, ∀ φ : PDE.WeakTestFunction Ω,
      ‖energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ‖ ≤ C *
        ‖smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ‖ := by
  refine ⟨4 * (1 + d * (2 * K + 1)) / |h| ^ 2, ?_⟩
  intro φ
  exact norm_energyTestSmoothCoreLinearMap_apply_le hΩ η k h φ hηΩ hηshift

/-- The internal bounded extension of the smooth localized energy test. -/
def energyTestH10CLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
  (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift).extendOfNorm
    (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)

private theorem energyTestH10CLM_apply_smooth
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    energyTestH10CLM hΩ η k h hηΩ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ := LinearMap.extendOfNorm_eq
    (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
    (exists_energyTestSmoothCoreLinearMap_bound hΩ η k h hηΩ hηshift) φ

private theorem inner_scalarLp_eq_integral_mul_of_ae_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (F G : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (f g : PDE.Vec d → ℝ)
    (hF : ⇑F =ᵐ[PDE.volumeOn Ω] f) (hG : ⇑G =ᵐ[PDE.volumeOn Ω] g) :
    inner ℝ F G = ∫ y, f y * g y ∂PDE.volumeOn Ω := by
  apply integral_congr_ae
  filter_upwards [hF, hG] with y hF hG
  rw [hF, hG]
  simp [mul_comm]

private theorem inner_value_energyTestSmoothCore_eq
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ ψ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    Inner.inner ℝ
      (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
      (valueCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift ψ)) =
      Inner.inner ℝ
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ))) := by
  have hφ := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ
  have hψ := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    (localizedSpatialDifferenceQuotientEnergyWeakTest η k h ψ ψ.contDiff hηΩ hηshift)
  have hAφ := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η k h
    _
    φ hφ hηshift
  have hAψbase := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ
  have hAψ := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η k h
    _
    ψ hAψbase hηshift
  calc
    _ = ∫ y, φ y * localizedSpatialDifferenceQuotientEnergyTest η k h ψ y
        ∂PDE.volumeOn Ω := by
      apply inner_scalarLp_eq_integral_mul_of_ae_eq
        _
        _
        φ _ hφ
      exact hψ
    _ = ∫ y, localizedSpatialDifferenceQuotient η k h φ y *
        localizedSpatialDifferenceQuotient η k h ψ y ∂PDE.volumeOn Ω := by
      rw [setIntegral_mul_localizedSpatialDifferenceQuotientEnergyTest_eq
        η k h φ ψ φ.contDiff.continuous ψ.contDiff.continuous hηΩ hηshift]
    _ = _ := (inner_scalarLp_eq_integral_mul_of_ae_eq
      _
      _
      _
      _ hAφ hAψ).symm

private theorem value_localizedSpatialDifferenceQuotientH10CLM_apply_smooth
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    valueCLM hΩ
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) =
      localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) := by
  have h := congrArg (fun M : H10HilbertGraph hΩ →L[ℝ]
      PDE.ScalarLp Ω _ => M
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
    (valueCLM_comp_localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift)
  simp_all

private def energyTestSmoothLeftPairCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    H10HilbertGraph hΩ →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ
    (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))).comp
      ((valueCLM hΩ).comp (energyTestH10CLM hΩ η k h hηΩ hηshift))

private def localizedSmoothLeftPairCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    H10HilbertGraph hΩ →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ
    (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))).comp
      ((valueCLM hΩ).comp (localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h hηΩ hηshift))

variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d)

private theorem energyTestSmoothLeftPairCLM_apply
     (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (v : H10HilbertGraph hΩ) :
    energyTestSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift v =
      Inner.inner ℝ
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
        (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v)) := by
  rfl

private theorem localizedSmoothLeftPairCLM_apply_smooth
     (h : ℝ) (φ ψ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    localizedSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ) =
      Inner.inner ℝ
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ))) := by
  calc
    _ = Inner.inner ℝ
        _
        _ := congrArg (fun z => Inner.inner ℝ z
        _)
        (value_localizedSpatialDifferenceQuotientH10CLM_apply_smooth
          hΩ η k h φ hηΩ hηshift)
    _ = _ := congrArg _
        (value_localizedSpatialDifferenceQuotientH10CLM_apply_smooth
          hΩ η k h ψ hηΩ hηshift)

private theorem energyTestSmoothLeftPairCLM_eq_localizedSmoothLeftPairCLM
     (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    energyTestSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift =
      localizedSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift := by
  apply ContinuousLinearMap.ext
  exact fun w => congrFun
    ((denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).equalizer
      (energyTestSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift).continuous
      (localizedSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift).continuous (by
      funext ψ
      change energyTestSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift
          _ =
        localizedSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift
          _
      rw [energyTestSmoothLeftPairCLM_apply, energyTestH10CLM_apply_smooth]
      rw [localizedSmoothLeftPairCLM_apply_smooth]
      exact inner_value_energyTestSmoothCore_eq hΩ η k h φ ψ hηΩ hηshift)) w

private theorem inner_value_energyTestH10CLM_eq_of_smooth_left
     (h : ℝ) (φ : PDE.WeakTestFunction Ω) (v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    Inner.inner ℝ (valueCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
      (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v)) =
      Inner.inner ℝ (valueCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))
        (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v)) := congrArg (fun M : H10HilbertGraph hΩ →L[ℝ] ℝ => M v)
    (energyTestSmoothLeftPairCLM_eq_localizedSmoothLeftPairCLM
      hΩ η k h φ hηΩ hηshift)

private def energyTestFixedRightPairCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) : H10HilbertGraph hΩ →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v))).comp
    (valueCLM hΩ)

private def localizedFixedRightPairCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) : H10HilbertGraph hΩ →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ
    (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v))).comp
      ((valueCLM hΩ).comp (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift))

variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d)

private theorem energyTestFixedRightPairCLM_eq_localizedFixedRightPairCLM
     (h : ℝ) (v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    energyTestFixedRightPairCLM hΩ η k h v hηΩ hηshift =
      localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift := by
  apply ContinuousLinearMap.ext
  exact fun u => congrFun
    ((denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).equalizer
      (energyTestFixedRightPairCLM hΩ η k h v hηΩ hηshift).continuous
      (localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift).continuous (by
      funext φ
      calc
        _ = Inner.inner ℝ
            _
            _ :=
          real_inner_comm _ _
        _ = Inner.inner ℝ _
            _ :=
          inner_value_energyTestH10CLM_eq_of_smooth_left hΩ η k h φ v hηΩ hηshift
        _ = _ := real_inner_comm _ _)) u

private theorem inner_value_energyTestH10CLM_eq
     (h : ℝ) (u v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    Inner.inner ℝ (valueCLM hΩ u)
      (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v)) =
    Inner.inner ℝ
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u))
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v)) := by
  calc
    _ = Inner.inner ℝ _
        _ := real_inner_comm _ _
    _ = Inner.inner ℝ _
        _ :=
      congrArg (fun M : H10HilbertGraph hΩ →L[ℝ] ℝ => M u)
        (energyTestFixedRightPairCLM_eq_localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift)
    _ = _ := real_inner_comm _ _

/-- The bounded H10 extension of the localized spatial energy test. -/
def localizedSpatialDifferenceQuotientEnergyTestH10CLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
  energyTestH10CLM hΩ η k h hηΩ hηshift

variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d)

/-- The energy-test extension agrees with the literal bundled smooth core. -/
theorem localizedSpatialDifferenceQuotientEnergyTestH10CLM_apply_smooth
     (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) := by
  change energyTestH10CLM hΩ η k h hηΩ hηshift
      _ = _
  rw [energyTestH10CLM_apply_smooth]
  rfl

/-- The energy-test value pairing is the localized quotient inner product. -/
theorem inner_value_localizedSpatialDifferenceQuotientEnergyTestH10CLM_eq
     (h : ℝ) (u v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    Inner.inner ℝ (valueCLM hΩ u)
      (valueCLM hΩ
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h hηΩ hηshift v)) =
    Inner.inner ℝ
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u))
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v)) := inner_value_energyTestH10CLM_eq hΩ η k h u v hηΩ hηshift

end HypoellipticAleksandrov.Parabolic.Dirichlet
