module

public import Mathlib.Analysis.Normed.Operator.Extend
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientPointwise
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothH10DenseRange
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientSmoothCore
import all HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds

open private HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
open private HypoellipticAleksandrov.Parabolic.Dirichlet.norm_h10HilbertGraph_le_value_add_gradient from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientSmoothCore


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

variable {d : ℕ}

section
variable {Ω : PDE.VelocityRegion d} (hΩ : MeasurableSet Ω) (k : Fin d) (s : ℝ)

/-- The quotient-safe unweighted restricted scalar `L²` difference quotient. -/
private def unweightedSpatialDifferenceQuotientL2
       :=
  let μ : Measure (PDE.Vec d) := volume
  let z : PDE.Vec d := s • PDE.basisVec k
  let T : PDE.VectorField d := fun y => y + z
  let hT : MeasurePreserving T μ μ := measurePreserving_add_right μ z
  let E : PDE.ScalarLp Ω (2 ) →L[ℝ] Lp ℝ (2 ) μ :=
    (Lp.zeroExtendLinearIsometry (μ := μ) hΩ).toContinuousLinearMap
  let P : Lp ℝ (2 ) μ →L[ℝ] Lp ℝ (2 ) μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap
  let R : Lp ℝ (2 ) μ →L[ℝ] PDE.ScalarLp Ω (2 ) :=
    LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ μ _ Ω
  s⁻¹ • R.comp (P.comp E - E)

variable (f : PDE.ScalarLp Ω (2 ))

/-- The outer quotient has its canonical ambient zero-extension formula. -/
private theorem unweightedSpatialDifferenceQuotientL2_apply_ae

     :
    ⇑(unweightedSpatialDifferenceQuotientL2 hΩ k s f) =ᵐ[PDE.volumeOn Ω]
      fun y =>
        (⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)
            (y + s • PDE.basisVec k) -
          ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y) / s := by
  let sharedTerm_0a2387bca3 := ((measurePreserving_add_right (volume : Measure (PDE.Vec d)) (s • PDE.basisVec k)))
  let sharedTerm_c3c8bb0bc8 := ((fun y : PDE.Vec d => y + s • PDE.basisVec k))
  unfold unweightedSpatialDifferenceQuotientL2
  dsimp
  have hP :
      ⇑((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        sharedTerm_c3c8bb0bc8
        sharedTerm_0a2387bca3)
        ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)) =ᵐ[volume]
        (⇑((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) ∘
          sharedTerm_c3c8bb0bc8) := by
    change MeasureTheory.Lp.compMeasurePreserving
      sharedTerm_c3c8bb0bc8
      sharedTerm_0a2387bca3 ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) =ᵐ[volume]
        (⇑((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) ∘
          sharedTerm_c3c8bb0bc8)
    exact MeasureTheory.Lp.coeFn_compMeasurePreserving
      _
      sharedTerm_0a2387bca3
  have hR := LpToLpRestrictCLM_coeFn ℝ Ω
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      sharedTerm_c3c8bb0bc8
      sharedTerm_0a2387bca3) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
      (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
  have hsub := MeasureTheory.Lp.coeFn_sub
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      sharedTerm_c3c8bb0bc8
      sharedTerm_0a2387bca3) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
    ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
  have hsmul := MeasureTheory.Lp.coeFn_smul s⁻¹
    ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        sharedTerm_c3c8bb0bc8
        sharedTerm_0a2387bca3) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
  filter_upwards [hsmul, hR, hsub.restrict, hP.restrict] with y hsmul hR hsub hP
  simp only [smul_apply, ContinuousLinearMap.comp_apply, sub_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hR, hsub]
  simp only [Pi.sub_apply]
  rw [hP]
  simp only [Function.comp_def, div_eq_mul_inv]
  ring

/-- A representative supported in the raw domain may replace the canonical
zero extension in the unweighted quotient, with no collar premise. -/
private theorem unweightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq

     (g : PDE.ScalarField d)
    (hfg : ⇑f =ᵐ[PDE.volumeOn Ω] g)
    (hgsupp : Function.support g ⊆ Ω) :
    ⇑(unweightedSpatialDifferenceQuotientL2 hΩ k s f) =ᵐ[PDE.volumeOn Ω]
      fun y => (g (y + s • PDE.basisVec k) - g y) / s := by
  have hzero := MeasureTheory.Lp.coeFn_zeroExtendLinearIsometry hΩ f

  have hambient : ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) =ᵐ[volume] g := by
    filter_upwards [hzero, (ae_imp_of_ae_restrict hfg)] with y hzero hfg
    rw [hzero]
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy]
      exact hfg hy
    · rw [Set.indicator_of_notMem hy]

      exact (show g y = 0 by
          by_contra hgne
          exact hy (hgsupp hgne)).symm
  have hshifted := (measurePreserving_add_right (volume : Measure (PDE.Vec d))
    (s • PDE.basisVec k)).quasiMeasurePreserving.ae hambient


  filter_upwards [unweightedSpatialDifferenceQuotientL2_apply_ae hΩ k s f,
    ((ae_restrict_iff' hΩ).mpr (hambient.mono fun _ hy _ => hy)), ((ae_restrict_iff' hΩ).mpr (hshifted.mono fun _ hy _ => hy))] with y hq hambient hshifted
  rw [hq, hambient, hshifted]
end


private theorem sq_tsupport_subset
     {inner outer : PDE.VelocityRegion d} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) :
    tsupport η.sq.toFun ⊆ tsupport η.toFun := by
  simpa only [PDE.QuantitativeSmoothCutoff.sq_toFun, pow_two] using
    (tsupport_mul_subset_left (f := η.toFun) (g := η.toFun))

private theorem energyWeakTest_partialDeriv_eq_backwardSquare
     {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)
    (φ : PDE.WeakTestFunction Ω) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (j : Fin d) (y : PDE.Vec d) :
    PDE.WeakTestFunction.partialDeriv
      (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) j y =
      ((localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
          ((sq_tsupport_subset η).trans hηΩ)).partialDeriv j
          (y + (-h) • PDE.basisVec k) -
        (localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
          ((sq_tsupport_subset η).trans hηΩ)).partialDeriv j y) / h := by
  let ψ := localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
    ((sq_tsupport_subset η).trans hηΩ)
  have hψshift : DifferentiableAt ℝ
      (fun x  => ψ (x + (-h) • PDE.basisVec k)) y :=
    (ψ.contDiff.comp (contDiff_id.add contDiff_const)).contDiffAt.differentiableAt (by simp)
  have hψ : DifferentiableAt ℝ (ψ : PDE.ScalarField d) y :=
    ψ.contDiff.contDiffAt.differentiableAt (by simp)
  let q  := fun x =>
    ψ (x + (-h) • PDE.basisVec k) - ψ x
  have hq : DifferentiableAt ℝ q y := hψshift.sub hψ
  have hrewrite : localizedSpatialDifferenceQuotientEnergyTest η k h φ =
      fun x  => (ψ (x + (-h) • PDE.basisVec k) - ψ x) / h := by
    funext x
    dsimp only [ψ]
    simp only [localizedSpatialDifferenceQuotientEnergyTest_apply,
      localizedSpatialDifferenceQuotient_apply,
      localizedSpatialDifferenceQuotientWeakTest_apply,
      PDE.QuantitativeSmoothCutoff.sq_toFun, pow_two]
    rw [sub_eq_add_neg, neg_smul]
    ring
  unfold PDE.WeakTestFunction.partialDeriv localizedSpatialDifferenceQuotientEnergyWeakTest
  change (fderiv ℝ (localizedSpatialDifferenceQuotientEnergyTest η k h φ) y)
      (PDE.basisVec j) = _
  rw [hrewrite]
  have hquotient : (fun x  =>
      (ψ (x + (-h) • PDE.basisVec k) - ψ x) / h) = fun x => h⁻¹ • q x := by
    funext x
    simp only [q, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hquotient, fderiv_fun_const_smul hq h⁻¹]
  have hqderiv : (fderiv ℝ q y) (PDE.basisVec j) =
      ψ.partialDeriv j (y + (-h) • PDE.basisVec k) - ψ.partialDeriv j y := by
    dsimp only [q]
    rw [fderiv_fun_sub hψshift hψ, fderiv_comp_add_right]
    rfl
  rw [ContinuousLinearMap.smul_apply, hqderiv]
  simp only [PDE.WeakTestFunction.partialDeriv, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The unweighted outer quotient has the totalized scalar `L²` bound. -/
private theorem norm_unweightedSpatialDifferenceQuotientL2_apply_le
     {Ω : PDE.VelocityRegion d}
    (hΩ : MeasurableSet Ω) (k : Fin d) (s : ℝ)
    (f : PDE.ScalarLp Ω (2 )) :
    ‖unweightedSpatialDifferenceQuotientL2 hΩ k s f‖ ≤ (2 / |s|) * ‖f‖ := by
  let sharedTerm_eeda7d8794 := ((measurePreserving_add_right (volume : Measure (PDE.Vec d)) (s • PDE.basisVec k)))
  let sharedTerm_6cc2a14909 := ((fun y : PDE.Vec d => y + s • PDE.basisVec k))
  let sharedTerm_654b0f545c := ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω))
  by_cases hs : s = 0
  · subst s
    simp [unweightedSpatialDifferenceQuotientL2]
  unfold unweightedSpatialDifferenceQuotientL2
  dsimp


  simp only [smul_apply, ContinuousLinearMap.comp_apply, sub_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [norm_smul, norm_inv, Real.norm_eq_abs]
  calc
    _ ≤ |s|⁻¹ * ‖sharedTerm_654b0f545c
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          sharedTerm_6cc2a14909
          sharedTerm_eeda7d8794) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ := by rfl
    _ ≤ |s|⁻¹ * (2 * ‖f‖) :=
      mul_le_mul_of_nonneg_left ((norm_Lp_toLp_restrict_le Ω _).trans (by
          calc
            _ ≤ ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
                sharedTerm_6cc2a14909
                sharedTerm_eeda7d8794) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ +
                ‖(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ := norm_sub_le _ _
            _ = 2 * ‖f‖ := by
              rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
              ring)) (inv_nonneg.mpr (abs_nonneg s))
    _ = (2 / |s|) * ‖f‖ := by
      rw [div_eq_mul_inv]
      ring

section
variable {Ω inner outer : PDE.VelocityRegion d} {K : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)

section
variable (k : Fin d) (h : ℝ)

/-- The literal smooth B core is linear before any completion argument. -/
def energyTestSmoothCoreLinearMap

     (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
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
        (φ : PDE.ScalarField d) (ψ : PDE.ScalarField d)) y
  map_smul' c φ := by
    rw [← map_smul]
    congr 1
    apply PDE.WeakTestFunction.ext
    funext y
    simpa only [localizedSpatialDifferenceQuotientEnergyWeakTest, PDE.WeakTestFunction.smul_toFun,
      Pi.smul_def, smul_eq_mul, RingHom.id_apply] using
      congrFun (localizedSpatialDifferenceQuotientEnergyTest_smul c η k h
        (φ : PDE.ScalarField d)) y

/-- The quotient-safe scalar receiver dictated by the literal B test. -/
private def energyTestValueReceiver

     :
    H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 ) :=
  (-1 : ℝ) • (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)).comp
    ((localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
      (valueCLM hΩ))
end


/-- Each B gradient coordinate has the forced outer-quotient receiver. -/
private def energyTestGradientReceiver

    (j k : Fin d) (h : ℝ)  :=
  (-1 : ℝ) • (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)).comp
    ((cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq j k h).comp
        (valueCLM hΩ) +
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
        ((PDE.hilbertVectorLpCoord Ω (2 ) j).comp (gradientCLM hΩ)))

section
variable (k : Fin d) (h : ℝ)

private def energyTestGradientVectorReceiver

     :
    H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 ) :=
  PDE.hilbertVectorLpAssemble fun j => energyTestGradientReceiver hΩ η j k h

private theorem energyTestSmoothCore_value_eq_receiver

     (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    valueCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ) =
      energyTestValueReceiver hΩ η k h
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  let sharedTerm_cd97287621 := ((localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
    (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))))
  let sharedTerm_f2c7c002ee := ((localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift))
  have hcore : energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        sharedTerm_f2c7c002ee := by
    apply Subtype.ext
    rfl
  have hinput : smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
    apply Subtype.ext
    rfl
  rw [hcore, hinput]
  change valueCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        sharedTerm_f2c7c002ee) =
    (-1 : ℝ) • unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
      sharedTerm_cd97287621
  apply MeasureTheory.Lp.ext
  have hleft := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    sharedTerm_f2c7c002ee


  have hA := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η.sq k h
    _
    φ (ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ) (fun y hy => hηshift (sq_tsupport_subset η hy))

  have houter := unweightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet k (-h)
    sharedTerm_cd97287621
    _ hA (by
        intro y hy
        exact hηΩ (sq_tsupport_subset η
          (tsupport_localizedSpatialDifferenceQuotient_subset η.sq k h φ
            (subset_tsupport _ hy))))
  have hsmul := MeasureTheory.Lp.coeFn_smul (-1 : ℝ)
    (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
      sharedTerm_cd97287621)
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
end


private theorem energyTestSmoothCore_gradientCoord_eq_receiver

    (j k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    PDE.hilbertVectorLpCoord Ω (2 ) j
      (gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ)) =
      energyTestGradientReceiver hΩ η j k h
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  let sharedTerm_4fb58c4d3d := ((localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift))
  let ψ := localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
    ((sq_tsupport_subset η).trans hηΩ)
  let F : PDE.ScalarLp Ω (2 ) :=
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq j k h
        (valueCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)) +
      localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
        (PDE.hilbertVectorLpCoord Ω (2 ) j
          (gradientCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)))
  have hcore : energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        sharedTerm_4fb58c4d3d := by
    apply Subtype.ext
    rfl
  have hinput : smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
    apply Subtype.ext
    rfl

  have hcoord : PDE.hilbertVectorLpCoord Ω (2 ) j
      (gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)) = F := by
    dsimp only [F, ψ]
    exact localizedSpatialDifferenceQuotientWeakTest_gradientCoord_eq
      hΩ η.sq k h φ _ (fun y hy => hηshift (sq_tsupport_subset η hy)) j
  rw [hcore, hinput]
  change PDE.hilbertVectorLpCoord Ω (2 ) j
      (gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
          sharedTerm_4fb58c4d3d)) =
    (-1 : ℝ) • unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h) F
  apply MeasureTheory.Lp.ext
  have hleftCoord := PDE.coeFn_hilbertVectorLpCoord Ω _ j
    (gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        sharedTerm_4fb58c4d3d))
  have hleftJet := ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    sharedTerm_4fb58c4d3d j


  have houter := unweightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet k (-h) F ((ψ.partialDeriv j)) (by
        rw [← hcoord]
        exact (PDE.coeFn_hilbertVectorLpCoord Ω _ j
          (gradientCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ))).trans
          (ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ j)) (by
        intro y hy
        apply ψ.tsupport_subset
        by_contra hynot
        apply hy
        unfold PDE.WeakTestFunction.partialDeriv
        change (fderiv ℝ ψ.toFun y) (PDE.basisVec j) = 0
        rw [fderiv_of_notMem_tsupport ℝ hynot]
        exact ContinuousLinearMap.zero_apply _)
  have hsmul := MeasureTheory.Lp.coeFn_smul (-1 : ℝ)
    (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h) F)
  filter_upwards [hleftCoord, hleftJet, houter, hsmul] with y hleftCoord hleftJet houter hsmul
  rw [hleftCoord, hleftJet, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [houter]
  have hraw := energyWeakTest_partialDeriv_eq_backwardSquare
    η k h φ hηΩ hηshift j y
  dsimp only [ψ] at hraw ⊢
  rw [hraw]
  ring

private theorem energyTestSmoothCore_gradient_eq_receiver

    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ) =
      energyTestGradientVectorReceiver hΩ η k h
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  let sharedTerm_06a9da491c := ((energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ))
  let L : Fin d → H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 ) := fun j =>
    energyTestGradientReceiver hΩ η j k h
  have hcoord (j : Fin d) :
      PDE.hilbertVectorLpCoord Ω (2 ) j
        (gradientCLM hΩ sharedTerm_06a9da491c) =
      L j (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
    dsimp only [L]
    exact energyTestSmoothCore_gradientCoord_eq_receiver
      hΩ η j k h φ hηΩ hηshift
  change gradientCLM hΩ sharedTerm_06a9da491c =
    PDE.hilbertVectorLpAssemble L
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)
  apply MeasureTheory.Lp.ext
  have hcoords : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω, ∀ j : Fin d,
      gradientCLM hΩ sharedTerm_06a9da491c y j =
        L j (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) y := by
    apply ae_all_iff.mpr
    intro j
    have hleft := PDE.coeFn_hilbertVectorLpCoord Ω _ j
      (gradientCLM hΩ sharedTerm_06a9da491c)
    filter_upwards [hleft] with y hleft
    exact hleft.symm.trans (congrArg (fun z : PDE.ScalarLp Ω (2 ) => z y)
      (hcoord j))
  have hassemble := PDE.hilbertVectorLpAssemble_apply_ae L
    (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)
  filter_upwards [hcoords, hassemble] with y hcoords hassemble
  rw [hassemble]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).injective
  ext j
  simpa only [PiLp.coe_continuousLinearEquiv] using hcoords j
end





section
variable {Ω inner outer : PDE.VelocityRegion d} {K : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)

private theorem norm_energyTestValueReceiver_apply_le

    (k : Fin d) (h : ℝ) (u : H10HilbertGraph hΩ) :
    ‖energyTestValueReceiver hΩ η k h u‖ ≤ (4 / |h| ^ 2) * ‖u‖ := by
  let sharedTerm_88dc2e3367 := ((localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h (valueCLM hΩ u)))
  have hvalue : ‖valueCLM hΩ u‖ ≤ ‖u‖ := by
    let z  := (u : PDE.H1HilbertGraph Ω).1
    change ‖z.fst‖ ≤ ‖z‖
    exact WithLp.norm_fst_le _ z
  change ‖(-1 : ℝ) • unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
      sharedTerm_88dc2e3367‖ ≤ _
  calc
    _ = ‖unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
        sharedTerm_88dc2e3367‖ := by simp
    _ ≤ (2 / |-h|) * ‖sharedTerm_88dc2e3367‖ := norm_unweightedSpatialDifferenceQuotientL2_apply_le _ _ _ _
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

    (j k : Fin d) (h : ℝ) (u : H10HilbertGraph hΩ) :
    ‖energyTestGradientReceiver hΩ η j k h u‖ ≤
      (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by
  let sharedTerm_0baf1249c5 := (((PDE.hilbertVectorLpCoord Ω (2 ) j).comp (gradientCLM hΩ)))
  let sharedTerm_2ad339b5e0 := (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))
  let sharedTerm_cd46b7f9b3 := ((cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq j k h).comp (valueCLM hΩ) u)
  let sharedTerm_fe6408eca4 := ((4 * K / |h|) * ‖valueCLM hΩ u‖)




  change ‖(-1 : ℝ) • unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
      (sharedTerm_cd46b7f9b3 +
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
          sharedTerm_0baf1249c5 u)‖ ≤ _
  calc
    _ = ‖unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
        (sharedTerm_cd46b7f9b3 +
          (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
            sharedTerm_0baf1249c5 u)‖ := by
      rw [map_add]
      simp only [neg_one_smul]
      exact norm_neg _
    _ ≤ (2 / |-h|) * ‖sharedTerm_cd46b7f9b3 +
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
          sharedTerm_0baf1249c5 u‖ :=
      norm_unweightedSpatialDifferenceQuotientL2_apply_le _ _ _ _
    _ ≤ (2 / |h|) * (sharedTerm_fe6408eca4 +
        (2 / |h|) * ‖sharedTerm_2ad339b5e0‖) := by
      rw [abs_neg]
      apply mul_le_mul_of_nonneg_left
      · exact (norm_add_le _ _).trans (add_le_add (by
          change ‖cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq j k h
            (valueCLM hΩ u)‖ ≤ _
          calc
            _ ≤ (2 * (2 * K) / |h|) * ‖valueCLM hΩ u‖ :=
              norm_cutoffGradientSpatialDifferenceQuotientL2_apply_le
                hΩ.measurableSet η.sq j k h _
            _ = sharedTerm_fe6408eca4 := by ring) (by
          change ‖localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
            sharedTerm_2ad339b5e0‖ ≤ _
          exact norm_localizedSpatialDifferenceQuotientL2_apply_le
            hΩ.measurableSet η.sq k h
              sharedTerm_2ad339b5e0))
      · exact div_nonneg (by norm_num) (abs_nonneg h)
    _ ≤ (2 / |h|) * ((4 * K / |h|) * ‖u‖ + (2 / |h|) * ‖u‖) := by
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add
        · apply mul_le_mul_of_nonneg_left (by
            let z  := (u : PDE.H1HilbertGraph Ω).1
            change ‖z.fst‖ ≤ ‖z‖
            exact WithLp.norm_fst_le _ z)
          exact div_nonneg (mul_nonneg (by norm_num) η.gradient_bound_nonneg) (abs_nonneg h)
        · apply mul_le_mul_of_nonneg_left
            ((_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le j (gradientCLM hΩ u)).trans (by
                let z  := (u : PDE.H1HilbertGraph Ω).1
                change ‖z.snd‖ ≤ ‖z‖
                exact WithLp.norm_snd_le _ z))
          exact div_nonneg (by norm_num) (abs_nonneg h)
      · exact div_nonneg (by norm_num) (abs_nonneg h)
    _ = (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by ring

private theorem norm_energyTestGradientVectorReceiver_apply_le

    (k : Fin d) (h : ℝ) (u : H10HilbertGraph hΩ) :
    ‖energyTestGradientVectorReceiver hΩ η k h u‖ ≤
      (d : ℝ) * (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by
  let sharedTerm_7c1713bf79 := (4 * (2 * K + 1) / |h| ^ 2)
  let L : Fin d → H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 ) := fun j =>
    energyTestGradientReceiver hΩ η j k h
  change ‖PDE.hilbertVectorLpAssemble L u‖ ≤ _
  calc
    _ ≤ ∑ j, ‖L j u‖ := PDE.norm_hilbertVectorLpAssemble_apply_le L u
    _ ≤ ∑ _ : Fin d, (sharedTerm_7c1713bf79) * ‖u‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact norm_energyTestGradientReceiver_apply_le hΩ η j k h u
    _ = (d : ℝ) * (sharedTerm_7c1713bf79) * ‖u‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
end





section
variable {Ω inner outer : PDE.VelocityRegion d} {K : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)

private theorem norm_energyTestSmoothCoreLinearMap_apply_le
      (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ‖energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ‖ ≤
      (4 * (1 + (d : ℝ) * (2 * K + 1)) / |h| ^ 2) *
        ‖smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ‖ := by
  let x  := smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ
  let q  := energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ
  have hvalue : valueCLM hΩ q = energyTestValueReceiver hΩ η k h x := by
    simpa only [q, x] using energyTestSmoothCore_value_eq_receiver
      hΩ η k h φ hηΩ hηshift
  have hgradient : gradientCLM hΩ q = energyTestGradientVectorReceiver hΩ η k h x := by
    simpa only [q, x] using energyTestSmoothCore_gradient_eq_receiver
      hΩ η k h φ hηΩ hηshift
  calc
    ‖energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ‖ = ‖q‖ := rfl
    _ ≤ ‖valueCLM hΩ q‖ + ‖gradientCLM hΩ q‖ :=
      _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_h10HilbertGraph_le_value_add_gradient hΩ q
    _ = ‖energyTestValueReceiver hΩ η k h x‖ +
        ‖energyTestGradientVectorReceiver hΩ η k h x‖ := by rw [hvalue, hgradient]
    _ ≤ (4 / |h| ^ 2) * ‖x‖ +
        ((d : ℝ) * (4 * (2 * K + 1) / |h| ^ 2)) * ‖x‖ :=
      add_le_add (norm_energyTestValueReceiver_apply_le hΩ η k h x)
        (norm_energyTestGradientVectorReceiver_apply_le hΩ η k h x)
    _ = (4 * (1 + (d : ℝ) * (2 * K + 1)) / |h| ^ 2) * ‖x‖ := by ring

section
variable (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)

private theorem exists_energyTestSmoothCoreLinearMap_bound
       :
    ∃ C : ℝ, ∀ φ : PDE.WeakTestFunction Ω,
      ‖energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ‖ ≤ C *
        ‖smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ‖ := (Exists.intro (4 * (1 + ↑d * (2 * K + 1)) / |h| ^ 2) fun φ =>
  norm_energyTestSmoothCoreLinearMap_apply_le hΩ η k h φ hηΩ hηshift)

/-- The internal bounded extension of the smooth localized energy test. -/
def energyTestH10CLM
       :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
  (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift).extendOfNorm
    (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
end


private theorem energyTestH10CLM_apply_smooth
      (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    energyTestH10CLM hΩ η k h hηΩ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ := by
  unfold energyTestH10CLM
  exact LinearMap.extendOfNorm_eq
    (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
    (exists_energyTestSmoothCoreLinearMap_bound hΩ η k h hηΩ hηshift) φ
end


private theorem inner_scalarLp_eq_integral_mul_of_ae_eq
     {Ω : PDE.VelocityRegion d}
    (F G : PDE.ScalarLp Ω (2 )) (f g : PDE.ScalarField d)
    (hF : ⇑F =ᵐ[PDE.volumeOn Ω] f) (hG : ⇑G =ᵐ[PDE.volumeOn Ω] g) :
    inner ℝ F G = ∫ y, f y * g y ∂PDE.volumeOn Ω := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF, hG] with y hF hG
  rw [hF, hG]
  simp [mul_comm]

variable {Ω inner outer : PDE.VelocityRegion d} {K : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)

private theorem inner_value_energyTestSmoothCore_eq
      (φ ψ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    Inner.inner ℝ
      (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
      (valueCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift ψ)) =
      Inner.inner ℝ
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ))) := by
  let sharedTerm_fc1928421b := ((localizedSpatialDifferenceQuotientEnergyWeakTest η k h ψ ψ.contDiff hηΩ hηshift))
  have hφcore : smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
    apply Subtype.ext
    rfl
  have hψcore : energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift ψ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        sharedTerm_fc1928421b := by
    apply Subtype.ext
    rfl
  rw [hφcore, hψcore]
  have hφ := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ
  have hψ := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    sharedTerm_fc1928421b
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
      solve_by_elim (maxDepth := 4) [inner_scalarLp_eq_integral_mul_of_ae_eq, valueCLM, smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph, localizedSpatialDifferenceQuotientEnergyWeakTest, localizedSpatialDifferenceQuotientEnergyTest]
    _ = ∫ y, localizedSpatialDifferenceQuotient η k h φ y *
        localizedSpatialDifferenceQuotient η k h ψ y ∂PDE.volumeOn Ω := by
      change (∫ y in Ω, φ y * localizedSpatialDifferenceQuotientEnergyTest η k h ψ y) = _
      rw [setIntegral_mul_localizedSpatialDifferenceQuotientEnergyTest_eq
        η k h φ ψ φ.contDiff.continuous ψ.contDiff.continuous hηΩ hηshift]
    _ = _ := (inner_scalarLp_eq_integral_mul_of_ae_eq
      _
      _
      _
      _ hAφ hAψ).symm

section
variable (φ : PDE.WeakTestFunction Ω) (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)

private theorem value_localizedSpatialDifferenceQuotientH10CLM_apply_smooth
       :
    valueCLM hΩ
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) =
      localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) := (congrArg (fun M => M ((smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ) φ))
  (valueCLM_comp_localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift))

private def energyTestSmoothLeftPairCLM
       :
    H10HilbertGraph hΩ →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ
    (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))).comp
      ((valueCLM hΩ).comp (energyTestH10CLM hΩ η k h hηΩ hηshift))

private def localizedSmoothLeftPairCLM
       :
    H10HilbertGraph hΩ →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ
    (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))).comp
      ((valueCLM hΩ).comp (localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h hηΩ hηshift))

private theorem energyTestSmoothLeftPairCLM_apply
       (v : H10HilbertGraph hΩ) :
    energyTestSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift v =
      Inner.inner ℝ
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
        (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v)) := rfl
end


private theorem localizedSmoothLeftPairCLM_apply_smooth
      (φ ψ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    localizedSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ) =
      Inner.inner ℝ
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ))) := (id
  (Trans.trans
    (congrArg
      (fun z =>
        ⟪z,
          (valueCLM hΩ)
            ((localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift)
              ((smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ) ψ))⟫)
      (value_localizedSpatialDifferenceQuotientH10CLM_apply_smooth hΩ η k h φ hηΩ hηshift))
    (congrArg
      (Inner.inner ℝ
        ((localizedSpatialDifferenceQuotientL2 (IsOpen.measurableSet hΩ) η k h)
          ((valueCLM hΩ) ((smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ) φ))))
      (value_localizedSpatialDifferenceQuotientH10CLM_apply_smooth hΩ η k h ψ hηΩ hηshift))))

variable (φ : PDE.WeakTestFunction Ω)

private theorem energyTestSmoothLeftPairCLM_eq_localizedSmoothLeftPairCLM

    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
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
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ) =
        localizedSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ)
      rw [energyTestSmoothLeftPairCLM_apply]
      rw [energyTestH10CLM_apply_smooth hΩ η k h ψ hηΩ hηshift]
      rw [localizedSmoothLeftPairCLM_apply_smooth]
      exact inner_value_energyTestSmoothCore_eq hΩ η k h φ ψ hηΩ hηshift)) w

private theorem inner_value_energyTestH10CLM_eq_of_smooth_left
       (v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
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

variable (v : H10HilbertGraph hΩ)

section
variable (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)

private def energyTestFixedRightPairCLM

     : H10HilbertGraph hΩ →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v))).comp
    (valueCLM hΩ)

private def localizedFixedRightPairCLM

     : H10HilbertGraph hΩ →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ
    (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v))).comp
      ((valueCLM hΩ).comp (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift))
end


section
variable (φ : PDE.WeakTestFunction Ω) (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)

private theorem energyTestFixedRightPairCLM_apply_smooth
        :
    energyTestFixedRightPairCLM hΩ η k h v hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      Inner.inner ℝ (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v))
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) := rfl

private theorem localizedFixedRightPairCLM_apply_smooth
        :
    localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      Inner.inner ℝ (valueCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v))
        (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))) := rfl
end


private theorem energyTestFixedRightPairCLM_eq_localizedFixedRightPairCLM

    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    energyTestFixedRightPairCLM hΩ η k h v hηΩ hηshift =
      localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift := by
  apply ContinuousLinearMap.ext
  exact fun u => congrFun
    ((denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).equalizer
      (energyTestFixedRightPairCLM hΩ η k h v hηΩ hηshift).continuous
      (localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift).continuous (by
      funext φ
      change energyTestFixedRightPairCLM hΩ η k h v hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
        localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)
      rw [energyTestFixedRightPairCLM_apply_smooth]
      rw [localizedFixedRightPairCLM_apply_smooth]
      calc
        _ = Inner.inner ℝ
            (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
            (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v)) :=
          real_inner_comm _ _
        _ = Inner.inner ℝ (valueCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
              (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))
            (valueCLM hΩ
              (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v)) :=
          inner_value_energyTestH10CLM_eq_of_smooth_left hΩ η k h φ v hηΩ hηshift
        _ = _ := real_inner_comm _ _)) u

private theorem inner_value_energyTestH10CLM_eq
      (u v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    Inner.inner ℝ (valueCLM hΩ u)
      (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v)) =
    Inner.inner ℝ
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u))
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v)) := (Trans.trans
  (Trans.trans (real_inner_comm ((valueCLM hΩ) ((energyTestH10CLM hΩ η k h hηΩ hηshift) v)) ((valueCLM hΩ) u))
    (congrArg (fun M => M u) (energyTestFixedRightPairCLM_eq_localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift)))
  (real_inner_comm ((valueCLM hΩ) ((localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift) u))
    ((valueCLM hΩ) ((localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift) v))))

/-- The bounded H10 extension of the localized spatial energy test. -/
def localizedSpatialDifferenceQuotientEnergyTestH10CLM
      (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
  energyTestH10CLM hΩ η k h hηΩ hηshift

/-- The energy-test extension agrees with the literal bundled smooth core. -/
theorem localizedSpatialDifferenceQuotientEnergyTestH10CLM_apply_smooth
      (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) := (energyTestH10CLM_apply_smooth hΩ η k h φ hηΩ hηshift)

/-- The energy-test value pairing is the localized quotient inner product. -/
theorem inner_value_localizedSpatialDifferenceQuotientEnergyTestH10CLM_eq
      (u v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    Inner.inner ℝ (valueCLM hΩ u)
      (valueCLM hΩ
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h hηΩ hηshift v)) =
    Inner.inner ℝ
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u))
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v)) := inner_value_energyTestH10CLM_eq hΩ η k h u v hηΩ hηshift

end HypoellipticAleksandrov.Parabolic.Dirichlet
