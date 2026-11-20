module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialWeakDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.HessianTimeDerivativeL2Assembly
public import HypoellipticAleksandrov.Parabolic.Dirichlet.HessianCoefficientCancellation
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SeparatedTestsDetermineWeakTimeDerivative
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientL2WeakDerivative
import HypoellipticAleksandrov.Parabolic.ParabolicMemLpSpatialDifferenceQuotient
import HypoellipticAleksandrov.Analysis.L2Convergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10InteriorCaccioppoli
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGradientProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimePlateauCutoffDerivativeBound
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeInteriorCoefficientMajorant

/-! # Interior weak jets from the reverse-time Caccioppoli estimate -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter MeasureTheory Set
open scoped ENNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

private theorem gradientCoord_localizedSpatialDifferenceQuotientH10CLM_ae_eq_raw_on
    {d : ℕ} {Ω inner outer O : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (hOopen : IsOpen O)
    (hOinner : O ⊆ inner)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : η.ShiftMapsInto k h Ω)
    (j : Fin d) (u : H10HilbertGraph hΩ) (g : PDE.Vec d → ℝ)
    (hg : ⇑(PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u))
      =ᵐ[PDE.volumeOn Ω] g) :
    (fun y => PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
        (gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u)) y)
      =ᵐ[PDE.volumeOn O]
        fun y => (g (y + h • PDE.basisVec k) - g y) / h := by
  have hclass := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.gradientCoord_localizedSpatialDifferenceQuotientH10CLM_eq
    hΩ η k h hηΩ hηshift j u
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

private theorem exists_raw_gradientCoord_spatialDifferenceQuotient_memLp_norm_sq_le
    {d : ℕ} {Ω inner O : Set (PDE.Vec d)} {Kη : ℝ}
    (hΩ : IsOpen Ω) (T : ℝ)
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
    (hηshift : η.ShiftMapsInto k h Ω) :
    ∃ hD : ParabolicMemLpOn (J ×ˢ O) (2 : ℝ≥0∞)
        (spatialDifferenceQuotient k h (G j)),
      ‖hD.toLp (spatialDifferenceQuotient k h (G j))‖ ^ 2 ≤
        ∫ τ,
          ‖gradientCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM hΩ η k h
              η.tsupport_subset hηshift (u τ))‖ ^ 2
          ∂volume.restrict J := by
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let L := (gradientCLM hΩ).comp A
  let D := spatialDifferenceQuotient k h (G j)
  have hsupport (y : PDE.Vec d) (hy : y ∈ O) : y ∈ tsupport η.toFun := by
    apply subset_tsupport
    change η y ≠ 0
    simp [η.eq_one_on_inner y (hOinner hy)]
  have hOΩ : O ⊆ Ω := fun y hy => η.tsupport_subset (hsupport y hy)
  have hD : ParabolicMemLpOn (J ×ˢ O) 2 D :=
    ParabolicMemLpOn.spatialDifferenceQuotient_of_subset_mapsTo (hGmem j) k h
      (Set.prod_mono hJ hOΩ) (by
        rintro ⟨τ, y⟩ hz
        rw [spatialShift_apply]
        exact ⟨hJ hz.1, hηshift (hsupport y hz.2)⟩)
  have hprod : timeVelocityVolumeOn (J ×ˢ O) = (volume.restrict J).prod (PDE.volumeOn O) := by
    rw [timeVelocityVolumeOn, volume_timeVelocity_eq_prod, Measure.prod_restrict]
  have hμ : volume.restrict J ≤ reverseTimeVolume T := Measure.restrict_mono_set volume hJ
  have htime : MemLp (fun τ => L (u τ)) 2 (volume.restrict J) := (L.comp_memLp u).mono_measure hμ
  have hslice : ∀ᵐ τ ∂volume.restrict J,
      (fun y => D (τ, y)) =ᵐ[PDE.volumeOn O] fun y =>
        PDE.hilbertVectorLpCoord Ω 2 j (L (u τ)) y := by
    filter_upwards [hGslice.filter_mono (ae_mono hμ)] with τ hτ
    have hg := (hτ j).trans (PDE.coeFn_hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ (u τ))).symm
    simpa only [D, L, ContinuousLinearMap.comp_apply, spatialDifferenceQuotient_apply,
      spatialTranslate_apply, spatialShift_apply] using
      (gradientCoord_localizedSpatialDifferenceQuotientH10CLM_ae_eq_raw_on
      hΩ η hOopen hOinner k h η.tsupport_subset hηshift j (u τ) (fun y => G j (τ, y)) hg.symm).symm
  refine ⟨hD, ?_⟩
  rw [← Analysis.integral_real_sq_eq_norm_toLp_sq hD, hprod]
  have hi : Integrable (fun z => D z ^ 2) ((volume.restrict J).prod (PDE.volumeOn O)) :=
    hprod ▸ hD.integrable_sq
  rw [integral_prod _ hi]
  apply integral_mono_ae (Integrable.integral_prod_left hi) htime.norm.integrable_sq
  filter_upwards [hslice] with τ hτ
  let W := PDE.hilbertVectorLpCoord Ω 2 j (L (u τ))
  have hW := Lp.memLp W
  change (∫ y, D (τ, y) ^ 2 ∂PDE.volumeOn O) ≤ ‖L (u τ)‖ ^ 2
  rw [integral_congr_ae (hτ.mono fun y hy => congrArg (· ^ 2) hy)]
  calc
    _ ≤ ∫ y, W y ^ 2 ∂PDE.volumeOn Ω :=
      integral_mono_measure (Measure.restrict_mono_set volume hOΩ)
        (Eventually.of_forall fun _ => sq_nonneg _) hW.integrable_sq
    _ = ‖W‖ ^ 2 := by rw [Analysis.integral_real_sq_eq_norm_toLp_sq hW, Lp.toLp_coeFn]
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) (PDE.norm_hilbertVectorLpCoord_le j _) 2

namespace IsReverseTimeVariationalEnergySolution

/-- Recover the interior weak Hessian from spatial difference quotients, and
then the time derivative from the variational equation. -/
theorem exists_reverseTimeInteriorJet
    {d : ℕ} {Ω inner O : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (hd : 0 < d)
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (hOopen : IsOpen O) (hOinner : O ⊆ inner)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (τ₀ τ₁ τ₂ τ₃ : ℝ) (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁)
    (hτ₁τ₂ : τ₁ < τ₂) (hτ₂τ₃ : τ₂ < τ₃) (hτ₃ : τ₃ < r₁ - r₀)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hUpper : HasUpperEllipticityOn Lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcNonpos : ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω, c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω 2) (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu) :
    ∃ J : ParabolicW12Function d (Ioo τ₁ τ₂ ×ˢ O) 2,
      MemLp J.toFun 2 (timeVelocityVolumeOn (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) ∧
      (∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
        (fun y => J.toFun (τ, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u τ) y) ∧
      ∀ z, J.timeDeriv z =
        (∑ i, ∑ j, reverseTimeCoefficient r₁ a z.1 z.2 i j * J.velocityHessian z j i) +
        (∑ j, reverseTimeVectorCoefficient r₁ b z.1 z.2 j * J.velocityGrad z j) +
        reverseTimeScalarCoefficient r₁ c z.1 z.2 * J.toFun z -
        reverseTimeScalarCoefficient r₁ F z.1 z.2 := by
  obtain ⟨δ, hδ, hcarrier, hcac⟩ :=
    exists_uniform_interiorSpatialDifferenceQuotient_caccioppoli hd r₀ r₁ h₀₁ hΩ hΩbounded η χ
  obtain ⟨M, hM, hbound⟩ :=
    exists_reverseTimeInteriorCoefficientMajorant r₀ r₁ χ δ hcarrier
      a b c F haSmooth hbSmooth hcSmooth hFSmooth
  obtain ⟨ζ, Kζ, hKζ, hζnonneg, hζleOne, hζplateau, _, hζderiv⟩ :=
    exists_reverseTimeScalarTest_plateau_with_deriv_bound
      (r₁ - r₀) τ₀ τ₁ τ₂ τ₃ hτ₀.le hτ₀τ₁ hτ₁τ₂.le hτ₂τ₃ hτ₃.le
  obtain ⟨C_cac, _, hcac'⟩ := hcac Kζ hKζ lam Lam M hlam hlamLam hM
  obtain ⟨G, hG, hGslice⟩ := exists_reverseTimeL2V_gradient_coord_product_representatives hΩ (r₁ - r₀) u
  let Qin := Ioo τ₁ τ₂ ×ˢ O
  let B := C_cac * ((r₁ - r₀) +
    (reverseTimeGalerkinPrimalRadius
        ⟨h₀₁, hlam, hΩ, hΩbounded, a, b, c, F, haSmooth, hbSmooth, hcSmooth, hFSmooth, hLower, hcNonpos⟩ initial) ^ 2)
  have htime : Ioo τ₁ τ₂ ⊆ reverseTimeOpenInterval (r₁ - r₀) := fun τ hτ =>
    ⟨hτ₀.trans (hτ₀τ₁.trans hτ.1), hτ.2.trans (hτ₂τ₃.trans hτ₃)⟩
  have hOΩ : O ⊆ Ω := hOinner.trans η.inner_subset_outer
  have hQ := Set.prod_mono htime hOΩ
  have hGlocal (j : Fin d) : ParabolicMemLpOn Qin 2 (G j) :=
    (hG j).mono_measure (Measure.restrict_mono_set volume hQ)
  let hηshift (k : Fin d) (h : ℝ) (habs : |h| ≤ δ) : η.ShiftMapsInto k h Ω :=
    (mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k habs).mono_left χ.inner_subset_tsupport
  let hraw (j k : Fin d) (h : ℝ) (habs : |h| ≤ δ) :=
    exists_raw_gradientCoord_spatialDifferenceQuotient_memLp_norm_sq_le
      hΩ (r₁ - r₀) η hOopen hOinner (Ioo τ₁ τ₂) measurableSet_Ioo htime
      u G hG hGslice j k h (hηshift k h habs)
  have hsmall (h : ℝ) (hh0 : 0 < h) (hhδ : h < δ) : |h| ≤ δ := (abs_of_pos hh0).symm ▸ hhδ.le
  have hclose (j k : Fin d) := exists_hasWeakVelocityPartialDerivOn_norm_le_of_uniform_spatialDifferenceQuotient
    Qin (isOpen_Ioo.prod hOopen) k (G j) (hGlocal j) δ (Real.sqrt B) hδ
    (fun h hh0 hhδ => (hraw j k h (hsmall h hh0 hhδ)).choose) (by
      intro h hh0 hhδ
      have habs := hsmall h hh0 hhδ
      have henergy := hcac' ζ hζnonneg hζleOne hζderiv a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
        hbound initial u g hdu hu k h (abs_pos.mpr hh0.ne') habs
      let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
        localizedSpatialDifferenceQuotientH10CLM hΩ η k h
          η.tsupport_subset (hηshift k h habs)
      let e : ℝ → ℝ := fun τ => ‖gradientCLM hΩ (A (u τ))‖ ^ 2
      have heInt : Integrable e (reverseTimeVolume (r₁ - r₀)) := by
        exact integrable_norm_sq_timewise_apply
          hΩ (r₁ - r₀) ((gradientCLM hΩ).comp A) u
      have hζunit (τ : ℝ) : ‖ζ τ‖ ≤ 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg (hζnonneg τ)] using hζleOne τ
      have hweightedInt : Integrable (fun τ => ζ τ * e τ)
          (reverseTimeVolume (r₁ - r₀)) :=
        heInt.bdd_mul ζ.contDiff.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall hζunit)
      have hlocalWeighted : (∫ τ, e τ ∂volume.restrict (Set.Ioo τ₁ τ₂)) =
          ∫ τ in Set.Ioo τ₁ τ₂, ζ τ * e τ
            ∂reverseTimeVolume (r₁ - r₀) := by
        have hμ : (reverseTimeVolume (r₁ - r₀)).restrict (Set.Ioo τ₁ τ₂) =
            volume.restrict (Set.Ioo τ₁ τ₂) := by
          exact Measure.restrict_restrict_of_subset htime
        rw [← hμ]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
        rw [hζplateau τ ⟨hτ.1.le, hτ.2.le⟩, one_mul]
      have hlocalLe : (∫ τ, e τ ∂volume.restrict (Set.Ioo τ₁ τ₂)) ≤
          ∫ τ, ζ τ * e τ ∂reverseTimeVolume (r₁ - r₀) := by
        rw [hlocalWeighted]
        exact MeasureTheory.setIntegral_le_integral hweightedInt
          (Filter.Eventually.of_forall fun τ => mul_nonneg (hζnonneg τ) (sq_nonneg _))
      have hsq := (hraw j k h habs).choose_spec.trans (hlocalLe.trans henergy)
      exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans hsq)).mpr hsq)
  choose entry hHmem hHweak _ using hclose
  let H : TimeVelocity d → PDE.Mat d := fun z j k => entry j k z
  obtain ⟨U, hU, hUslice⟩ := exists_reverseTimeL2V_value_product_representative hΩ (r₁ - r₀) u
  have hUGlobal :=
    reverseTime_hasWeakVelocityPartialDerivOn_of_product_representatives
      hΩ (r₁ - r₀) u U hU hUslice G hG hGslice
  have hUweak : ∀ j : Fin d,
      HasWeakVelocityPartialDerivOn (Set.Ioo τ₁ τ₂ ×ˢ O) j U (G j) := by
    intro j
    exact (hUGlobal j).restrict (Set.prod_mono htime hOΩ)
  let W : TimeVelocity d → ℝ := fun z =>
    (∑ i : Fin d, ∑ j : Fin d,
      reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) +
    (∑ j : Fin d, reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) +
    reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z -
    reverseTimeScalarCoefficient r₁ F z.1 z.2
  have hUlocal : ParabolicMemLpOn Qin 2 U := hU.mono_measure (Measure.restrict_mono_set volume hQ)
  have hW : ParabolicMemLpOn
      (Set.Ioo τ₁ τ₂ ×ˢ O) (2 : ℝ≥0∞) W :=
    hessianTimeDerivative_memLp r₀ r₁ τ₁ τ₂ hΩ hΩbounded hOopen hOΩ htime
      a b c F haSmooth hbSmooth hcSmooth hFSmooth U hUlocal G hGlocal H hHmem
  have hsep :=
    reverseTime_separated_hessian_coefficient_cancellation
      r₀ r₁ h₀₁ hΩ hΩbounded hOopen hOΩ τ₁ τ₂ htime a b c F haSmooth hbSmooth
      hcSmooth hFSmooth initial u g hdu hu U hU hUslice G hG hGslice H hHmem hHweak
  have hWweak : HasWeakTimeDerivOn (Set.Ioo τ₁ τ₂ ×ˢ O) U W :=
    hasWeakTimeDerivOn_of_forall_separatedProduct hOopen hUlocal hW (by
      intro eta psi
      simpa only [W] using hsep eta psi)
  exact ⟨⟨U, W, fun z j => G j z, H, hUlocal, hW, hGlocal, hHmem,
    hWweak, hUweak, hHweak⟩, hU, hUslice, fun _ => rfl⟩

end IsReverseTimeVariationalEnergySolution
end HypoellipticAleksandrov.Parabolic.Dirichlet
