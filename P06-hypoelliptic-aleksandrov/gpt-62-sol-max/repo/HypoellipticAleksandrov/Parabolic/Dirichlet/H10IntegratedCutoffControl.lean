module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10CoerciveConsequence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientVariationalWeightedEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10CutoffGradientBound

/-!
# Sign-free integrated cutoff-gradient control

This module replaces the signed companion-field term in integrated H10 half
absorption with its sign-free aggregate cutoff-gradient control.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

namespace IsReverseTimeVariationalEnergySolution

/-- The integrated cutoff-control H10 inequality has a Young constant uniform
in the reverse-time scalar test and all data satisfying the supplied literal
majorants. -/
theorem
  exists_uniform_timeTest_integral_h10Commutator_add_halfCoercive_le_cutoffControl_of_majorants
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (delta : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) delta ⊆ Ω)
    (lam : ℝ) (hlam : 0 < lam) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C_lam : ℝ, 0 ≤ C_lam ∧
      ∀ (ζ : ReverseTimeScalarTest (r₁ - r₀))
        (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1),
      ∀ (Lam : ℝ) (hlamLam : lam ≤ Lam)
        (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
        (c F : ℝ → PDE.Vec d → ℝ),
        ∀ (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
          (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
          (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
          (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
          (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hUpper : HasUpperEllipticityOn Lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hbound : ReverseTimeCoefficientMajorant r₀ r₁ (tsupport χ.toFun) delta M a b c F),
        ∀ (k : Fin d) (h : ℝ) (hh : |h| ≤ delta)
          (hζnonneg : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 0 ≤ ζ τ)
          (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
          (u : ReverseTimeL2V hΩ (r₁ - r₀))
          (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
          (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
            (sub_pos.mpr h₀₁) u g)
          (hu : IsReverseTimeVariationalEnergySolution
            r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
          let hχshift : χ.ShiftMapsInto k h Ω :=
            mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset
              hcarrier k hh
          let hηχ := χ.inner_subset_tsupport
          let hηshift : η.ShiftMapsInto k h Ω :=
            hχshift.mono_left hηχ
          let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
            localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift
          let Gv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
            fun τ => gradientCLM hΩ (A (u τ))
          (-(1 / 2 : ℝ) *
              (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
                ∂reverseTimeVolume (r₁ - r₀)) +
            (∫ τ, ζ τ *
                ((lam / 2) * ‖Gv τ‖ ^ 2 -
                  Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
                ∂reverseTimeVolume (r₁ - r₀)) ≤
            (∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2))
              ∂reverseTimeVolume (r₁ - r₀))) := by
  obtain ⟨C_lam, hC, hfixed⟩ :=
    exists_uniform_timeTest_h10Commutator_add_coerciveTerm_le_nonprincipalYoung_of_majorants
      r₀ r₁ h₀₁ hΩ hΩbounded η χ delta hcarrier M hM (lam / 2) (half_pos hlam)
  refine ⟨C_lam, hC, ?_⟩
  intro ζ hζunit Lam hlamLam a b c F ha hb hc hF hlo hhi
    hbound k h hh hζnonneg initial u g hdu hu
  let hχshift := mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  let hηshift := hχshift.mono_left χ.inner_subset_tsupport
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let B := localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h η.tsupport_subset hηshift
  let G := (gradientCLM hΩ).comp A
  let W := cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hF
  let R := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc u
  let Q (τ : ℝ) := ζ τ * ((S τ) (B (u τ)) - (R τ) (B (u τ)))
  let L (τ : ℝ) := ζ τ * ((lam / 2) * ‖G (u τ)‖ ^ 2 - Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
  let Y (τ : ℝ) := ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2))
  let μ := reverseTimeVolume (r₁ - r₀)
  haveI : IsFiniteMeasure μ := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) (r₁ - r₀)))
    infer_instance
  have hQ : Integrable Q μ := ζ.integrable_mul
    ((integrable_reverseTimeDualPairing_timewiseCLM hΩ _ B u S).sub
      (integrable_reverseTimeDualPairing_timewiseCLM hΩ _ B u R))
  have hL : Integrable L μ := ζ.integrable_mul
    (((integrable_norm_sq_timewise_apply hΩ _ G u).const_mul (lam / 2)).sub
      ((integrable_norm_sq_timewise_apply hΩ _ (gradientCLM hΩ) u).const_mul (Lam * Kη ^ 2)))
  have hUsq : Integrable (fun τ => ‖u τ‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) u u
  have hY : Integrable Y μ := ζ.integrable_mul (((integrable_const (1 : ℝ)).add hUsq).const_mul C_lam)
  have hmono : ∀ᵐ τ ∂μ, Q τ + L τ ≤ Y τ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hζnonneg,
      ae_reverseTimeNegativeSource_apply r₀ r₁ h₀₁ hΩ hΩbounded F hF,
      ae_reverseTimeSpatialFormBochnerAction_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc u]
      with τ hτ hζτ hsource hform
    have ht : τ ∈ Icc 0 (r₁ - r₀) := ⟨hτ.1.le, hτ.2.le⟩
    let v := B (u τ)
    have hs : (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hF τ) v = (S τ) v :=
      congrArg (fun q => q v) ((reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc
        r₀ r₁ h₀₁ hΩ hΩbounded F hF τ ht).trans (hsource hτ).symm)
    have hp : ζ τ * ((reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hF τ) v -
        reverseTimeSpatialForm hΩ r₁ τ a b c (u τ) v) +
        ζ τ * (lam * ‖G (u τ)‖ ^ 2 - Lam * ‖W (u τ)‖ ^ 2) ≤
        ζ τ * ((lam / 2) * ‖G (u τ)‖ ^ 2 + C_lam * (1 + ‖u τ‖ ^ 2)) :=
      hfixed ζ hζunit lam Lam a b c F ha hb hc hF hlo hhi hbound k h hh τ ht hζτ (u τ)
    rw [hs, ← hform v] at hp
    have hcut := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (norm_sq_cutoffGradientSpatialDifferenceQuotientH10CLM_apply_le_gradient
        hΩ η χ k h hχshift (u τ)) (hlam.le.trans hlamLam)) hζτ
    change ζ τ * (Lam * ‖W (u τ)‖ ^ 2) ≤
      ζ τ * (Lam * (Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)) at hcut
    change ζ τ * ((S τ) v - (R τ) v) + L τ ≤ Y τ
    dsimp only [L, Y]
    linear_combination hp + hcut
  have he : -(1 / 2 : ℝ) * (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ ∂μ) =
      ∫ τ, Q τ ∂μ := by
    have he := integral_localizedSpatialDifferenceQuotient_norm_sq_mul_reverseTimeScalarTest_deriv_eq
      r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF initial u g hdu hu η k h η.tsupport_subset hηshift ζ
    change (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ ∂μ) =
      -(∫ τ, (2 * ((S τ) (B (u τ)) - (R τ) (B (u τ)))) * ζ τ ∂μ) at he
    rw [he, neg_mul_neg, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with τ
    dsimp only [Q]
    ring
  change -(1 / 2 : ℝ) * (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ ∂μ) +
    (∫ τ, L τ ∂μ) ≤ ∫ τ, Y τ ∂μ
  rw [he, ← integral_add hQ hL]
  exact integral_mono_ae (hQ.add hL) hY hmono

end IsReverseTimeVariationalEnergySolution

end HypoellipticAleksandrov.Parabolic.Dirichlet
