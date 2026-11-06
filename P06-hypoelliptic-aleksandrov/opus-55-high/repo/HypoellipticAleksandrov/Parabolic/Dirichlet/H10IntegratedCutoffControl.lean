module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10IntegratedHalfAbsorption
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10CutoffGradientBound
public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10IntegratedCoerciveConsequence

/-!
# Sign-free integrated cutoff-gradient control

This module replaces the signed companion-field term in integrated H10 half
absorption with its sign-free aggregate cutoff-gradient control.
-/

@[expose] public section


open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

namespace IsReverseTimeVariationalEnergySolution

variable {d : ℕ}



/-- The integrated cutoff-control H10 inequality has a Young constant uniform
in the reverse-time scalar test and all data satisfying the supplied literal
majorants. -/
theorem
  exists_uniform_timeTest_integral_h10Commutator_add_halfCoercive_le_cutoffControl_of_majorants
     {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
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
          (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialMatrixFDerivFrobeniusNorm
              (fun w : TimeVelocity d =>
                reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
          (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            PDE.vecEuclideanNorm
              (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
          (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialVectorFDerivFrobeniusNorm
              (fun w : TimeVelocity d =>
                reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
          (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
          (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialScalarFDerivEuclideanNorm
              (fun w : TimeVelocity d =>
                -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
          (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialScalarFDerivEuclideanNorm
              (fun w : TimeVelocity d =>
                -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
        ∀ (k : Fin d) (h : ℝ) (hh : |h| ≤ delta)
          (hζnonneg : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 0 ≤ ζ τ)
          (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
          (u : ReverseTimeL2V hΩ (r₁ - r₀))
          (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
          (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
            (sub_pos.mpr h₀₁) u g)
          (hu : IsReverseTimeVariationalEnergySolution
            r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
          let hχshift : Set.MapsTo
              (fun y : PDE.Vec d => y + h • PDE.basisVec k)
              (tsupport χ.toFun) Ω :=
            mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset
              hcarrier k hh
          let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
            intro y hy
            apply subset_tsupport
            change χ y ≠ 0
            rw [χ.eq_one_on_inner y hy]
            exact one_ne_zero
          let hηshift : Set.MapsTo
              (fun y : PDE.Vec d => y + h • PDE.basisVec k)
              (tsupport η.toFun) Ω :=
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
  obtain ⟨C_lam, hC_lam, hparent⟩ :=
  exists_uniform_timeTest_integral_h10Commutator_add_halfCoercive_le_nonprincipalYoung_of_majorants
    r₀ r₁ h₀₁ hΩ hΩbounded η χ delta hcarrier lam hlam M hM
  refine ⟨C_lam, hC_lam, ?_⟩
  intro zeta hzetaunit Lam hlamLam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
    hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu
  have hLam : 0 ≤ Lam := (le_of_lt hlam).trans hlamLam
  let hχshift  :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  let hηshift  := hχshift.mono_left hηχ
  let A  :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let Gv  :=
    fun τ => gradientCLM hΩ (A (u τ))
  let Wv  :=
    fun τ => cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h (u τ)
  have hparent' := hparent zeta hzetaunit Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth
    hLower hUpper hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu
  have hGsq : Integrable (fun τ => ‖Gv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := integrable_norm_sq_timewise_apply hΩ _ ((gradientCLM hΩ).comp A) u
  have hWsq : Integrable (fun τ => ‖Wv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := integrable_norm_sq_timewise_apply hΩ _
      _ u
  have hUsq : Integrable (fun τ => ‖gradientCLM hΩ (u τ)‖ ^ 2)
      (reverseTimeVolume (r₁ - r₀)) := integrable_norm_sq_timewise_apply hΩ _ _ u
  have hhalf : Integrable (fun τ => zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2))
      _ :=
    integrable_weighted zeta hzetaunit (hGsq.const_mul _)
  have hW : Integrable (fun τ => zeta τ * (Lam * ‖Wv τ‖ ^ 2))
      _ :=
    integrable_weighted zeta hzetaunit (hWsq.const_mul Lam)
  have hcutoff : Integrable (fun τ => zeta τ *
      (Lam * Kη ^ 2 * ‖gradientCLM hΩ _‖ ^ 2))
      _ :=
    integrable_weighted zeta hzetaunit (hUsq.const_mul _)
  have hparentBulk : Integrable (fun τ => zeta τ *
      ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [Pi.sub_def, mul_sub] using hhalf.sub hW
  have htargetBulk : Integrable (fun τ => zeta τ *
      ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [Pi.sub_def, mul_sub] using hhalf.sub hcutoff
  have hpoint : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2) ≤
      zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2) := by
    filter_upwards [hζnonneg] with τ hζτ
    have hcontrol : Lam * ‖Wv τ‖ ^ 2 ≤
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2 := by
      calc
        Lam * ‖Wv τ‖ ^ 2 ≤ Lam * (Kη ^ 2 * ‖gradientCLM hΩ _‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (norm_sq_cutoffGradientSpatialDifferenceQuotientH10CLM_apply_le_gradient
              hΩ η χ k h hχshift _) hLam
        _ = Lam * Kη ^ 2 * ‖gradientCLM hΩ _‖ ^ 2 := by ring
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hcontrol _) hζτ
  have hbulk :
      (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ _‖ ^ 2)
        ∂reverseTimeVolume _) ≤
      ∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume _ :=
    integral_mono_ae htargetBulk hparentBulk hpoint
  calc
    -(1 / 2) *
        (∫ τ, ‖valueCLM hΩ _‖ ^ 2 * zeta.deriv τ
          ∂reverseTimeVolume _) +
        (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
          Lam * Kη ^ 2 * ‖gradientCLM hΩ _‖ ^ 2)
          ∂reverseTimeVolume _) ≤
        -(1 / 2) *
          (∫ τ, ‖valueCLM hΩ _‖ ^ 2 * zeta.deriv τ
            ∂reverseTimeVolume _) +
          (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
            ∂reverseTimeVolume _) :=
      add_le_add_right hbulk _
    _ ≤ ∫ τ, zeta τ * (C_lam * (1 + ‖u τ‖ ^ 2))
        ∂reverseTimeVolume _ := hparent'

end IsReverseTimeVariationalEnergySolution

end HypoellipticAleksandrov.Parabolic.Dirichlet
