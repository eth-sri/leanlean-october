module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10IntegratedHalfAbsorption
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10CutoffGradientBound
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.H10IntegratedCoerciveConsequence

open private HypoellipticAleksandrov.Parabolic.Dirichlet.IsReverseTimeVariationalEnergySolution.integrable_norm_sq_timewise_apply from HypoellipticAleksandrov.Parabolic.Dirichlet.H10IntegratedCoerciveConsequence
open private HypoellipticAleksandrov.Parabolic.Dirichlet.IsReverseTimeVariationalEnergySolution.integrable_weighted from HypoellipticAleksandrov.Parabolic.Dirichlet.H10IntegratedCoerciveConsequence


/-!
# Sign-free integrated cutoff-gradient control

This module replaces the signed companion-field term in integrated H10 half
absorption with its sign-free aggregate cutoff-gradient control.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

namespace IsReverseTimeVariationalEnergySolution

/-- The reducible exact output proposition of integrated H10 half coercivity
with sign-free cutoff-gradient control.  This names a conclusion and is not an
assumption package. -/
abbrev integratedH10HalfCoerciveCutoffControlOutput
    {d : ℕ} {Ω inner : PDE.VelocityRegion d} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)
    (_haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (_hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧
      ∀ lam : ℝ, 0 < lam →
        ∃ C_lam : ℝ, 0 ≤ C_lam ∧
          ∀ (Lam : ℝ)
            (hLower : ∀ z : TimeVelocity d,
              z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
            (hUpper : ∀ z : TimeVelocity d,
              z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                a z.1 z.2 ≤ Lam • (1 : PDE.Mat d)),
            ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
              ∃ hχshift : Set.MapsTo
                (fun y  => y + h • PDE.basisVec k)
                (tsupport χ.toFun) Ω,
              ∀ (hζnonneg :
                  ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 0 ≤ ζ τ)
                (initial : PDE.ScalarLp Ω (2 ))
                (u : ReverseTimeL2V hΩ (r₁ - r₀))
                (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
                (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
                  (sub_pos.mpr h₀₁) u g)
                (hu : IsReverseTimeVariationalEnergySolution
                  r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
                let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
                  intro y hy
                  apply subset_tsupport
                  change χ y ≠ 0
                  rw [χ.eq_one_on_inner y hy]
                  exact one_ne_zero
                let hηshift : Set.MapsTo
                    (fun y  => y + h • PDE.basisVec k)
                    (tsupport η.toFun) Ω :=
                  hχshift.mono_left hηχ
                let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
                  localizedSpatialDifferenceQuotientH10CLM
                    hΩ η k h η.tsupport_subset hηshift
                let Gv : ℝ → PDE.HilbertVectorLp Ω (2 ) :=
                  fun τ => gradientCLM hΩ (A (u τ))
                (-(1 / 2 : ℝ) *
                    (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
                      ∂reverseTimeVolume (r₁ - r₀)) +
                  (∫ τ, ζ τ *
                    ((lam / 2) * ‖Gv τ‖ ^ 2 -
                      max Lam 0 * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
                    ∂reverseTimeVolume (r₁ - r₀)) ≤
                  (∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2))
                    ∂reverseTimeVolume (r₁ - r₀)))







/-- The integrated cutoff-control H10 inequality has a Young constant uniform
in the reverse-time scalar test and all data satisfying the supplied literal
majorants. -/
theorem
  exists_uniform_timeTest_integral_h10Commutator_add_halfCoercive_le_cutoffControl_of_majorants
    {d : ℕ} {Ω inner : PDE.VelocityRegion d} {Kη Kχ : ℝ}
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
        (a : CoefficientField d) (b : PDE.TimeVectorField d)
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
          (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialMatrixFDerivFrobeniusNorm
              (fun w  =>
                reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
          (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            PDE.vecEuclideanNorm
              (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
          (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialVectorFDerivFrobeniusNorm
              (fun w  =>
                reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
          (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
          (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialScalarFDerivEuclideanNorm
              (fun w  =>
                -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
          (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialScalarFDerivEuclideanNorm
              (fun w  =>
                -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
        ∀ (k : Fin d) (h : ℝ) (hh : |h| ≤ delta)
          (hζnonneg : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 0 ≤ ζ τ)
          (initial : PDE.ScalarLp Ω (2 ))
          (u : ReverseTimeL2V hΩ (r₁ - r₀))
          (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
          (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
            (sub_pos.mpr h₀₁) u g)
          (hu : IsReverseTimeVariationalEnergySolution
            r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
          let hχshift : Set.MapsTo
              (fun y  => y + h • PDE.basisVec k)
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
              (fun y  => y + h • PDE.basisVec k)
              (tsupport η.toFun) Ω :=
            hχshift.mono_left hηχ
          let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
            localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift
          let Gv : ℝ → PDE.HilbertVectorLp Ω (2 ) :=
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

  let hχshift  :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh

  let hηshift  := hχshift.mono_left (by
      intro y hy
      apply subset_tsupport
      change χ y ≠ 0
      rw [χ.eq_one_on_inner y hy]
      exact one_ne_zero)
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let Gv : ℝ → PDE.HilbertVectorLp Ω (2 ) :=
    fun τ => gradientCLM hΩ (A (u τ))
  let Wv  :=
    fun τ => cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h (u τ)
  have hparent' := hparent zeta hzetaunit Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth
    hLower hUpper hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu



  have hhalf  :=
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.IsReverseTimeVariationalEnergySolution.integrable_weighted zeta hzetaunit ((show Integrable (fun τ => ‖Gv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) by
        exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.IsReverseTimeVariationalEnergySolution.integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) ((gradientCLM hΩ).comp A) u).const_mul (lam / 2))
  have hW  :=
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.IsReverseTimeVariationalEnergySolution.integrable_weighted zeta hzetaunit ((show Integrable (fun τ => ‖Wv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) by
        exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.IsReverseTimeVariationalEnergySolution.integrable_norm_sq_timewise_apply hΩ (r₁ - r₀)
          (cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h) u).const_mul Lam)
  have hcutoff  :=
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.IsReverseTimeVariationalEnergySolution.integrable_weighted zeta hzetaunit ((show Integrable (fun τ => ‖gradientCLM hΩ (u τ)‖ ^ 2)
      (reverseTimeVolume (r₁ - r₀)) by
        exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.IsReverseTimeVariationalEnergySolution.integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) (gradientCLM hΩ) u).const_mul (Lam * Kη ^ 2))




  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * zeta.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, zeta τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * zeta.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, zeta τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀) at hparent'
  calc
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * zeta.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
        (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
          Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
          ∂reverseTimeVolume (r₁ - r₀)) ≤
        -(1 / 2 : ℝ) *
          (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * zeta.deriv τ
            ∂reverseTimeVolume (r₁ - r₀)) +
          (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
            ∂reverseTimeVolume (r₁ - r₀)) :=
      add_le_add_right (integral_mono_ae (by
          simpa only [Pi.sub_def, mul_sub] using hhalf.sub hcutoff) (by
          simpa only [Pi.sub_def, mul_sub] using hhalf.sub hW) (by
          filter_upwards [hζnonneg] with τ hζτ

          exact mul_le_mul_of_nonneg_left (sub_le_sub_left (by
              calc
                Lam * ‖Wv τ‖ ^ 2 ≤ Lam * (Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2) :=
                  mul_le_mul_of_nonneg_left
                    (norm_sq_cutoffGradientSpatialDifferenceQuotientH10CLM_apply_le_gradient
                      hΩ η χ k h hχshift (u τ)) ((le_of_lt hlam).trans hlamLam)
                _ = Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2 := by ring) _) hζτ)) _
    _ ≤ ∫ τ, zeta τ * (C_lam * (1 + ‖u τ‖ ^ 2))
        ∂reverseTimeVolume (r₁ - r₀) := hparent'

end IsReverseTimeVariationalEnergySolution

end HypoellipticAleksandrov.Parabolic.Dirichlet
