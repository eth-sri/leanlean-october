module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedRawIntegrability
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedRawSliceExpansion
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedRawIntegralAlgebra
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedResidual
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductMeasure
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Reverse-time separated raw assembly

This module assembles the reverse-time variational residual into the literal spacetime raw
distribution identity using joint value and gradient representatives.
-/

 public section

open MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise MatrixOrder



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A reverse-time variational energy solution and joint value and gradient representatives
satisfy the global separated-product raw distribution identity. -/
theorem reverseTime_global_separated_product_distribution_of_reverseTimeVariationalEnergy
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood
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
    (initial : PDE.ScalarLp Ω (2 ))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu)
    (U : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hU : MemLp U (2 )
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hUslice : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      (fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u τ) y)
    (G : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hG : ∀ j, MemLp (G j) (2 )
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hGslice : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ j,
      (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => gradientCLM hΩ (u τ) y j)
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (psi : PDE.WeakTestFunction Ω) :
    let raw : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z =>
      U z * eta.deriv z.1 * psi z.2 -
        (∑ i : Fin d, ∑ j : Fin d,
          reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
            psi.partialDeriv i z.2) * eta z.1 -
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
            G j z * psi z.2) * eta z.1 +
        reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z *
          psi z.2 * eta z.1 -
        reverseTimeScalarCoefficient r₁ F z.1 z.2 * psi z.2 * eta z.1
    Integrable raw
        (timeVelocityVolumeOn
          (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) ∧
      (∫ z, raw z
        ∂timeVelocityVolumeOn
          (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) = 0 := by
  dsimp only
  letI : SFinite (reverseTimeVolume (r₁ - r₀)) := by
    dsimp only [reverseTimeVolume]
    infer_instance
  obtain ⟨hmass, hprincipal, hdrift, hscalar, hsource⟩ :=
    raw_reverseTime_separated_product_families_integrable r₀ r₁ hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth U hU G hG eta psi
  have hraw := integrable_full_reverseTime_separated_product_of_raw_families
    a b c F U G eta psi hmass hprincipal hdrift hscalar hsource
  refine ⟨hraw, ?_⟩
  have hprod := reverseTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn (r₁ - r₀) Ω
  rw [← hprod] at hmass hprincipal hdrift hscalar hsource hraw



  obtain ⟨_, hresidual⟩ := reverseTime_separated_residual_of_variationalEnergy
    r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu hu eta
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ psi)
  rw [← hprod]
  calc
    _ = ∫ τ, ∫ y,
        U (τ, y) * eta.deriv τ * psi y -
          (∑ i : Fin d, ∑ j : Fin d,
            reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
              psi.partialDeriv i y) * eta τ -
          (∑ j : Fin d,
            reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * psi y) * eta τ +
          reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ -
          reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ
        ∂PDE.volumeOn Ω ∂reverseTimeVolume (r₁ - r₀) := integral_prod _ hraw
    _ = _ := (integral_congr_ae (by
        filter_upwards [hmass.prod_right_ae, (show ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ i j : Fin d,
      Integrable (fun y => reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
        psi.partialDeriv i y * eta τ) (PDE.volumeOn Ω) by
            rw [ae_all_iff]
            intro i
            rw [ae_all_iff]
            intro j
            exact (hprincipal i j).prod_right_ae), (show ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ j : Fin d,
      Integrable (fun y => reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) *
        psi y * eta τ) (PDE.volumeOn Ω) by
            rw [ae_all_iff]
            intro j
            exact (hdrift j).prod_right_ae), hscalar.prod_right_ae,
          hsource.prod_right_ae,
          reverseTime_raw_mass_expand_ae (r₁ - r₀) hΩ u U hUslice psi,
          reverseTime_raw_spatialForm_expand_ae
            (r₁ - r₀) r₁ hΩ a b c u U hUslice G hGslice psi,
          ae_restrict_mem measurableSet_Ioo] with τ hm hp hq hc hs hM hA hτ
        exact reverseTime_raw_slice_integral_eq_residual  r₁ τ
          a b c F U G eta psi _ _ _ hm hp hq hc hs hM hA
          (reverseTime_raw_source_expand r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ hτ psi))).trans hresidual

end HypoellipticAleksandrov.Parabolic.Dirichlet
