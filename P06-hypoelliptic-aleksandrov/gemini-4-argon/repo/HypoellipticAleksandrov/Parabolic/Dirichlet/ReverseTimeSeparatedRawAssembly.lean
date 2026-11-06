module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedRawIntegrability
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedRawSliceExpansion
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedRawIntegralAlgebra
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedResidual
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductMeasure
public import Mathlib.MeasureTheory.Integral.Prod
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGradientProductRepresentative
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorContinuity
import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductRepresentative
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm

/-!
# Reverse-time separated raw assembly

This module assembles the reverse-time variational residual into the literal spacetime raw
distribution identity using joint value and gradient representatives.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/- A reverse-time variational energy solution and joint value and gradient representatives
satisfy the global separated-product raw distribution identity. -/
theorem reverseTime_global_separated_product_distribution_of_reverseTimeVariationalEnergy
    {d Ω}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
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
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu)
    (U : TimeVelocity d → ℝ)
    (hU : MemLp U (2 : ℝ≥0∞)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hUslice : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      (fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u τ) y)
    (G : Fin d → TimeVelocity d → ℝ)
    (hG : ∀ j, MemLp (G j) (2 : ℝ≥0∞)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hGslice : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ j,
      (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => gradientCLM hΩ (u τ) y j)
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (psi : PDE.WeakTestFunction Ω) :
    let raw : TimeVelocity d → ℝ := fun z =>
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
  have hraw : Integrable (fun z : TimeVelocity d =>
      U z * eta.deriv z.1 * psi z.2 -
        (∑ i : Fin d, ∑ j : Fin d,
          reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
            psi.partialDeriv i z.2) * eta z.1 -
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
            G j z * psi z.2) * eta z.1 +
        reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z *
          psi z.2 * eta z.1 -
        reverseTimeScalarCoefficient r₁ F z.1 z.2 *
          psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
    have hprincipalSum : Integrable (fun z : TimeVelocity d =>
        ∑ i : Fin d, ∑ j : Fin d,
          reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
            psi.partialDeriv i z.2 * eta z.1)
        (timeVelocityVolumeOn
          (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
      apply integrable_finset_sum Finset.univ
      intro i _
      apply integrable_finset_sum Finset.univ
      intro j _
      exact hprincipal i j
    have hdriftSum : Integrable (fun z : TimeVelocity d =>
        ∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
            G j z * psi z.2 * eta z.1)
        (timeVelocityVolumeOn
          (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
      apply integrable_finset_sum Finset.univ
      intro j _
      exact hdrift j
    have hprincipal' : Integrable (fun z : TimeVelocity d =>
        (∑ i : Fin d, ∑ j : Fin d,
          reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
            psi.partialDeriv i z.2) * eta z.1)
        (timeVelocityVolumeOn
          (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
      refine hprincipalSum.congr (ae_of_all _ fun z => ?_)
      simp only [Finset.sum_mul]
    have hdrift' : Integrable (fun z : TimeVelocity d =>
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
            G j z * psi z.2) * eta z.1)
        (timeVelocityVolumeOn
          (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
      refine hdriftSum.congr (ae_of_all _ fun z => ?_)
      simp only [Finset.sum_mul]
    exact (((hmass.sub hprincipal').sub hdrift').add hscalar).sub hsource
  refine ⟨hraw, ?_⟩
  have hprod := reverseTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn (r₁ - r₀) Ω
  rw [← hprod] at hmass hprincipal hdrift hscalar hsource hraw
  have hprincipalAE : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ i j : Fin d,
      Integrable (fun y => reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
        psi.partialDeriv i y * eta τ) (PDE.volumeOn Ω) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact (hprincipal i j).prod_right_ae
  have hdriftAE : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ j : Fin d,
      Integrable (fun y => reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) *
        psi y * eta τ) (PDE.volumeOn Ω) := by
    rw [ae_all_iff]
    intro j
    exact (hdrift j).prod_right_ae
  have hslice : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      (∫ y,
        U (τ, y) * eta.deriv τ * psi y -
          (∑ i : Fin d, ∑ j : Fin d,
            reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
              psi.partialDeriv i y) * eta τ -
          (∑ j : Fin d,
            reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * psi y) * eta τ +
          reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ -
          reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ
        ∂PDE.volumeOn Ω) =
        inner ℝ (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ psi))
          (valueCLM hΩ (u τ)) * eta.deriv τ -
        reverseTimeSpatialForm hΩ r₁ τ a b c (u τ)
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ psi) * eta τ +
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ psi) * eta τ := by
    have _h_xinl_0 : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), inner ℝ (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ psi)) (valueCLM hΩ (u τ)) = ∫ y, U (τ, y) * psi y ∂PDE.volumeOn Ω := by
      let T := (r₁ - r₀)
      filter_upwards [hUslice] with τ hU
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards
        [ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ psi, hU] with y hψ hy
      rw [hψ, ← hy]
      simp only [RCLike.inner_apply, conj_trivial]
    filter_upwards [hmass.prod_right_ae, hprincipalAE, hdriftAE, hscalar.prod_right_ae,
      hsource.prod_right_ae,
      _h_xinl_0,
      reverseTime_raw_spatialForm_expand_ae
        (r₁ - r₀) r₁ hΩ a b c u U hUslice G hGslice psi,
      ae_restrict_mem measurableSet_Ioo] with τ hm hp hq hc hs hM hA hτ
    have _h_xinl_0 : reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ psi) = -(∫ y, reverseTimeScalarCoefficient r₁ F τ y * psi y ∂PDE.volumeOn Ω) := by
      have hτIcc : τ ∈ Set.Icc 0 (r₁ - r₀) :=
        ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
      rw [reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc
          r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ hτIcc,
        reverseTimeSourceFunctional_apply, L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards
        [coeFn_reverseTimeSourceSlice r₁ τ F
          (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
            r₀ r₁ hΩ hΩbounded F hFSmooth τ hτIcc),
          ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ psi] with y hF hψ
      rw [hψ, hF]
      simp only [RCLike.inner_apply, conj_trivial, reverseTimeScalarCoefficient_apply]
    exact reverseTime_raw_slice_integral_eq_residual (T := r₁ - r₀) r₁ τ
      a b c F U G eta psi _ _ _ hm hp hq hc hs hM hA
      _h_xinl_0
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
        ∂PDE.volumeOn Ω ∂reverseTimeVolume (r₁ - r₀) := by
      exact integral_prod _ hraw
    _ = _ := (integral_congr_ae hslice).trans hresidual

end HypoellipticAleksandrov.Parabolic.Dirichlet
