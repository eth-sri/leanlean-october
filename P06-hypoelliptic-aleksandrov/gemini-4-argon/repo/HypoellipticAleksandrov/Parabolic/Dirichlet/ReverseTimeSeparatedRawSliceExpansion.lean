module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet

/-!
# Reverse-time separated raw slice expansions

This module expands the fixed-time mass, source, and spatial-form pairings against joint value
and gradient representatives.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/- A joint reverse-time value representative expands the fixed-time mass pairing. -/
theorem reverseTime_raw_spatialForm_expand_ae
    {d Ω}
    (T r₁ : ℝ) (hΩ : IsOpen Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (u : ReverseTimeL2V hΩ T)
    (U : TimeVelocity d → ℝ)
    (hUslice : ∀ᵐ τ ∂reverseTimeVolume T,
      (fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u τ) y)
    (G : Fin d → TimeVelocity d → ℝ)
    (hGslice : ∀ᵐ τ ∂reverseTimeVolume T, ∀ j,
      (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => gradientCLM hΩ (u τ) y j)
    (ψ : PDE.WeakTestFunction Ω) :
    ∀ᵐ τ ∂reverseTimeVolume T,
      reverseTimeSpatialForm hΩ r₁ τ a b c (u τ)
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) =
        (∑ i : Fin d, ∑ j : Fin d,
          ∫ y, reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
            ψ.partialDeriv i y ∂PDE.volumeOn Ω) +
          (∑ j : Fin d, ∫ y,
            reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * ψ y
              ∂PDE.volumeOn Ω) -
          ∫ y, reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * ψ y
            ∂PDE.volumeOn Ω := by
  filter_upwards [hUslice, hGslice] with τ hU hG
  rw [reverseTimeSpatialForm_apply]
  have hprincipal (i j : Fin d) :
      (∫ y in Ω, a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
            (gradientCLM hΩ (u τ))) y *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ
              (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ))) y) =
        ∫ y, reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
          ψ.partialDeriv i y ∂PDE.volumeOn Ω := by
    apply integral_congr_ae
    filter_upwards
      [PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
        (gradientCLM hΩ (u τ)), hG j,
       PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (gradientCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)),
       ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ i] with
        y hGj hGyi hψi hψ
    rw [hGj, ← hGyi, hψi, hψ]
    simp only [reverseTimeCoefficient_apply]
  have hdrift (j : Fin d) :
      (∫ y in Ω, reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
            (gradientCLM hΩ (u τ))) y *
          (valueCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)) y) =
        ∫ y, reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * ψ y
          ∂PDE.volumeOn Ω := by
    apply integral_congr_ae
    filter_upwards
      [PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
        (gradientCLM hΩ (u τ)), hG j,
       ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ] with y hGj hGyi hψ
    rw [hGj, ← hGyi, hψ]
  have hscalar :
      (∫ y in Ω, reverseTimeScalarCoefficient r₁ c τ y *
          (valueCLM hΩ (u τ)) y *
          (valueCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)) y) =
        ∫ y, reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * ψ y
          ∂PDE.volumeOn Ω := by
    apply integral_congr_ae
    filter_upwards
      [hU, ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ] with y hUyi hψ
    rw [← hUyi, hψ]
  simp_rw [hprincipal, hdrift, hscalar]

end HypoellipticAleksandrov.Parabolic.Dirichlet
