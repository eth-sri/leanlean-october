/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.SpatialExpectationMeasurable
public import DOZZ.FourPoint.Fusion.LocalSecondKernel
/-! # Restricted signed spatial expectations -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
noncomputable def fusionSecondSpatial {Ω : Type*} [MeasurableSpace Ω] (mixed : Bool)
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (B : Set ℂ) (z : ℂ) : ℂ :=
  ∫ ω, ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ (-p - 1)).toReal : ℂ) *
    (∫ x in B, fusionSecondKernel mixed γ α₁ α₂ α₃ z x ∂M ω) ∂P

noncomputable abbrev fusionPureSpatial {Ω : Type*} [MeasurableSpace Ω] := fusionSecondSpatial (Ω := Ω) false
noncomputable abbrev fusionMixedSpatial {Ω : Type*} [MeasurableSpace Ω] := fusionSecondSpatial (Ω := Ω) true

/-- Restricting the spatial kernel to a fixed measurable region preserves parameter measurability. -/
theorem fusionSecondSpatial_measurable {Ω : Type*} [MeasurableSpace Ω] (mixed : Bool)
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (B : Set ℂ) (hB : MeasurableSet B) :
    Measurable (fusionSecondSpatial mixed P M γ α₁ α₂ α₃ p B) := by
  let H := (Prod.snd ⁻¹' B).indicator (fun q : ℂ × ℂ => fusionSecondKernel mixed γ α₁ α₂ α₃ q.1 q.2)
  have hH : Measurable H := (measurable_fusionSecondKernel mixed γ α₁ α₂ α₃).indicator
    (hB.preimage measurable_snd)
  have h := fusion_gammaHalf_spatial_expectation_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 1) H hH
  have he (z : ℂ) : (fun x => H (z, x)) = B.indicator (fusionSecondKernel mixed γ α₁ α₂ α₃ z) := by
    funext x
    by_cases hx : x ∈ B <;> simp [H, hx]
  unfold fusionSecondSpatial
  simpa only [he, integral_indicator hB] using h

end DOZZ.Proofs
