/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.OneChannel
public import DOZZ.FourPoint.Crossing.CoefficientExtraction
public import DOZZ.FourPoint.Crossing.DiagonalUniqueness
public import DOZZ.FourPoint.Crossing.Multiplier
public import DOZZ.FourPoint.Crossing.Normalization
public import DOZZ.Statements.Correlations.UnitVolumeStructureConstantSymmetricExtended
public import DOZZ.Hypergeom.ClassificationDiagonalConnection
public import DOZZ.Hypergeom.ConnectionDiagonalCoefficients
import Mathlib.Tactic
public import DOZZ.Correlations.Symmetry.SymmetricExtended

/-! # Crossing coefficient assembly with both analytic inputs visible

The two premises are literal specializations of the conclusions of
`degenerateFourPoint_diagonal_classification` and
`gammaHalf_full_unreflected_formula`. This is not the unconditional proof of
`DOZZ.gammaHalf_crossing`, nor a reduction from the unreflected formula alone. The global
zero-channel classification remains an additional BPZ input.
-/

public section
open MeasureTheory
namespace DOZZ.Proofs

/-- With the original diagonal classification and the admissible epsilon-channel
unreflected formula, the connection matrix gives both literal crossing identities. -/
theorem gammaHalf_crossing_of_diagonal_and_unreflected {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α' ε α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hεhi : ε < 2 / γ) (hα : α < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ < α + α' + ε - γ / 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hdiagonal :
      let a := gaussParameterA γ (γ / 2) α' ε α
      let b := gaussParameterB γ (γ / 2) α' ε α
      let c := gaussParameterC γ (γ / 2) α'
      ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-γ / 2) α' ε α z =
        structureConstant P M γ μ (α' - γ / 2) ε α *
          (‖gaussFMinus H a b c z‖ ^ 2 + gaussCoefficientRatio a b c *
            ‖gaussFPlus H a b c z‖ ^ 2))
    (hformula :
      let a := gaussParameterA γ (γ / 2) ε α' α
      let b := gaussParameterB γ (γ / 2) ε α' α
      let c := gaussParameterC γ (γ / 2) ε
      ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-γ / 2) ε α' α z =
        structureConstant P M γ μ (ε - γ / 2) α' α * ‖gaussFMinus H a b c z‖ ^ 2 +
        (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * ε)).re) *
          structureConstant P M γ μ (ε + γ / 2) α' α * ‖gaussFPlus H a b c z‖ ^ 2) :
    structureConstant P M γ μ (α' - γ / 2) ε α =
      gammaHalfCrossingMultiplier γ μ α' ε α *
        structureConstant P M γ μ α' (ε + γ / 2) α ∧
    unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
      gammaHalfUnitCrossingMultiplier γ μ α' ε α *
        unitVolumeStructureConstant P M γ α' (ε + γ / 2) α := by
  let a := gaussParameterA γ (γ / 2) α' ε α
  let b := gaussParameterB γ (γ / 2) α' ε α
  let c := gaussParameterC γ (γ / 2) α'
  let d₀ := structureConstant P M γ μ (α' - γ / 2) ε α
  let e₀ := structureConstant P M γ μ (ε - γ / 2) α' α
  let Bε := -μ * (planarGaussConstant (γ ^ 2 / 2) (γ * ε)).re
  let e₁ := Bε * structureConstant P M γ μ (ε + γ / 2) α' α
  have hεQ : ε < Q γ := by unfold Q; linarith only [hεhi, hγ]
  have hsum : 2 * Q γ + γ / 2 < α' + ε + α := by linarith only [hs]
  obtain ⟨ha, hab, hbc, hc1, hδ, hδ1, _, hK₂⟩ :=
    DOZZ.gauss_physical_parameter_range γ (γ / 2) α' ε α hγ hγ2 (Or.inl rfl)
      hsum hα' hεQ hα
  obtain ⟨hcn, hδn, _⟩ := crossing_gammaHalf_parameter_guards γ α' ε α hγ hγ2 hεhi hα' hα hs
  have hone := gammaHalf_one_channel_of_full_unreflected H P X M γ μ α' ε α hγ hγ2 hX hM hformula
  obtain ⟨hcross, -, hE⟩ := crossing_diagonal_transfer hH a b c d₀ e₀ e₁
    hcn hδn hK₂.ne' hdiagonal hone
  have hex := crossing_diagonal_coefficient_extraction a b c _ _ _ ha hab hbc hc1 hδ hδ1 hcross hE
  have hpQ : ε + γ / 2 < Q γ := by unfold Q; linarith only [hεhi]
  have hpS : 0 < sExp γ (ε + γ / 2) α' α := div_pos (by linarith only [hs, hγ]) hγ
  have hswap : structureConstant P M γ μ (ε + γ / 2) α' α =
      structureConstant P M γ μ α' (ε + γ / 2) α :=
    structureConstant_swap12 P X M hγ hγ2 hX hM (extendedSeiberg3_of_sExp_pos hγ hpQ hα' hα hpS)
  change d₀ = _ * e₁ at hex
  have hfull : structureConstant P M γ μ (α' - γ / 2) ε α =
      gammaHalfCrossingMultiplier γ μ α' ε α *
        structureConstant P M γ μ α' (ε + γ / 2) α := by
    dsimp [e₁, Bε] at hex
    rw [hswap, ← mul_assoc, crossing_connection_times_fusion γ μ α' ε α] at hex
    exact hex
  exact ⟨hfull, gammaHalf_crossing_unit_of_full P M γ μ α' ε α hγ hμ hs hfull⟩

end DOZZ.Proofs
