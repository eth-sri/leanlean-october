/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.SharedHyp

public import DOZZ.ShiftEquations.DualR.SeedFull
public import DOZZ.ShiftEquations.DualR.FirstShiftFull

/-!
# The second dual crossing seed in shifted form

Where both the continued second dual seed and the first structure shift hold, the structure
constant `C(2Q - ε - 2/γ, α, α')` in the seed can be replaced by its shifted form
`-𝒜(2Q - ε - 2/γ - γ/2) C(2Q - ε - 2/γ - γ)/(πμ)`. Unlike the original, the shifted form stays
meromorphic as `ε` crosses `γ/2` with the spectators `(α, α')` near `(γ/2, 2/γ)`: this is the
source's use of the gluing lemma in the proof of the `2/γ` shift equation. The shifted identity
holds near every point where all its ingredients are analytic.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **The shifted second dual seed at one point.** -/
theorem starG_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hSeed : SeedHyp P X M γ μ)
    (hShiftGluing : ShiftGluingHyp P X M γ μ)
    {hR : ℝ} (hhR : 0 < hR) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR))
    {BR : ℝ → Ω → BrownianPath × BrownianPath} {ZR : Ω → Measure ℝ}
    (hBR : ReflectionDataFamily P γ BR ZR)
    (hRv : ReflectionFamily P γ μ R BR ZR)
    {ε α α' : ℝ} (h₁ : ExtendedSeiberg3 γ (2 * Q γ - ε - 2 / γ) α α')
    (h₂ : ExtendedSeiberg3 γ ε (2 * Q γ - α - 2 / γ) α')
    (h₃ : ExtendedSeiberg3 γ (2 * Q γ - ε - 2 / γ - γ) α α')
    (hRε : AnalyticAt ℂ R (ε : ℂ)) (hRα : AnalyticAt ℂ R (α : ℂ))
    (hs₁ : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - ε - 2 / γ) α α' : ℂ))
    (hs₂ : AnalyticAt ℂ Complex.Gamma (sExp γ ε (2 * Q γ - α - 2 / γ) α' : ℂ))
    (hs₃ : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - ε - 2 / γ - γ) α α' : ℂ))
    (g₁ : AnalyticAt ℂ Complex.Gamma (dualArg₁ γ ε))
    (g₂ : AnalyticAt ℂ Complex.Gamma (dualArg₂ γ α))
    (g₃ : AnalyticAt ℂ Complex.Gamma (1 - dualArg₃ γ ε α α'))
    (g₄ : AnalyticAt ℂ Complex.Gamma (1 - dualArg₄ γ ε α α'))
    (hA : ShiftCoeffGood γ (((2 * Q γ - ε - 2 / γ : ℝ) : ℂ) - γ / 2) α α') :
    R ε * (-(1 / (Real.pi * μ)) *
        shiftCoeffA γ (γ / 2) (((2 * Q γ - ε - 2 / γ : ℝ) : ℂ) - γ / 2) α α' *
          (structureConstant P M γ μ (2 * Q γ - ε - 2 / γ - γ) α α' : ℂ)) =
      dualLC γ ε α α' * R α * (structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α' : ℂ) := by
  rw [← firstShift_full P X M hγ hγ2 hμ hX hM hShiftGluing h₁ h₃ hs₁ hs₃ hA]
  exact seed_full P X M hγ hγ2 hμ hX hM hSeed hhR hRm hBR hRv h₁ h₂ hRε hRα hs₁ hs₂ g₁ g₂ g₃ g₄

/-- **The shifted second dual seed near a good point of a continuous curve.** -/
theorem starG_eventually {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hSeed : SeedHyp P X M γ μ)
    (hShiftGluing : ShiftGluingHyp P X M γ μ)
    {hR : ℝ} (hhR : 0 < hR) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR))
    {BR : ℝ → Ω → BrownianPath × BrownianPath} {ZR : Ω → Measure ℝ}
    (hBR : ReflectionDataFamily P γ BR ZR)
    (hRv : ReflectionFamily P γ μ R BR ZR)
    {f₁ f₂ f₃ : ℝ → ℝ} (hc₁ : Continuous f₁) (hc₂ : Continuous f₂) (hc₃ : Continuous f₃)
    {t₀ : ℝ} (h₁ : ExtendedSeiberg3 γ (2 * Q γ - f₁ t₀ - 2 / γ) (f₂ t₀) (f₃ t₀))
    (h₂ : ExtendedSeiberg3 γ (f₁ t₀) (2 * Q γ - f₂ t₀ - 2 / γ) (f₃ t₀))
    (h₃ : ExtendedSeiberg3 γ (2 * Q γ - f₁ t₀ - 2 / γ - γ) (f₂ t₀) (f₃ t₀))
    (hRε : AnalyticAt ℂ R (f₁ t₀ : ℂ)) (hRα : AnalyticAt ℂ R (f₂ t₀ : ℂ))
    (hs₁ : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - f₁ t₀ - 2 / γ) (f₂ t₀) (f₃ t₀) : ℂ))
    (hs₂ : AnalyticAt ℂ Complex.Gamma (sExp γ (f₁ t₀) (2 * Q γ - f₂ t₀ - 2 / γ) (f₃ t₀) : ℂ))
    (hs₃ : AnalyticAt ℂ Complex.Gamma
      (sExp γ (2 * Q γ - f₁ t₀ - 2 / γ - γ) (f₂ t₀) (f₃ t₀) : ℂ))
    (g₁ : AnalyticAt ℂ Complex.Gamma (dualArg₁ γ (f₁ t₀)))
    (g₂ : AnalyticAt ℂ Complex.Gamma (dualArg₂ γ (f₂ t₀)))
    (g₃ : AnalyticAt ℂ Complex.Gamma (1 - dualArg₃ γ (f₁ t₀) (f₂ t₀) (f₃ t₀)))
    (g₄ : AnalyticAt ℂ Complex.Gamma (1 - dualArg₄ γ (f₁ t₀) (f₂ t₀) (f₃ t₀)))
    (hA : ShiftCoeffGood γ (((2 * Q γ - f₁ t₀ - 2 / γ : ℝ) : ℂ) - γ / 2) (f₂ t₀) (f₃ t₀)) :
    ∀ᶠ t in 𝓝 t₀, R (f₁ t) * (-(1 / (Real.pi * μ)) *
        shiftCoeffA γ (γ / 2) (((2 * Q γ - f₁ t - 2 / γ : ℝ) : ℂ) - γ / 2) (f₂ t) (f₃ t) *
          (structureConstant P M γ μ (2 * Q γ - f₁ t - 2 / γ - γ) (f₂ t) (f₃ t) : ℂ)) =
      dualLC γ (f₁ t) (f₂ t) (f₃ t) * R (f₂ t) *
        (structureConstant P M γ μ (f₁ t) (2 * Q γ - f₂ t - 2 / γ) (f₃ t) : ℂ) := by
  filter_upwards [
    eventually_extendedSeiberg3 (f₁ := fun t => 2 * Q γ - f₁ t - 2 / γ)
      (by fun_prop) hc₂.continuousAt hc₃.continuousAt h₁,
    eventually_extendedSeiberg3 (f₂ := fun t => 2 * Q γ - f₂ t - 2 / γ)
      hc₁.continuousAt (by fun_prop) hc₃.continuousAt h₂,
    eventually_extendedSeiberg3 (f₁ := fun t => 2 * Q γ - f₁ t - 2 / γ - γ)
      (by fun_prop) hc₂.continuousAt hc₃.continuousAt h₃,
    eventually_analyticAt_comp (φ := fun t => (f₁ t : ℂ)) (by fun_prop) hRε,
    eventually_analyticAt_comp (φ := fun t => (f₂ t : ℂ)) (by fun_prop) hRα,
    eventually_analyticAt_comp
      (φ := fun t => (sExp γ (2 * Q γ - f₁ t - 2 / γ) (f₂ t) (f₃ t) : ℂ))
      (by unfold sExp; fun_prop) hs₁,
    eventually_analyticAt_comp
      (φ := fun t => (sExp γ (f₁ t) (2 * Q γ - f₂ t - 2 / γ) (f₃ t) : ℂ))
      (by unfold sExp; fun_prop) hs₂,
    eventually_analyticAt_comp
      (φ := fun t => (sExp γ (2 * Q γ - f₁ t - 2 / γ - γ) (f₂ t) (f₃ t) : ℂ))
      (by unfold sExp; fun_prop) hs₃,
    eventually_analyticAt_comp (φ := fun t => dualArg₁ γ (f₁ t))
      (by unfold dualArg₁; fun_prop) g₁,
    eventually_analyticAt_comp (φ := fun t => dualArg₂ γ (f₂ t))
      (by unfold dualArg₂; fun_prop) g₂,
    eventually_analyticAt_comp (φ := fun t => 1 - dualArg₃ γ (f₁ t) (f₂ t) (f₃ t))
      (by unfold dualArg₃; fun_prop) g₃,
    eventually_analyticAt_comp (φ := fun t => 1 - dualArg₄ γ (f₁ t) (f₂ t) (f₃ t))
      (by unfold dualArg₄; fun_prop) g₄,
    eventually_shiftCoeffGood (f₁ := fun t => ((2 * Q γ - f₁ t - 2 / γ : ℝ) : ℂ) - γ / 2)
      (f₂ := fun t => (f₂ t : ℂ)) (f₃ := fun t => (f₃ t : ℂ)) (by fun_prop) (by fun_prop)
      (by fun_prop) hA]
    with t a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃
  exact starG_point P X M hγ hγ2 hμ hX hM hSeed hShiftGluing hhR hRm hBR hRv a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉
    a₁₀ a₁₁ a₁₂ a₁₃

end DOZZ.Proofs

end
