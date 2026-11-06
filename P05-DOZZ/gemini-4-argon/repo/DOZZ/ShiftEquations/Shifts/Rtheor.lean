/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Reflection.RtheorIdentification
public import DOZZ.Statements.FourPoint.DualCrossingL
import DOZZ.Brownian.Reflection.WitnessIndependence
import DOZZ.Brownian.Reflection.MomentAssembly
import DOZZ.FourPoint.Crossing.GammaHalfCrossing
import DOZZ.ShiftEquations.Shift.Wrappers
import DOZZ.ShiftEquations.DualR.Wrapper

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

theorem reflection_Rtheor_off_poles_of_seedTwo
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X (M : Ω → Measure ℂ)
    (hseedTwo : ∀
    (γ μ α ε α' : ℝ)
    (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
    (_hα : α < Q γ) (_hε : ε < Q γ) (_hα' : α' < Q γ)
    (_hs : 2 * Q γ + 2 / γ < α + ε + α')
    (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
    ∃ Bε Bα : Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ ε Bε Z ∧
        IsReflectionData P γ α Bα Z ∧
        reflectionR P γ μ ε Bε Z *
            structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
          dualCrossingL γ ε α α' *
            reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α')
    (γ μ α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ) := by
  have hCross := fun μ' α' ε α hμ' h1 h2 h3 h4 h5 =>
    (gammaHalf_crossing P X M γ μ' α' ε α hγ hγ2 hμ' h1 h2 h3 h4 h5 hX hM).2
  obtain ⟨B₀, Z₀, -, hD₀, V, -, hVI, f, -, -, hgf, hgcoef⟩ :=
    reflectionBarR_holomorphic_representation_of_crossing P X M γ hγ hγ2 hX hM hCross
      (Ioo (γ / 2) (Q γ)) (fun _ h => h)
  have hD₀' : ∀ b : ℝ, γ / 2 < b → b < Q γ → IsReflectionData P γ b (B₀ b) Z₀ :=
    fun b h1 h2 => hD₀ b ⟨h1, h2⟩
  rw [reflectionR_eq_of_isReflectionData P P γ μ α B Z (B₀ α) Z₀ hData (hD₀' α hα.1 hα.2)]
  obtain ⟨B₁, Z₁, -, hD₁, h₁, hh₁, R₁, hR₁, hR₁α, hshift₁⟩ :=
    reflectionR_first_shift_meromorphic_of_crossing P X M γ μ hγ hγ2 hμ hX hM hCross
  obtain ⟨B₂, Z₂, -, hD₂, h₂, hh₂, R₂, hR₂, hR₂α, c, -, -, hshift₂⟩ :=
    reflectionR_dual_shift_unknown_constant_of_crossing_seed P X M γ μ hγ hγ2 hγirr hμ hX hM hCross
      fun a e a' h1 h2 h3 h4 => hseedTwo γ μ a e a' hγ hγ2 hμ h1 h2 h3 h4 hX hM
  have hR₁' : ∀ b : ℝ, γ / 2 < b → b < Q γ → R₁ (b : ℂ) = (reflectionR P γ μ b (B₀ b) Z₀ : ℂ) :=
    fun b h1 h2 => by
      rw [hR₁α b h1 h2, reflectionR_eq_of_isReflectionData P P γ μ b (B₁ b) Z₁ (B₀ b) Z₀
        (hD₁ b h1 h2) (hD₀' b h1 h2)]
  have hR₂' : ∀ b : ℝ, γ / 2 < b → b < Q γ → R₂ (b : ℂ) = (reflectionR P γ μ b (B₀ b) Z₀ : ℂ) :=
    fun b h1 h2 => by
      rw [hR₂α b h1 h2, reflectionR_eq_of_isReflectionData P P γ μ b (B₂ b) Z₂ (B₀ b) Z₀
        (hD₂ b h1 h2) (hD₀' b h1 h2)]
  have hBar := (Complex.continuous_re.comp_continuousOn (hgf.continuousOn.comp
      Complex.continuous_ofReal.continuousOn hVI)).congr fun b hb => by
        simpa using congrArg Complex.re (hgcoef b hb).symm
  exact reflectionR_eq_reflectionDOZZ_of_shifts P γ μ hγ hγ2 hγirr hμ B₀ Z₀ hD₀' hh₁ hh₂
    hR₁ hR₂ hR₁' hR₂' hshift₁ hshift₂ hBar (reflectionR_tendsto_Q P γ μ hγ hγ2 hμ B₀ Z₀ hD₀')
    hα hPole

end DOZZ.Proofs

end
