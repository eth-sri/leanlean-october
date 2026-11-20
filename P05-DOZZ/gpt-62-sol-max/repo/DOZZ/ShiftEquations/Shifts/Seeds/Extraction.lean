/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shifts.Seeds.Continuation
public import DOZZ.Statements.FourPoint.DualCrossingL
public import DOZZ.Statements.Hypergeom.GaussGMinus
public import DOZZ.Statements.Hypergeom.GaussGPlus
public import DOZZ.ShiftEquations.Rbar.Multiplier
import DOZZ.FourPoint.Crossing.ConnectionDet
import DOZZ.FourPoint.Crossing.DiagonalUniqueness
import DOZZ.FourPoint.Dual.ConnectionAlgebra
import DOZZ.FourPoint.Dual.GammaRatios
import DOZZ.FourPoint.Dual.Domain
import DOZZ.Correlations.Residue.FullFromUnit
import DOZZ.Correlations.Symmetry.SymmetricExtended
import DOZZ.Hypergeom.ConnectionDiagonalCoefficients
import DOZZ.Hypergeom.ClassificationDiagonalConnection
import DOZZ.Hypergeom.BasisRegularity
import DOZZ.Hypergeom.ODE.SlitPlaneGluing
import DOZZ.Hypergeom.PhysicalRange
import DOZZ.FourPoint.Diagonal.Assembly
import DOZZ.FourPoint.Dual.Parameters
public import DOZZ.FourPoint.SeedOne.TwoChannel

/-!
# The two dual channels and the second dual crossing seed

Fix a point `(α, ε, α')` of the seed domain `α, ε, α' < Q`, `α + ε + α' > 2Q + 2/γ`, and let
`a, b, c` be the dual Gauss parameters of `(α, ε, α')`.

* **Two channels.** The diagonal classification at `χ = 2/γ` gives the four-point function of
  `(α, ε, α')` as `d₀ (|F₋|² + r |F₊|²)` with `d₀ = C(α - 2/γ, ε, α')`, and that of `(ε, α, α')` as
  `e₀ (|F'₋|² + r' |F'₊|²)` with `e₀ = C(ε - 2/γ, α, α')`. The crossing symmetry `z ↦ 1 - z` and the
  channel relation `c' = 1 + a + b - c` turn the second into the basis at one of the first. The
  single-valuedness constraint `K₁ d₀ + K₂ d₀ r = 0` transfers the first to the same basis through
  the connection matrix `(u v; w x)`, and uniqueness of coefficients gives `e₀ = d₀ u² + d₁ w²` and
  `e₁ = d₀ v² + d₁ x²` (`dual_two_channel_extraction`, shared by both seeds).
* **The reflection identity on the whole domain** (`dual_reflection_identity_of_fusion`): near `Q`
  from the dual fusion statement `dual_full_fusion_and_asymptotic`, then continued in the first
  charge.
* **The second seed.** `e₁ = d₀ v² + d₁ x² = d₁ x det / u`, the Gamma recurrences turn `x det / u`
  into `dualCrossingL`, and the reflection identity at the two first charges `ε` and `α` identifies
  `e₁ = R(ε) C(2Q - ε - 2/γ, α, α')` and `d₁ = R(α) C(2Q - α - 2/γ, ε, α')`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

universe u

namespace DOZZ.Proofs

/-! ### The reflection identity on the whole seed domain -/

/-- **The dual reflection identity on the whole seed domain**, for every witness of `R(α₁)`, from
the complete statement of `dual_full_fusion_and_asymptotic` at universe `u`: near `Q` by the fusion
and the classification, then continued in the first charge. -/
theorem dual_reflection_identity_of_fusion
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)
    (γ μ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : IsReflectionData P γ α₁ B Z) :
    structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
        gaussCoefficientRatio (gaussParameterA γ (2 / γ) α₁ α₂ α₃)
          (gaussParameterB γ (2 / γ) α₁ α₂ α₃) (gaussParameterC γ (2 / γ) α₁) =
      reflectionR P γ μ α₁ B Z * structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ :=
  dual_reflection_identity_continuation P X M γ μ α₂ α₃ hγ hγ2 hμ hα₂ hα₃ hX hM
    (fun β h1 h2 h3 B' Z' hB' => dual_reflection_identity_near_Q P X M γ μ β α₂ α₃ hγ hγ2 hμ
      h1 h2 hα₂ hα₃ h3 hX hM B' Z' hB')
    α₁ hα₁ hs B Z hB

/-! ### The second seed -/

/-- **The second dual multiplier.** On the seed domain, `x det / u` is `dualCrossingL`
(`C₁ = 1 - δ`). -/
theorem dual_seed_two_multiplier (γ α ε α' : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α') :
    let a := gaussParameterA γ (2 / γ) α ε α'
    let b := gaussParameterB γ (2 / γ) α ε α'
    let c := gaussParameterC γ (2 / γ) α
    gaussConnectionReal₂₂ a b c * (gaussConnectionReal₁₁ a b c * gaussConnectionReal₂₂ a b c - gaussConnectionReal₁₂ a b c * gaussConnectionReal₂₁ a b c) /
        gaussConnectionReal₁₁ a b c = dualCrossingL γ ε α α' := by
  intro a b c
  obtain ⟨ha, hab, hbc, hc1, hδ, hδ1, -⟩ :=
    gauss_physical_parameter_range γ (2 / γ) α ε α' hγ hγ2 (Or.inr rfl) hs hα hε hα'
  have hc : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hcn : ∀ n : ℤ, c ≠ (n : ℝ) := fun n hn => by
    have h := seeds_ne_int_of_mem_Ioo hc hc1 n
    exact h (by exact_mod_cast hn)
  have hδn : ∀ n : ℤ, c - a - b ≠ (n : ℝ) := fun n hn => by
    have h := seeds_ne_int_of_mem_Ioo hδ hδ1 n
    exact h (by exact_mod_cast hn)
  have hdet : gaussConnectionReal₁₁ a b c * gaussConnectionReal₂₂ a b c - gaussConnectionReal₁₂ a b c * gaussConnectionReal₂₁ a b c =
      (c - 1) / (c - a - b) := crossing_connection_det_real a b c hcn hδn
  -- the Gamma values in `u` and `x`
  have hGc : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
  have hGδ : Real.Gamma (c - a - b) ≠ 0 := (Real.Gamma_pos_of_pos hδ).ne'
  have hGca : Real.Gamma (c - a) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hGcb : Real.Gamma (c - b) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hGac : Real.Gamma (a - c + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hGbc : Real.Gamma (b - c + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hG2c : Real.Gamma (2 - c) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hu : gaussConnectionReal₁₁ a b c ≠ 0 := by
    unfold gaussConnectionReal₁₁
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hGc hGδ) (inv_ne_zero hGca)) (inv_ne_zero hGcb)
  -- `x det / u` in the form of the Gamma recurrence
  have hxu : gaussConnectionReal₂₂ a b c * ((c - 1) / (c - a - b)) / gaussConnectionReal₁₁ a b c =
      ((c - 1) / (c - a - b)) * (Real.Gamma (2 - c) / Real.Gamma c) *
        (Real.Gamma (-(c - a - b)) / Real.Gamma (c - a - b)) * lR (c - a) * lR (c - b) := by
    unfold gaussConnectionReal₂₂ gaussConnectionReal₁₁ lR
    rw [show 1 - (c - a) = a - c + 1 by ring, show 1 - (c - b) = b - c + 1 by ring,
      show -(c - a - b) = a + b - c by ring]
    field_simp
  rw [hdet, hxu, dual_connection_second_multiplier a b c (c - a - b) hc hc1 hδ hδ1]
  -- `dualCrossingL`, with `C₁ = 1 + a + b - c`
  have hC := dual_seed_channel_parameter γ α ε α' hγ.ne'
  unfold dualCrossingL
  simp only [lFun_ofReal_re_eq_lR]
  rw [hC]
  have e1 : 1 - (c - a - b) - 1 = -(c - a - b) := by ring
  have e2 : 1 - (c - a - b) - a - b + 1 = 2 - c := by ring
  have e3 : 1 - (c - a - b) - a = 1 - c + b := by ring
  have e4 : 1 - (c - a - b) - b = 1 - c + a := by ring
  rw [e1, e2, e3, e4]

/-- **The second dual crossing identity on the whole seed domain**, given the dual reflection
identity at the first charges `α` and `ε`. -/
theorem dual_seed_two_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α')
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (Bε Bα : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hRIα : structureConstant P M γ μ (α - 2 / γ) ε α' *
        gaussCoefficientRatio (gaussParameterA γ (2 / γ) α ε α')
          (gaussParameterB γ (2 / γ) α ε α') (gaussParameterC γ (2 / γ) α) =
      reflectionR P γ μ α Bα Z * structureConstant P M γ μ (2 * Q γ - α - 2 / γ) ε α')
    (hRIε : structureConstant P M γ μ (ε - 2 / γ) α α' *
        gaussCoefficientRatio (gaussParameterA γ (2 / γ) ε α α')
          (gaussParameterB γ (2 / γ) ε α α') (gaussParameterC γ (2 / γ) ε) =
      reflectionR P γ μ ε Bε Z * structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α') :
    reflectionR P γ μ ε Bε Z *
        structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
      dualCrossingL γ ε α α' *
        reflectionR P γ μ α Bα Z *
          structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α' := by
  obtain ⟨hcross, -, hE⟩ := dual_two_channel_extraction P X M γ μ α ε α' hγ hγ2 hμ hα hε hα'
    hs hX hM
  have hL : gaussConnectionReal₂₂ (gaussParameterA γ (2 / γ) α ε α') (gaussParameterB γ (2 / γ) α ε α')
        (gaussParameterC γ (2 / γ) α) *
      (gaussConnectionReal₁₁ (gaussParameterA γ (2 / γ) α ε α') (gaussParameterB γ (2 / γ) α ε α')
          (gaussParameterC γ (2 / γ) α) *
        gaussConnectionReal₂₂ (gaussParameterA γ (2 / γ) α ε α') (gaussParameterB γ (2 / γ) α ε α')
          (gaussParameterC γ (2 / γ) α) -
        gaussConnectionReal₁₂ (gaussParameterA γ (2 / γ) α ε α') (gaussParameterB γ (2 / γ) α ε α')
          (gaussParameterC γ (2 / γ) α) *
        gaussConnectionReal₂₁ (gaussParameterA γ (2 / γ) α ε α') (gaussParameterB γ (2 / γ) α ε α')
          (gaussParameterC γ (2 / γ) α)) /
      gaussConnectionReal₁₁ (gaussParameterA γ (2 / γ) α ε α') (gaussParameterB γ (2 / γ) α ε α')
        (gaussParameterC γ (2 / γ) α) = dualCrossingL γ ε α α' :=
    dual_seed_two_multiplier γ α ε α' hγ hγ2 hα hε hα' hs
  obtain ⟨ha, hab, hbc, hc1, hδ, -⟩ :=
    gauss_physical_parameter_range γ (2 / γ) α ε α' hγ hγ2 (Or.inr rfl) hs hα hε hα'
  have hu : gaussConnectionReal₁₁ (gaussParameterA γ (2 / γ) α ε α') (gaussParameterB γ (2 / γ) α ε α')
      (gaussParameterC γ (2 / γ) α) ≠ 0 := by
    unfold gaussConnectionReal₁₁
    have hc : 0 < gaussParameterC γ (2 / γ) α := lt_trans (lt_trans ha hab) hbc
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Real.Gamma_pos_of_pos hc).ne'
      (Real.Gamma_pos_of_pos hδ).ne') (inv_ne_zero (Real.Gamma_pos_of_pos (by linarith)).ne'))
      (inv_ne_zero (Real.Gamma_pos_of_pos (by linarith)).ne')
  have h2 := dual_connection_diagonal_second_from_second _ _ _ _ _ _ hcross hu
  -- the reflected triple is symmetric in its first two charges
  have hswap := structureConstant_swap12 P X M (μ := μ) hγ hγ2 hX hM
    (seeds_reflected_triple hγ hγ2 hε hα' hα hs).2
  -- `e₁ = d₁ x det / u = L d₁`
  rw [← hRIε, hE.trans h2, ← hswap, mul_assoc (dualCrossingL γ ε α α'), ← hRIα, ← hL]
  ring

end DOZZ.Proofs

end
