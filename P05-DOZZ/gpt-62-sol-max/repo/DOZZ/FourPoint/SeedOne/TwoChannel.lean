/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.CoefficientExtraction
public import DOZZ.FourPoint.Crossing.DiagonalUniqueness
public import DOZZ.FourPoint.Diagonal.Assembly
public import DOZZ.ShiftEquations.Shifts.Seeds.Reflection
public import DOZZ.Hypergeom.ClassificationDiagonalConnection
public import DOZZ.Hypergeom.ConnectionDiagonalCoefficients
public import DOZZ.Hypergeom.BasisRegularity
public import DOZZ.Statements.FourPoint.DualCrossingMultiplier
public import DOZZ.Hypergeom.PhysicalRange
public import DOZZ.Statements.Hypergeom.GaussGPlus
public import DOZZ.Statements.Hypergeom.GaussGMinus
import DOZZ.ShiftEquations.Rbar.Multiplier
import DOZZ.Hypergeom.ODE.SlitPlaneGluing
import Mathlib.Tactic

/-!
# The two channels of the dual degenerate four-point function

For charges `α, ε, α' < Q` with `α + ε + α' > 2Q + 2/γ`, the reduced four-point function with
the `-2/γ` insertion is diagonal in the basis at `0` (the classification
`DOZZ.degenerateFourPoint_diagonal_classification` at `χ = 2/γ` for `(α, ε, α')`) and, through the
exchange `z ↦ 1 - z` of its first two charges (`fourPointT_reflection`), diagonal in the basis
at `1` (the same classification for `(ε, α, α')`). The connection matrix between the two bases
then fixes the four coefficients against each other; in particular the first zero-channel
coefficient `C(α - 2/γ, ε, α')` is the dual crossing multiplier times the second one-channel
coefficient `C(ε - 2/γ, α, α') ρ(ε, α, α')` ([KRV, Propositions 9.9 and 9.10], which proceed
along the same lines as [KRV, Proposition 9.8]).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The dual Gauss parameters are symmetric in the first two charges, and the one-channel
parameter is `1 + a + b - c`. -/
theorem dual_channel_parameters (γ α ε α' : ℝ) (hγ : γ ≠ 0) :
    gaussParameterA γ (2 / γ) ε α α' = gaussParameterA γ (2 / γ) α ε α' ∧
      gaussParameterB γ (2 / γ) ε α α' = gaussParameterB γ (2 / γ) α ε α' ∧
      gaussParameterC γ (2 / γ) ε = 1 + gaussParameterA γ (2 / γ) α ε α' +
        gaussParameterB γ (2 / γ) α ε α' - gaussParameterC γ (2 / γ) α := by
  refine ⟨?_, ?_, ?_⟩
  · unfold gaussParameterA
    ring
  · unfold gaussParameterB
    ring
  · unfold gaussParameterA gaussParameterB gaussParameterC Q
    field_simp
    ring

/-- **The one-channel form**: the classification for `(ε, α, α')`, read through `z ↦ 1 - z`, is a
diagonal form of the four-point function of `(α, ε, α')` in the basis at `1`. -/
theorem dual_one_channel_of_classification {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α')
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-(2 / γ)) α ε α' z =
      structureConstant P M γ μ (ε - 2 / γ) α α' *
          ‖gaussGMinus H (gaussParameterA γ (2 / γ) α ε α') (gaussParameterB γ (2 / γ) α ε α')
            (gaussParameterC γ (2 / γ) α) z‖ ^ 2 +
        structureConstant P M γ μ (ε - 2 / γ) α α' *
          gaussCoefficientRatio (gaussParameterA γ (2 / γ) ε α α')
            (gaussParameterB γ (2 / γ) ε α α') (gaussParameterC γ (2 / γ) ε) *
          ‖gaussGPlus H (gaussParameterA γ (2 / γ) α ε α') (gaussParameterB γ (2 / γ) α ε α')
            (gaussParameterC γ (2 / γ) α) z‖ ^ 2 := by
  obtain ⟨hA, hB, hC⟩ := dual_channel_parameters γ α ε α' hγ.ne'
  have h22 := degenerateFourPoint_diagonal_classification hH P X M γ μ (2 / γ) ε α α' hγ hγ2 hμ
    (Or.inr rfl) hε hα hα' (by linarith) hX hM
  intro z hz
  rw [fourPointT_reflection P X M γ μ (-(2 / γ)) α ε α' hγ hγ2 hX hM z]
  have h := h22 (1 - z) (one_sub_gaussCutPlane_subset_gaussCutPlane hz)
  rw [h, hA, hB]
  have hCC : (gaussParameterC γ (2 / γ) ε : ℂ) =
      1 + (gaussParameterA γ (2 / γ) α ε α' : ℂ) + (gaussParameterB γ (2 / γ) α ε α' : ℂ) -
        (gaussParameterC γ (2 / γ) α : ℂ) := by
    exact_mod_cast hC
  unfold gaussFMinus gaussFPlus gaussGMinus gaussGPlus
  rw [hCC]
  have hpow (A B C : ℂ) : 1 - (1 + A + B - C) = C - A - B := by ring
  have hplusA (A B C : ℂ) : A - (1 + A + B - C) + 1 = C - B := by ring
  have hplusB (A B C : ℂ) : B - (1 + A + B - C) + 1 = C - A := by ring
  have hplusC (A B C : ℂ) : 2 - (1 + A + B - C) = 1 + C - A - B := by ring
  rw [hpow, hplusA, hplusB, hplusC]
  ring

/-- **The two dual channels** (shared by both seeds). At a point of the seed domain, with `a, b, c`
the dual Gauss parameters of `(α, ε, α')`, `d₀ = C(α - 2/γ, ε, α')`, `d₁ = d₀ r(a, b, c)`,
`e₀ = C(ε - 2/γ, α, α')` and `e₁ = e₀ r'` (`r'` the ratio of [KRV, (Fundrelation)] for
`(ε, α, α')`): the mixed term of the transformed diagonal form vanishes and its two diagonal entries
are `e₀` and `e₁`. -/
theorem dual_two_channel_extraction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α')
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    let a := gaussParameterA γ (2 / γ) α ε α'
    let b := gaussParameterB γ (2 / γ) α ε α'
    let c := gaussParameterC γ (2 / γ) α
    let d₀ := structureConstant P M γ μ (α - 2 / γ) ε α'
    let d₁ := d₀ * gaussCoefficientRatio a b c
    let e₀ := structureConstant P M γ μ (ε - 2 / γ) α α'
    let e₁ := e₀ * gaussCoefficientRatio (gaussParameterA γ (2 / γ) ε α α')
      (gaussParameterB γ (2 / γ) ε α α') (gaussParameterC γ (2 / γ) ε)
    d₀ * gaussConnectionReal₁₁ a b c * gaussConnectionReal₁₂ a b c + d₁ * gaussConnectionReal₂₁ a b c * gaussConnectionReal₂₂ a b c = 0 ∧
      e₀ = d₀ * gaussConnectionReal₁₁ a b c ^ 2 + d₁ * gaussConnectionReal₂₁ a b c ^ 2 ∧
      e₁ = d₀ * gaussConnectionReal₁₂ a b c ^ 2 + d₁ * gaussConnectionReal₂₂ a b c ^ 2 := by
  intro a b c d₀ d₁ e₀ e₁
  obtain ⟨H, hH⟩ := gauss_hypergeometric_exists
  obtain ⟨ha, hab, hbc, hc1, hδ, hδ1, -, hK₂⟩ :=
    gauss_physical_parameter_range γ (2 / γ) α ε α' hγ hγ2 (Or.inr rfl) hs hα hε hα'
  exact crossing_diagonal_transfer hH a b c d₀ e₀ e₁
    (unit_interval_ne_int (ha.trans (hab.trans hbc)) hc1) (unit_interval_ne_int hδ hδ1) hK₂.ne'
    (degenerateFourPoint_diagonal_classification hH P X M γ μ (2 / γ) α ε α' hγ hγ2 hμ
      (Or.inr rfl) hα hε hα' hs hX hM)
    (dual_one_channel_of_classification hH P X M γ μ α ε α' hγ hγ2 hμ hα hε hα' hs hX hM)

/-- **The first zero-channel coefficient from the second one-channel coefficient**:
`C(α - 2/γ, ε, α') = dualCrossingMultiplier(α', α, ε) · C(ε - 2/γ, α, α') ρ(ε, α, α')`, on the whole
seed domain, from the classification alone. -/
theorem dual_first_coefficient_of_classification {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α')
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    structureConstant P M γ μ (α - 2 / γ) ε α' =
      dualCrossingMultiplier γ α' α ε *
        (structureConstant P M γ μ (ε - 2 / γ) α α' *
          gaussCoefficientRatio (gaussParameterA γ (2 / γ) ε α α')
            (gaussParameterB γ (2 / γ) ε α α') (gaussParameterC γ (2 / γ) ε)) := by
  let a := gaussParameterA γ (2 / γ) α ε α'
  let b := gaussParameterB γ (2 / γ) α ε α'
  let c := gaussParameterC γ (2 / γ) α
  obtain ⟨ha, hab, hbc, hc1, hδ, hδ1, -, -⟩ :=
    gauss_physical_parameter_range γ (2 / γ) α ε α' hγ hγ2 (Or.inr rfl) hs hα hε hα'
  obtain ⟨hcross, -, hE⟩ := dual_two_channel_extraction P X M γ μ α ε α' hγ hγ2 hμ hα hε hα' hs hX hM
  have hex := crossing_diagonal_coefficient_extraction a b c _ _ _ ha hab hbc hc1 hδ hδ1 hcross hE
  have hM' : lR a * lR b / (lR c * lR (a + b - c)) = dualCrossingMultiplier γ α' α ε := by
    unfold dualCrossingMultiplier
    simp only [lFun_ofReal_re_eq_lR]
    rfl
  simpa only [hM'] using hex

end DOZZ.Proofs

end
