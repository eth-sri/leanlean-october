/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import DOZZ.FourPoint.Dual.FullFusion

public import DOZZ.Statements.FourPoint.FourPointT
public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
public import DOZZ.Statements.Hypergeom.GaussFMinus
public import DOZZ.Statements.Hypergeom.GaussFPlus
public import DOZZ.Statements.Hypergeom.GaussCutPlane
public import DOZZ.Statements.Hypergeom.GaussParameterA
public import DOZZ.Statements.Hypergeom.GaussParameterB
public import DOZZ.Statements.Hypergeom.GaussParameterC
public import DOZZ.Statements.Hypergeom.IsGaussHypergeometricFamily
public import DOZZ.FourPoint.Crossing.Reflection
import DOZZ.ShiftEquations.Gluing.DiagonalUnique
import DOZZ.FourPoint.Diagonal.Assembly
import DOZZ.FourPoint.Dual.Parameters
import DOZZ.Hypergeom.ODE.SlitPlaneGluing
import DOZZ.Brownian.Reflection.WitnessIndependence

/-!
# The dual reflection identity near `Q`

Two ingredients of the dual crossing seeds.

* **Crossing symmetry.** The reduced four-point function with the dual degenerate charge `-2/γ` is
  symmetric under `z ↦ 1 - z` with the two finite charges exchanged. This is the affine moment
  identity with a charge at infinity, exactly as for the half charge
  (`fourPointT_reflection`).
* **The reflection identity near `Q`.** By the diagonal classification at `χ = 2/γ`, the four-point
  function is `C(α₁ - 2/γ, α₂, α₃) (|F₋|² + r |F₊|²)` with `r` the ratio of [KRV, (Fundrelation)].
  When `α₁` is close to `Q`, the dual fusion (`dual_full_fusion_and_asymptotic`, second conjunct)
  writes it as `C(α₁ - 2/γ, α₂, α₃) |F₋|² + R(α₁) C(2Q - α₁ - 2/γ, α₂, α₃) |F₊|²`. Uniqueness of
  diagonal coefficients in the Gauss basis at zero gives
  `C(α₁ - 2/γ, α₂, α₃) r = R(α₁) C(2Q - α₁ - 2/γ, α₂, α₃)`.

The fusion applies with `η = 2(Q - α₁)` and `ξ = 1/2` as soon as `Q - α₁ < (4 - γ²) γ / 64`
(`dualSeedWindow`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

universe u

namespace DOZZ.Proofs

/-! ### Crossing symmetry of the dual four-point function -/

/-! ### The near-`Q` window of the dual fusion -/

/-- The width of the near-`Q` window in which the dual fusion applies with `η = 2(Q - α₁)` and
`ξ = 1/2`. -/
noncomputable def dualSeedWindow (γ : ℝ) : ℝ := (4 - γ ^ 2) * γ / 64

theorem dualSeedWindow_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 < dualSeedWindow γ := by
  unfold dualSeedWindow
  have h4 : 0 < 4 - γ ^ 2 := by nlinarith
  positivity

/-- The polynomial core of the second slack condition, over abstract reals. -/
theorem dualSeedWindow_slack_core {γ d : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hd : 0 < d)
    (hdw : d < (4 - γ ^ 2) * γ / 64) :
    4 * d < (2 - γ ^ 2 / 2 - 3 * γ * d) / 2 * γ := by
  have hγsq : γ ^ 2 < 4 := by nlinarith
  have h1 : γ ^ 2 * d < 4 * d := mul_lt_mul_of_pos_right hγsq hd
  have h2 : 64 * d < (4 - γ ^ 2) * γ := by linarith
  have hexp : (2 - γ ^ 2 / 2 - 3 * γ * d) / 2 * γ = (4 - γ ^ 2) * γ / 4 - 3 / 2 * (γ ^ 2 * d) := by
    ring
  rw [hexp]
  linarith

/-- **The window.** If `0 < Q - α₁ < (4 - γ²) γ / 64`, then `η = 2(Q - α₁)` and `ξ = 1/2` satisfy
every window hypothesis of the dual fusion. -/
theorem dual_fusion_window {γ α₁ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα₁ : α₁ < Q γ)
    (hnear : Q γ - α₁ < dualSeedWindow γ) :
    0 < 2 * (Q γ - α₁) ∧ 2 * (Q γ - α₁) < γ / 2 ∧ Q γ - 2 * (Q γ - α₁) < α₁ ∧
      (4 / γ) * (Q γ - α₁) < 1 / 2 ∧
      (4 / γ) * (Q γ - α₁) < (1 - 1 / 2) * (4 - γ * α₁ - 2 * γ * (2 * (Q γ - α₁))) := by
  set d := Q γ - α₁ with hd_def
  have hd : 0 < d := sub_pos.mpr hα₁
  have hdw : d < (4 - γ ^ 2) * γ / 64 := hnear
  have hγsq : γ ^ 2 < 4 := by nlinarith
  have hd16 : d < γ / 16 := by
    have : (4 - γ ^ 2) * γ / 64 < 4 * γ / 64 := by
      have h4 : 4 - γ ^ 2 < 4 := by nlinarith
      have := mul_lt_mul_of_pos_right h4 hγ
      linarith
    linarith
  have hγQ : γ * Q γ = γ ^ 2 / 2 + 2 := by
    unfold Q
    field_simp
    ring
  have hα₁d : α₁ = Q γ - d := by rw [hd_def]; ring
  refine ⟨by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hγ]
    linarith
  · have hcore := dualSeedWindow_slack_core hγ hγ2 hd hdw
    have hrhs : (1 - 1 / 2) * (4 - γ * α₁ - 2 * γ * (2 * d)) =
        (2 - γ ^ 2 / 2 - 3 * γ * d) / 2 := by
      rw [hα₁d]
      linear_combination (-1 / 2 : ℝ) * hγQ
    rw [hrhs, div_mul_eq_mul_div, div_lt_iff₀ hγ]
    linarith

/-! ### The reflection identity near `Q` -/

/-- A Gauss parameter strictly between two consecutive integers is not an integer. -/
theorem seeds_ne_int_of_mem_Ioo {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    ∀ n : ℤ, (c : ℂ) ≠ (n : ℂ) := by
  intro n hn
  have hn' : c = (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (hn' ▸ h0)
  have hn1 : n < (1 : ℤ) := by exact_mod_cast (hn' ▸ h1)
  omega

/-- **The dual reflection identity near `Q`.** For `α₁` within `dualSeedWindow γ` of `Q`, the second
diagonal coefficient of the classified dual four-point function is the reflection coefficient times
the reflected structure constant, for every witness of `R(α₁)`. -/
theorem dual_reflection_identity_near_Q
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)
    (γ μ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ < Q γ) (hnear : Q γ - α₁ < dualSeedWindow γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : IsReflectionData P γ α₁ B Z) :
    structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
        gaussCoefficientRatio (gaussParameterA γ (2 / γ) α₁ α₂ α₃)
          (gaussParameterB γ (2 / γ) α₁ α₂ α₃) (gaussParameterC γ (2 / γ) α₁) =
      reflectionR P γ μ α₁ B Z * structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ := by
  obtain ⟨H, hH⟩ := gauss_hypergeometric_exists
  obtain ⟨hη0, hη1, hηlo, hslack₁, hslack₂⟩ := dual_fusion_window hγ hγ2 hα₁ hnear
  obtain ⟨B', Z', -, hB', hrest⟩ := dual_full_fusion_and_asymptotic hH P M X γ μ α₁ α₂ α₃ (2 * (Q γ - α₁)) (1 / 2)
    hγ hγ2 hμ hη0 hη1 (by norm_num) (by norm_num) hηlo hα₁ hα₂ hα₃ hs hslack₁ hslack₂ hX hM
  have hformula := hrest.2
  have hclass := degenerateFourPoint_diagonal_classification hH P X M γ μ (2 / γ) α₁ α₂ α₃
    hγ hγ2 hμ (Or.inr rfl) hα₁ hα₂ hα₃ hs hX hM
  obtain ⟨-, -, -, -, hC0, hC1, -⟩ :=
    dual_seed_parameter_intervals γ α₁ α₂ α₃ hγ hγ2 hα₁ hα₂ hα₃ hs
  have huniq := diagonal_gauss_coefficients_unique hH (seeds_ne_int_of_mem_Ioo hC0 hC1)
    (T := fun z => fourPointT P M γ μ (-(2 / γ)) α₁ α₂ α₃ z)
    (A₁ := structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃)
    (D₁ := structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
      gaussCoefficientRatio (gaussParameterA γ (2 / γ) α₁ α₂ α₃)
        (gaussParameterB γ (2 / γ) α₁ α₂ α₃) (gaussParameterC γ (2 / γ) α₁))
    (A₂ := structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃)
    (D₂ := reflectionR P γ μ α₁ (B' α₁) Z' *
      structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃)
    (fun z hz => by
      rw [hclass z hz]
      ring)
    (fun z hz => by
      have h := hformula z hz
      rw [neg_div] at h
      rw [h])
  rw [huniq.2, reflectionR_eq_of_isReflectionData P P γ μ α₁ (B' α₁) Z' B Z hB' hB]

end DOZZ.Proofs

end
