/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.SegFactors
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
import DOZZ.ShiftEquations.Gluing.BandNear
import DOZZ.Brownian.Reflection.RtheorAnalytic
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.ShiftEquations.Rbar.Continuation
public import DOZZ.ShiftEquations.Representatives

/-!
# The first γ/2 structure shift on the whole two-triple extended domain

For spectators near `Q` the first structure shift `C(x) = -𝒜(x - γ/2) C(x - γ)/(πμ)` holds at exact
real points (from `DOZZ.structureConstant_reflected_shift_and_gluing`, `firstShift_exact_of_strip`).
The set of real triples `(x, b, c)` with `(x, b, c)` and `(x - γ, b, c)` both in the extended
Seiberg domain is convex, and both sides are meromorphic along its segments
(`DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain`). Continuing from the near-`Q`
box along a segment gives the shift at every real point of that set where `Γ` is analytic at both
`s`-parameters and the shift coefficient is analytic (`ShiftCoeffGood`). This is the continuation in
the spectators of the gluing lemma ([KRV, Lemma 10.5], first half).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) {γ μ : ℝ}
  (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
include Ω hγ hγ2 hμ hX hM

/-- **The first structure shift near `Q` from `DOZZ.structureConstant_reflected_shift_and_gluing`**,
at every real point of the near-`Q` box. -/
theorem firstShift_nearQ_of_reflected_shift_and_gluing {η : ℝ} (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hShiftGluing : HasShiftGluingAt P X M γ μ η)
    (y b c : ℝ) (hy₁ : 2 * η + γ < y) (hy₂ : y < Q γ) (hb₁ : Q γ - η < b) (hb₂ : b < Q γ)
    (hc₁ : Q γ - η < c) (hc₂ : c < Q γ) :
    (structureConstant P M γ μ y b c : ℂ) = -(1 / (Real.pi * μ)) *
      shiftCoeffA γ (γ / 2) ((y : ℂ) - γ / 2) b c * (structureConstant P M γ μ (y - γ) b c : ℂ) := by
  obtain ⟨V₃, f₃, hExt⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  obtain ⟨B, Z, -, -, h, hh, C, R, hCm, -, hCv, -, hglue, hrefl⟩ :=
    hShiftGluing b c ⟨hb₁, hb₂⟩ ⟨hc₁, hc₂⟩
  have hCs : StructureFirstShift γ μ b c C := by
    filter_upwards [eventually_codiscrete_comp_add hglue ((γ : ℂ) / 2), hrefl] with z h1 h2
    rw [h1, show 2 * (Q γ : ℂ) - (z + γ / 2) = 2 * Q γ - z - γ / 2 by ring, h2]
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh := half_gamma_lt_two_div hγ hγ2
  have h2γ : 0 < 2 / γ := by positivity
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  have hgood : ShiftCoeffGood γ ((y : ℂ) - γ / 2) b c :=
    shiftCoeffGood_of_lt hγ (by linarith [hη.1]) (by linarith [hη.2])
      (by linarith [hη.1, hη.2]) (by linarith [hη.1, hη.2]) (by linarith [hη.1, hη.2])
  have hAy : AnalyticAt ℂ (fun z => shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ)) ((y : ℂ) - γ / 2) :=
    analyticAt_shiftCoeffA_comp (f₁ := id) (f₂ := fun _ => (b : ℂ)) (f₃ := fun _ => (c : ℂ))
      analyticAt_id analyticAt_const analyticAt_const hgood
  exact firstShift_exact_of_strip P M hγ hγ2 hμ hη ⟨hb₁, hb₂⟩ ⟨hc₁, hc₂⟩ hExt hh
    hCm hCv hCs hy₁ hy₂ hAy

/-- **The first structure shift on the two-triple extended domain**, from
`DOZZ.structureConstant_reflected_shift_and_gluing`: at every real `(x, b, c)` with `(x, b, c)` and
`(x - γ, b, c)` in the extended Seiberg domain, `Γ` analytic at both `s`-parameters and the shift
coefficient analytic. -/
theorem firstShift_full
    (hShiftGluing : HasShiftGluing P X M γ μ)
    {x b c : ℝ} (h₁ : ExtendedSeiberg3 γ x b c) (h₂ : ExtendedSeiberg3 γ (x - γ) b c)
    (hs₁ : AnalyticAt ℂ Complex.Gamma (sExp γ x b c : ℂ))
    (hs₂ : AnalyticAt ℂ Complex.Gamma (sExp γ (x - γ) b c : ℂ))
    (hA : ShiftCoeffGood γ ((x : ℂ) - γ / 2) b c) :
    (structureConstant P M γ μ x b c : ℂ) = -(1 / (Real.pi * μ)) *
      shiftCoeffA γ (γ / 2) ((x : ℂ) - γ / 2) b c * (structureConstant P M γ μ (x - γ) b c : ℂ) := by
  obtain ⟨V₃, f₃, hExt⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh := half_gamma_lt_two_div hγ hγ2
  have h2γ : 0 < 2 / γ := by positivity
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  set η₀ : ℝ := (Q γ - γ) / 4 with hη₀
  have hη : 0 < η₀ ∧ Q γ - 2 * η₀ > γ := ⟨by rw [hη₀]; linarith, by rw [hη₀]; linarith⟩
  have hbox := firstShift_nearQ_of_reflected_shift_and_gluing P X M hγ hγ2 hμ hX hM hη (hShiftGluing η₀ hη)
  set x₀ : ℝ := (2 * η₀ + γ + Q γ) / 2 with hx₀
  set b₀ : ℝ := Q γ - η₀ / 2 with hb₀
  have hx₀1 : 2 * η₀ + γ < x₀ := by rw [hx₀]; linarith
  have hx₀2 : x₀ < Q γ := by rw [hx₀]; linarith
  have hb₀1 : Q γ - η₀ < b₀ := by rw [hb₀]; linarith
  have hb₀2 : b₀ < Q γ := by rw [hb₀]; linarith
  have hq₀₁ : ExtendedSeiberg3 γ x₀ b₀ b₀ :=
    extendedSeiberg3_of_lt hγ hx₀2 hb₀2 hb₀2 (by linarith) (by linarith) (by linarith)
      (by linarith)
  have hq₀₂ : ExtendedSeiberg3 γ (x₀ - γ) b₀ b₀ :=
    extendedSeiberg3_of_lt hγ (by linarith) hb₀2 hb₀2 (by linarith) (by linarith) (by linarith)
      (by linarith)
  have key := affineLeftShift_of_box P M hγ hμ hExt 1 0
    (show (0 : ℝ) < 1 by norm_num) (R := fun _ => 1) (fun _ _ => MeromorphicAt.const _ _)
    (fun y b' c' hy₁ hy₂ hb₁ hb₂ hc₁ hc₂ _ => by
      simpa only [one_mul, add_zero] using hbox y b' c' hy₁ hy₂ hb₁ hb₂ hc₁ hc₂)
    ⟨hx₀1, hx₀2⟩ ⟨hb₀1, hb₀2⟩ ⟨hb₀1, hb₀2⟩ analyticAt_const (by simpa only [one_mul, add_zero] using hq₀₁) hq₀₂
    (by simpa only [one_mul, add_zero] using h₁) h₂ analyticAt_const
    (by simpa only [one_mul, add_zero] using hs₁) hs₂ hA
  simpa only [one_mul, add_zero] using key

end

end DOZZ.Proofs

end
