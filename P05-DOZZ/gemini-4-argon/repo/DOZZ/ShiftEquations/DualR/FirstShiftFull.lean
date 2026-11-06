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

theorem firstShift_full {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hShiftGluing : ∀ η : ℝ, (0 < η ∧ Q γ - 2 * η > γ) → ∀ α₂ α₃ : ℝ,
      (Q γ - η < α₂ ∧ α₂ < Q γ) → (Q γ - η < α₃ ∧ α₃ < Q γ) →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ, C z = R z * C (2 * Q γ - z)) ∧
              (∀ᶠ z in codiscrete ℂ,
                R (z + γ / 2) * C (2 * Q γ - z - γ / 2) =
                  -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
                    C (z - γ / 2)))
    {x b c : ℝ} (h₁ : ExtendedSeiberg3 γ x b c) (h₂ : ExtendedSeiberg3 γ (x - γ) b c)
    (hs₁ : AnalyticAt ℂ Complex.Gamma (sExp γ x b c : ℂ))
    (hs₂ : AnalyticAt ℂ Complex.Gamma (sExp γ (x - γ) b c : ℂ))
    (hA : ShiftCoeffGood γ ((x : ℂ) - γ / 2) b c) :
    (structureConstant P M γ μ x b c : ℂ) = -(1 / (Real.pi * μ)) *
      shiftCoeffA γ (γ / 2) ((x : ℂ) - γ / 2) b c * (structureConstant P M γ μ (x - γ) b c : ℂ) := by
  obtain ⟨V₃, hV₃, hV₃mem, f₃, hf₃, hf₃eq⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  have h2γ : 0 < 2 / γ := by positivity
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  set η₀ : ℝ := (Q γ - γ) / 4 with hη₀
  have hη : 0 < η₀ ∧ Q γ - 2 * η₀ > γ := ⟨by rw [hη₀]; linarith, by rw [hη₀]; linarith⟩
  have hbox : ∀ y b' c' : ℝ, 2 * η₀ + γ < y → y < Q γ → Q γ - η₀ < b' → b' < Q γ →
      Q γ - η₀ < c' → c' < Q γ →
      (structureConstant P M γ μ y b' c' : ℂ) = -(1 / (Real.pi * μ)) *
        shiftCoeffA γ (γ / 2) ((y : ℂ) - γ / 2) b' c' *
          (structureConstant P M γ μ (y - γ) b' c' : ℂ) := by
    intro y b' c' hy₁ hy₂ hb₁ hb₂ hc₁ hc₂
    obtain ⟨B, Z, -, -, h, hh, C, R, hCm, -, hCv, -, hglue, hrefl⟩ :=
      hShiftGluing η₀ hη b' c' ⟨hb₁, hb₂⟩ ⟨hc₁, hc₂⟩
    exact firstShift_exact_of_strip P M hγ hγ2 hμ hη ⟨hb₁, hb₂⟩ ⟨hc₁, hc₂⟩ hV₃ hV₃mem hf₃ hf₃eq hh
      hCm hCv (by filter_upwards [eventually_codiscrete_comp_add hglue ((γ : ℂ) / 2), hrefl] with z h1 h2; rw [h1, show 2 * (Q γ : ℂ) - (z + γ / 2) = 2 * Q γ - z - γ / 2 by ring, h2]) hy₁ hy₂ (analyticAt_shiftCoeffA_comp (f₁ := id) (f₂ := fun _ => (b' : ℂ))
        (f₃ := fun _ => (c' : ℂ)) analyticAt_id analyticAt_const analyticAt_const (shiftCoeffGood_of_lt hγ (by linarith [hη.1]) (by linarith [hη.2]) (by linarith [hη.1, hη.2]) (by linarith [hη.1, hη.2]) (by linarith [hη.1, hη.2])))
  set x₀ : ℝ := (2 * η₀ + γ + Q γ) / 2 with hx₀
  set b₀ : ℝ := Q γ - η₀ / 2 with hb₀
  have hx₀2 : x₀ < Q γ := by rw [hx₀]; linarith
  have hb₀1 : Q γ - η₀ < b₀ := by rw [hb₀]; linarith
  have hb₀2 : b₀ < Q γ := by rw [hb₀]; linarith
  have hq₀₁ : ExtendedSeiberg3 γ x₀ b₀ b₀ :=
    extendedSeiberg3_of_lt hγ hx₀2 hb₀2 hb₀2 (by linarith) (by linarith) (by linarith)
      (by linarith)
  have hq₀₂ : ExtendedSeiberg3 γ (x₀ - γ) b₀ b₀ :=
    extendedSeiberg3_of_lt hγ (by linarith) hb₀2 hb₀2 (by linarith) (by linarith) (by linarith)
      (by linarith)
  set U : Set ℂ := segT x₀ x b₀ b b₀ c ⁻¹' V₃ ∩ segT (x₀ - γ) (x - γ) b₀ b b₀ c ⁻¹' V₃ with hU
  set F : ℂ → ℂ := fun t => structureConstantH f₃ γ μ (segT x₀ x b₀ b b₀ c t) with hF
  set G : ℂ → ℂ := fun t => -(1 / (Real.pi * μ)) *
    shiftCoeffA γ ((γ : ℂ) / 2) (segC x₀ x t - γ / 2) (segC b₀ b t) (segC b₀ c t) *
      structureConstantH f₃ γ μ (segT (x₀ - γ) (x - γ) b₀ b b₀ c t) with hG
  have hFm : MeromorphicOn F U :=
    (segH_meromorphicOn hV₃ hf₃ hμ x₀ x b₀ b b₀ c).mono_set inter_subset_left
  have hGm : MeromorphicOn G U := fun t ht =>
    (MeromorphicAt.const _ t |>.fun_mul (meromorphicAt_shiftCoeffA_comp
      (f₁ := fun t => segC x₀ x t - γ / 2) ((analyticAt_segC x₀ x t).sub analyticAt_const)
      (analyticAt_segC b₀ b t) (analyticAt_segC b₀ c t))).fun_mul
      (segH_meromorphicOn hV₃ hf₃ hμ (x₀ - γ) (x - γ) b₀ b b₀ c t ht.2)
  have hstart : ∀ᶠ t : ℝ in 𝓝[>] 0, F t = G t := by
    filter_upwards [eventually_segC_mem (b := x) isOpen_Ioo ⟨(show 2 * η₀ + γ < x₀ by rw [hx₀]; linarith), hx₀2⟩,
      eventually_segC_mem (b := b) isOpen_Ioo ⟨hb₀1, hb₀2⟩,
      eventually_segC_mem (b := c) isOpen_Ioo ⟨hb₀1, hb₀2⟩,
      Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t hxt hbt hct ht
    simp only [hF, hG]
    rw [segH_ofReal P M hμ hf₃eq (extendedSeiberg3_segment hγ hq₀₁ h₁ ht.1.le ht.2.le), segH_ofReal P M hμ hf₃eq (extendedSeiberg3_segment hγ hq₀₂ h₂ ht.1.le ht.2.le), segC_ofReal, segC_ofReal,
      segC_ofReal, show x₀ - γ + t * (x - γ - (x₀ - γ)) = x₀ + t * (x - x₀) - γ by ring]
    exact hbox _ _ _ hxt.1 hxt.2 hbt.1 hbt.2 hct.1 hct.2
  have hF1 : AnalyticAt ℂ F 1 := segH_analyticAt_one hV₃ hf₃ hμ (hV₃mem ![x, b, c] h₁) hs₁
  have hG1 : AnalyticAt ℂ G 1 := by
    refine (analyticAt_const.mul (analyticAt_shiftCoeffA_comp
      (f₁ := fun t => segC x₀ x t - γ / 2)
      ((analyticAt_segC x₀ x 1).sub analyticAt_const) (analyticAt_segC b₀ b 1)
      (analyticAt_segC b₀ c 1) ?_)).mul
      (segH_analyticAt_one hV₃ hf₃ hμ (hV₃mem ![x - γ, b, c] h₂) hs₂)
    rw [segC_one, segC_one, segC_one]
    exact hA
  have key := eq_at_one_of_segment (fun t h0 h1 => ⟨segT_mem hγ hV₃mem hq₀₁ h₁ h0 h1, segT_mem hγ hV₃mem hq₀₂ h₂ h0 h1⟩ : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (t : ℂ) ∈ U) hFm hGm hstart hF1 hG1
  simp only [hF, hG] at key
  rw [segH_one P M hμ hf₃eq h₁, segH_one P M hμ hf₃eq h₂, segC_one, segC_one, segC_one] at key
  exact key

end DOZZ.Proofs

end
