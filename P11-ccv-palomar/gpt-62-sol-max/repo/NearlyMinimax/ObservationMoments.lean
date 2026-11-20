module

public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.ModelRegularity
public import NearlyMinimax.Moments


@[expose] public section

/-! Response moments under the original covariate-dependent error model.
All localization bounds are derived from the actual observation measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def responseSecondBound {d : ℕ} (C : ModelConstants d) : ℝ :=
  C.holderBound ^ 2 + C.varianceUpper

def responseFourthBound {d : ℕ} (C : ModelConstants d) : ℝ :=
  8 * (C.holderBound ^ 4 + C.fourthBound)

section
variable {d : ℕ}

theorem responseSecondBound_pos (C : ModelConstants d) :
    0 < responseSecondBound C := by
  have hv := C.varianceLower_pos.trans C.variance_interval
  unfold responseSecondBound
  positivity

theorem responseFourthBound_pos (C : ModelConstants d) :
    0 < responseFourthBound C := by
  have h4 := lt_of_le_of_lt (sq_nonneg _) C.fourth_margin
  unfold responseFourthBound
  positivity

private theorem observation_coordinates_measurable {C : ModelConstants d}
    {θ : RegressionParameter d} (hθ : Admissible C θ) :
    Measurable (fun z : Covariate d × ℝ => (z.1, θ.regression z.1 + z.2)) :=
  measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)

/-- Single-observation Bochner disintegration, with integrability explicit. -/
theorem observationLaw_integral_conditioning {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (g : Observation d → E) (hg : Integrable g (observationLaw θ)) :
    (∫ z, g z ∂observationLaw θ) =
      ∫ x, ∫ u, g (x, θ.regression x + u) ∂θ.errors x ∂designLaw θ := by
  let := designLaw_isProbability C θ hθ
  have hm := observation_coordinates_measurable hθ
  have hcomp := hg.comp_measurable hm
  unfold observationLaw at hg ⊢
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable]
  simpa only [Function.comp_def] using Measure.integral_compProd hcomp

end

private theorem shift_fourth_moments (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f H B : ℝ) (hf : |f| ≤ H) (h4 : Integrable (fun u : ℝ => u ^ 4) μ)
    (hB : (∫ u : ℝ, u ^ 4 ∂μ) ≤ B) :
    Integrable (fun u => (f + u) ^ 4) μ ∧ (∫ u : ℝ, (f + u) ^ 4 ∂μ) ≤ 8 * (H ^ 4 + B) := by
  have hd : Integrable (fun u => 8 * (f ^ 4 + u ^ 4)) μ := ((integrable_const (f ^ 4)).add h4).const_mul 8
  have hmono (u : ℝ) : (f + u) ^ 4 ≤ 8 * (f ^ 4 + u ^ 4) := by
    have h := (show Even (4 : ℕ) by decide).add_pow_le (a := f) (b := u)
    norm_num at h
    exact h
  have hi := hd.mono_nonneg ((measurable_const.add measurable_id).pow_const 4).aestronglyMeasurable
    (.of_forall fun u : ℝ => by positivity) (.of_forall hmono)
  have hh := integral_mono hi hd hmono
  have hf4 : f ^ 4 ≤ H ^ 4 := by
    simpa only [show (4 : ℕ) = 2 * 2 by decide, pow_mul, sq_abs] using pow_le_pow_left₀ (abs_nonneg f) hf 4
  rw [integral_const_mul, integral_add (integrable_const _) h4, integral_const] at hh
  simp at hh
  exact ⟨hi, by linarith⟩

section
variable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
include hθ

theorem admissible_conditional_response_fourth :
    ∀ᵐ x ∂designLaw θ,
      Integrable (fun u : ℝ => (θ.regression x + u) ^ 4) (θ.errors x) ∧
      (∫ u : ℝ, (θ.regression x + u) ^ 4 ∂θ.errors x) ≤ responseFourthBound C := by
  filter_upwards [designLaw_cube_ae θ, hθ.2.2.2.2.2.2.2] with x hx hm
  exact shift_fourth_moments _ _ _ _ (admissible_regression_value_bound C θ hθ x hx) hm.2.2.1 hm.2.2.2.2.2

theorem admissible_conditional_response_second :
    ∀ᵐ x ∂designLaw θ,
      Integrable (fun u : ℝ => (θ.regression x + u) ^ 2) (θ.errors x) ∧
      (∫ u : ℝ, (θ.regression x + u) ^ 2 ∂θ.errors x) =
        θ.regression x ^ 2 + θ.variance ∧
      (∫ u : ℝ, (θ.regression x + u) ^ 2 ∂θ.errors x) ≤ responseSecondBound C := by
  filter_upwards [designLaw_cube_ae θ, hθ.2.2.2.2.2.2.2] with x hx hm
  have h2 : MemLp (fun u : ℝ => u) 2 (θ.errors x) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hm.2.1
  have heq := response_second_moment_of_centered_error h2 hm.2.2.2.1 hm.2.2.2.2.1
    (θ.regression x)
  refine ⟨((memLp_const (θ.regression x)).add h2).integrable_sq, heq, ?_⟩
  rw [heq]
  have hf := admissible_regression_value_bound C θ hθ x hx
  have hfsq : θ.regression x ^ 2 ≤ C.holderBound ^ 2 := by
    calc θ.regression x ^ 2 = |θ.regression x| ^ 2 := by rw [sq_abs]
         _ ≤ C.holderBound ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hf 2
  exact add_le_add hfsq hθ.2.2.2.2.2.2.1

/-- The observed covariate has exactly the original design marginal. -/
theorem observationLaw_fst_measurePreserving :
    MeasurePreserving (Prod.fst : Observation d → Covariate d)
      (observationLaw θ) (designLaw θ) := by
  let := designLaw_isProbability C θ hθ
  refine ⟨measurable_fst, ?_⟩
  have hm := observation_coordinates_measurable hθ
  unfold observationLaw
  rw [Measure.map_map measurable_fst hm]
  apply Measure.fst_compProd

/-- A measurable function of the observed design integrates under the exact
design marginal. This follows from the actual observation measure's map. -/
theorem observationLaw_integral_design (g : Covariate d → ℝ)
    (hg : Measurable g) : (∫ z, g z.1 ∂observationLaw θ) = ∫ x, g x ∂designLaw θ := by
  have hp := observationLaw_fst_measurePreserving C θ hθ
  rw [← hp.map_eq]
  exact (integral_map hp.aemeasurable hg.aestronglyMeasurable).symm

end

section
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
include hθ

/-- A bounded conditional expectation of a nonnegative function gives integrability
under the observation law. This uses the actual covariate-dependent error kernel. -/
private theorem observationLaw_integrable_of_conditional_bound {g : Observation d → ℝ}
    (hg : Measurable g) (hn : ∀ z, 0 ≤ g z) (B : ℝ)
    (hb : ∀ᵐ x ∂designLaw θ, Integrable (fun u => g (x, θ.regression x + u)) (θ.errors x) ∧
      (∫ u, g (x, θ.regression x + u) ∂θ.errors x) ≤ B) : Integrable g (observationLaw θ) := by
  let := designLaw_isProbability C θ hθ
  have hm := observation_coordinates_measurable hθ
  have hf := (hg.comp hm).stronglyMeasurable
  unfold observationLaw
  rw [integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable]
  refine (Measure.integrable_compProd_iff hf.aestronglyMeasurable).2 ⟨hb.mono fun x hx => hx.1, ?_⟩
  simp only [Function.comp_apply, Real.norm_of_nonneg (hn _)]
  refine (integrable_const B).mono_nonneg (hf.integral_kernel_prod_right' (κ := θ.errors)).aestronglyMeasurable
    (.of_forall fun x => integral_nonneg fun u => hn _) (hb.mono fun x hx => hx.2)

theorem observationLaw_response_fourth_integrable :
    Integrable (fun z : Observation d => z.2 ^ 4) (observationLaw θ) :=
  observationLaw_integrable_of_conditional_bound C θ hθ (measurable_snd.pow_const 4)
    (fun _ => by positivity) _ (admissible_conditional_response_fourth C θ hθ)

theorem observationLaw_response_memLp_two : MemLp (Prod.snd : Observation d → ℝ) 2 (observationLaw θ) :=
  (memLp_two_iff_integrable_sq measurable_snd.aestronglyMeasurable).2
    (observationLaw_integrable_of_conditional_bound C θ hθ (measurable_snd.pow_const 2)
      (fun _ => by positivity) _ ((admissible_conditional_response_second C θ hθ).mono fun x hx => ⟨hx.1, hx.2.2⟩))

section
variable (A : Set (Covariate d)) (hA : MeasurableSet A)
include hA

private theorem observationLaw_localized_integral_conditioning
    (g : Observation d → ℝ) (hg : Integrable g (observationLaw θ)) :
    (∫ z, (Prod.fst ⁻¹' A).indicator g z ∂observationLaw θ) =
      ∫ x, A.indicator (fun x => ∫ u, g (x, θ.regression x + u) ∂θ.errors x) x ∂designLaw θ := by
  rw [observationLaw_integral_conditioning C θ hθ _ (hg.indicator (measurable_fst hA))]
  exact integral_congr_ae (.of_forall fun x => by by_cases hx : x ∈ A <;> simp [hx])

private theorem observationLaw_localized_integral_le
    (g : Observation d → ℝ) (hg : Integrable g (observationLaw θ)) (hn : ∀ z, 0 ≤ g z)
    (B : ℝ) (hb : ∀ᵐ x ∂designLaw θ, (∫ u, g (x, θ.regression x + u) ∂θ.errors x) ≤ B) :
    (∫ z, (Prod.fst ⁻¹' A).indicator g z ∂observationLaw θ) ≤ B * (designLaw θ).real A := by
  let := designLaw_isProbability C θ hθ
  rw [observationLaw_localized_integral_conditioning C θ hθ A hA g hg]
  apply (integral_mono_of_nonneg (.of_forall fun x => Set.indicator_nonneg
    (fun _ _ => integral_nonneg fun u => hn _) x) ((integrable_const B).indicator hA)
    (hb.mono fun x hx => Set.indicator_le_indicator hx)).trans_eq
  simp [integral_indicator_const, hA, mul_comm]

theorem observationLaw_localized_fourth_integral_le :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 4) z ∂observationLaw θ) ≤
      responseFourthBound C * (designLaw θ).real A :=
  observationLaw_localized_integral_le C θ hθ A hA _
    (observationLaw_response_fourth_integrable C θ hθ) (fun _ => by positivity) _
    ((admissible_conditional_response_fourth C θ hθ).mono fun x hx => hx.2)

theorem observationLaw_localized_response_energy_le :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => (1 + |z.2|) ^ 2) z ∂observationLaw θ) ≤
      (2 * (1 + responseSecondBound C)) * (designLaw θ).real A := by
  let := observationLaw_isProbability C θ hθ
  have hm := observationLaw_response_memLp_two C θ hθ
  have hi := ((memLp_const (1 : ℝ)).add hm.abs).integrable_sq
  refine observationLaw_localized_integral_le C θ hθ A hA _ hi (fun _ => sq_nonneg _) _ ?_
  filter_upwards [admissible_conditional_response_second C θ hθ] with x hx
  have hd : Integrable (fun u : ℝ => 2 * (1 + (θ.regression x + u) ^ 2)) (θ.errors x) :=
    ((integrable_const 1).add hx.1).const_mul 2
  have he := integral_mono_of_nonneg (.of_forall fun u : ℝ => sq_nonneg (1 + |θ.regression x + u|)) hd
    (.of_forall fun u => by nlinarith [sq_nonneg (1 - |θ.regression x + u|), sq_abs (θ.regression x + u)])
  rw [integral_const_mul, integral_add (integrable_const _) hx.1, integral_const] at he
  simp at he
  change (∫ u, (1 + |θ.regression x + u|) ^ 2 ∂θ.errors x) ≤ _
  linarith [hx.2.2]

/-- Exact localized first moment, with the covariate-dependent conditional law. -/
theorem observationLaw_localized_first_integral :
    (∫ z, (Prod.fst ⁻¹' A).indicator (Prod.snd : Observation d → ℝ) z ∂observationLaw θ) =
      ∫ x, A.indicator θ.regression x ∂designLaw θ := by
  let := observationLaw_isProbability C θ hθ
  rw [observationLaw_localized_integral_conditioning C θ hθ A hA _
    ((observationLaw_response_memLp_two C θ hθ).integrable (by norm_num))]
  apply integral_congr_ae
  filter_upwards [hθ.2.2.2.2.2.2.2] with x hx
  by_cases hxa : x ∈ A <;> simp [hxa, integral_add (integrable_const _) hx.1, hx.2.2.2.1]

/-- Exact localized second moment; no marginal error distribution is introduced. -/
theorem observationLaw_localized_second_integral :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 2) z ∂observationLaw θ) =
      ∫ x, A.indicator (fun x => θ.regression x ^ 2 + θ.variance) x ∂designLaw θ := by
  rw [observationLaw_localized_integral_conditioning C θ hθ A hA _
    (observationLaw_response_memLp_two C θ hθ).integrable_sq]
  apply integral_congr_ae
  filter_upwards [admissible_conditional_response_second C θ hθ] with x hx
  by_cases hxa : x ∈ A <;> simp_all

end

end
end NearlyMinimax
