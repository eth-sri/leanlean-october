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

section
variable {d : ℕ} (C : ModelConstants d) {μ : Measure ℝ}

def responseSecondBound : ℝ :=
  C.holderBound ^ 2 + C.varianceUpper

def responseFourthBound : ℝ :=
  8 * (C.holderBound ^ 4 + C.fourthBound)

theorem responseSecondBound_pos :
    0 < responseSecondBound C := by
  have hv  := C.varianceLower_pos.trans C.variance_interval
  unfold responseSecondBound
  positivity

theorem responseFourthBound_pos :
    0 < responseFourthBound C := by
  have h4  := lt_of_le_of_lt (sq_nonneg _) C.fourth_margin
  unfold responseFourthBound
  positivity

/-- Single-observation Tonelli disintegration for the model's actual law. -/
theorem observationLaw_lintegral_conditioning {C : ModelConstants d}
    {θ : RegressionParameter d} (hθ : Admissible C θ)
    {g : Observation d → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ z, g z ∂observationLaw θ) =
      ∫⁻ x, ∫⁻ u, g (x, θ.regression x + u) ∂θ.errors x ∂designLaw θ := by
  let := designLaw_isProbability C θ hθ
  have hm := responseShift_measurable hθ
  unfold observationLaw
  rw [lintegral_map' hg.aemeasurable hm.aemeasurable]
  exact Measure.lintegral_compProd (hg.comp hm)

/-- Single-observation Bochner disintegration, with integrability explicit. -/
theorem observationLaw_integral_conditioning {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {C : ModelConstants d}
    {θ : RegressionParameter d} (hθ : Admissible C θ)
    {g : Observation d → E} (hg : Integrable g (observationLaw θ)) :
    (∫ z, g z ∂observationLaw θ) =
      ∫ x, ∫ u, g (x, θ.regression x + u) ∂θ.errors x ∂designLaw θ := by
  let := designLaw_isProbability C θ hθ
  have hm := responseShift_measurable hθ
  have hcomp := hg.comp_measurable hm
  unfold observationLaw at hg ⊢
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable]
  exact Measure.integral_compProd hcomp

/-- Control the integrability and the value of the shifted fourth moment
with the same pointwise majorant. -/
theorem shifted_fourth_moment [IsProbabilityMeasure μ] {f H B : ℝ} (hf : |f| ≤ H)
    (hi : Integrable (fun u => u ^ 4) μ) (hB : (∫ u, u ^ 4 ∂μ) ≤ B) :
    Integrable (fun u => (f + u) ^ 4) μ ∧ (∫ u, (f + u) ^ 4 ∂μ) ≤ 8 * (H ^ 4 + B) := by
  have hm (u : ℝ) : (f + u)^4 ≤ 8*(f^4 + u^4) := by
    have h := (show Even 4 by decide).add_pow_le (a := f) (b := u)
    norm_num at h
    exact h
  have hd := ((integrable_const (f ^ 4)).add hi).const_mul 8
  have hs := hd.mono' (f := fun u => (f + u)^4) (by fun_prop)
    (Eventually.of_forall fun u => by change _ ≤ _; rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hm u)
  refine ⟨hs, (integral_mono hs hd hm).trans ?_⟩
  simp only [Pi.add_apply, integral_const_mul, integral_add (integrable_const _) hi, integral_const,
    probReal_univ, one_smul]
  apply mul_le_mul_of_nonneg_left (add_le_add ?_ hB) (by norm_num)
  simpa only [(show Even 4 by decide).pow_abs] using pow_le_pow_left₀ (abs_nonneg _) hf 4

end

variable {d : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ)
    {A : Set (Covariate d)} (hA : MeasurableSet A)
include hθ

theorem admissible_conditional_response_fourth :
    ∀ᵐ x ∂designLaw θ,
      Integrable (fun u => (θ.regression x + u) ^ 4) (θ.errors x) ∧
      (∫ u, (θ.regression x + u) ^ 4 ∂θ.errors x) ≤ responseFourthBound C := by
  filter_upwards [designLaw_cube_ae θ, hθ.2.2.2.2.2.2.2] with x hx hm
  exact shifted_fourth_moment (admissible_regression_value_bound hθ hx) hm.2.2.1 hm.2.2.2.2.2

theorem admissible_conditional_response_second :
    ∀ᵐ x ∂designLaw θ,
      Integrable (fun u => (θ.regression x + u) ^ 2) (θ.errors x) ∧
      (∫ u, (θ.regression x + u) ^ 2 ∂θ.errors x) =
        θ.regression x ^ 2 + θ.variance ∧
      (∫ u, (θ.regression x + u) ^ 2 ∂θ.errors x) ≤ responseSecondBound C := by
  filter_upwards [designLaw_cube_ae θ, hθ.2.2.2.2.2.2.2] with x hx hm
  have h2 : MemLp (fun u => u) 2 (θ.errors x) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hm.2.1
  have heq := response_second_moment_of_centered_error h2 hm.2.2.2.1 hm.2.2.2.2.1
    (θ.regression x)
  refine ⟨((memLp_const (θ.regression x)).add h2).integrable_sq, heq, ?_⟩
  rw [heq]
  have hf := admissible_regression_value_bound hθ hx
  have hfsq : θ.regression x ^ 2 ≤ C.holderBound ^ 2 := by
    calc _ = |θ.regression x| ^ 2 := by simp
         _ ≤ _ := by bound
  exact add_le_add hfsq hθ.2.2.2.2.2.2.1

include hA in
/-- Uniform conditional moments transfer to every localization of the response
under the observable joint law. In particular the response moment is integrable. -/
theorem localized_response_moment {f : ℝ → ℝ} {B : ℝ} (hf : Measurable f)
    (hn : ∀ t, 0 ≤ f t) (hB : 0 ≤ B)
    (h : ∀ᵐ x ∂designLaw θ, Integrable (fun u => f (θ.regression x + u)) (θ.errors x) ∧
      (∫ u, f (θ.regression x + u) ∂θ.errors x) ≤ B) :
    let g := (Prod.fst ⁻¹' A).indicator (fun z : Observation d => f z.2)
    Integrable g (observationLaw θ) ∧ (∫ z, g z ∂observationLaw θ) ≤ B * (designLaw θ).real A := by
  intro g
  let := designLaw_isProbability C θ hθ
  have hg : Measurable g := (hf.comp measurable_snd).indicator (measurable_fst hA)
  have hpos (z) : 0 ≤ g z := Set.indicator_nonneg (fun x _ => hn x.2) z
  have hlin : (∫⁻ z, ENNReal.ofReal (g z) ∂observationLaw θ) ≤ ENNReal.ofReal (B * (designLaw θ).real A) := by
    rw [observationLaw_lintegral_conditioning hθ hg.ennreal_ofReal]
    calc
      _ ≤ ∫⁻ x, A.indicator (fun _ => ENNReal.ofReal B) x ∂designLaw θ := by
        apply lintegral_mono_ae
        filter_upwards [h] with x hx
        by_cases hmem : x ∈ A
        · simp only [g, Set.indicator, Set.mem_preimage, hmem, ite_true]
          rw [← ofReal_integral_eq_lintegral_ofReal hx.1 (.of_forall fun u => hn _)]
          exact ENNReal.ofReal_mono hx.2
        · simp [g, Set.indicator, hmem]
      _ = _ := by rw [lintegral_indicator_const hA, ENNReal.ofReal_mul hB, measureReal_def,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hi : Integrable g (observationLaw θ) := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    simpa only [hasFiniteIntegral_iff_enorm, Real.enorm_of_nonneg (hpos _)] using
      hlin.trans_lt ENNReal.ofReal_lt_top
  rw [← ofReal_integral_eq_lintegral_ofReal hi (.of_forall hpos)] at hlin
  exact ⟨hi, (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB (measureReal_nonneg))).mp hlin⟩

/-- The observed covariate has exactly the original design marginal. -/
theorem observationLaw_fst_measurePreserving :
    MeasurePreserving Prod.fst
      (observationLaw θ) (designLaw θ) := by
  let := designLaw_isProbability C θ hθ
  refine ⟨measurable_fst, ?_⟩
  have hm := responseShift_measurable hθ
  unfold observationLaw
  rw [Measure.map_map measurable_fst hm]
  exact Measure.fst_compProd (designLaw θ) θ.errors

theorem observationLaw_response_fourth_integrable :
    Integrable (fun z => z.2 ^ 4) (observationLaw θ) := by
  simpa using (localized_response_moment hθ (A := univ) MeasurableSet.univ (f := (· ^ 4))
    (by fun_prop) (by intro; positivity) (responseFourthBound_pos C).le (admissible_conditional_response_fourth hθ)).1

theorem observationLaw_response_memLp_four :
    MemLp Prod.snd 4 (observationLaw θ) := by
  apply (integrable_norm_rpow_iff
    measurable_snd.aestronglyMeasurable (by norm_num) (by simp)).mp
  have heq : (fun z : Observation d => ‖z.2‖ ^ ((4 : ℝ≥0∞).toReal)) =
      (fun z => z.2 ^ 4) := by
    funext z
    norm_num only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
    exact Eq.trans (Eq.trans (Real.rpow_natCast _ _) ((abs_pow z.2 4).symm)) (abs_of_nonneg (by positivity))
  rw [heq]
  exact observationLaw_response_fourth_integrable hθ

theorem observationLaw_response_memLp_two :
    MemLp Prod.snd 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  exact (observationLaw_response_memLp_four hθ).mono_exponent (by norm_num)

include hA in
theorem observationLaw_localized_second_integral_le :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z => z.2 ^ 2) z
      ∂observationLaw θ) ≤ responseSecondBound C * (designLaw θ).real A :=
  (localized_response_moment hθ hA (f := (· ^ 2)) (by fun_prop) sq_nonneg (responseSecondBound_pos C).le
    ((admissible_conditional_response_second hθ).mono fun _ h => ⟨h.1, h.2.2⟩)).2

include hA in
theorem observationLaw_localized_fourth_integral_le :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z => z.2 ^ 4) z
      ∂observationLaw θ) ≤ responseFourthBound C * (designLaw θ).real A :=
  (localized_response_moment hθ hA (f := (· ^ 4)) (by fun_prop) (by intro; positivity)
    (responseFourthBound_pos C).le (admissible_conditional_response_fourth hθ)).2

include hA in
theorem observationLaw_localized_response_energy_le :
    (∫ z, (Prod.fst ⁻¹' A).indicator
      (fun z => (1 + |z.2|) ^ 2) z ∂observationLaw θ) ≤
      (2 * (1 + responseSecondBound C)) * (designLaw θ).real A := by
  let := observationLaw_isProbability C θ hθ
  have hs : MemLp (fun z => |z.2|) 2 (observationLaw θ) := by
    exact (observationLaw_response_memLp_two hθ).norm
  have hi : Integrable (fun z => (1 + |z.2|) ^ 2)
      (observationLaw θ) := ((memLp_const (1 : ℝ)).add hs).integrable_sq
  have hd : Integrable (fun z => 2 * (1 + z.2 ^ 2))
      (observationLaw θ) :=
    ((integrable_const 1).add
      (observationLaw_response_memLp_two hθ).integrable_sq).const_mul 2
  have hb := integral_mono (hi.indicator (measurable_fst hA))
    (hd.indicator (measurable_fst hA)) (fun z => by
      apply Set.indicator_le_indicator
      have hab := sq_nonneg (1 - |z.2|)
      nlinarith [sq_abs z.2])
  have heq : (fun z => (Prod.fst ⁻¹' A).indicator
      (fun z => 2 * (1 + z.2 ^ 2)) z) =
      (fun z => 2 * ((Prod.fst ⁻¹' A).indicator (fun _ => 1) z +
        (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 2) z)) := by
    funext z
    by_cases hz : z.1 ∈ A <;> simp [hz]
  rw [heq, integral_const_mul,
    integral_add ((integrable_const 1).indicator (measurable_fst hA))
      ((observationLaw_response_memLp_two hθ).integrable_sq.indicator
        (measurable_fst hA))] at hb
  have hI : (∫ z, (Prod.fst ⁻¹' A).indicator (fun _ => 1) z
      ∂observationLaw θ) = (designLaw θ).real A := by
    rw [integral_indicator_const 1 (measurable_fst hA)]
    simp
    exact (observationLaw_fst_measurePreserving hθ).measureReal_preimage
      hA.nullMeasurableSet
  rw [hI] at hb
  have hb2 := observationLaw_localized_second_integral_le hθ hA
  nlinarith

include hA in
/-- Exact localized first moment, with the covariate-dependent conditional law. -/
theorem observationLaw_localized_first_integral :
    (∫ z, (Prod.fst ⁻¹' A).indicator Prod.snd z
      ∂observationLaw θ) =
      ∫ x, A.indicator θ.regression x ∂designLaw θ := by
  let := observationLaw_isProbability C θ hθ
  have hi := (observationLaw_response_memLp_two hθ).integrable (by norm_num)
  rw [observationLaw_integral_conditioning hθ
    (hi.indicator (measurable_fst hA))]
  apply integral_congr_ae
  filter_upwards [hθ.2.2.2.2.2.2.2] with x hx
  by_cases hxa : x ∈ A
  · simp [hxa, integral_add (integrable_const _) hx.1, hx.2.2.2.1]
  · simp [hxa]

include hA in
/-- Exact localized second moment; no marginal error distribution is introduced. -/
theorem observationLaw_localized_second_integral :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z => z.2 ^ 2) z
      ∂observationLaw θ) =
      ∫ x, A.indicator (fun x => θ.regression x ^ 2 + θ.variance) x ∂designLaw θ := by
  have hi := (observationLaw_response_memLp_two hθ).integrable_sq
  rw [observationLaw_integral_conditioning hθ
    (hi.indicator (measurable_fst hA))]
  apply integral_congr_ae
  filter_upwards [admissible_conditional_response_second hθ] with x hx
  by_cases hxa : x ∈ A
  · simpa [hxa] using hx.2.1
  · simp [hxa]

end NearlyMinimax
