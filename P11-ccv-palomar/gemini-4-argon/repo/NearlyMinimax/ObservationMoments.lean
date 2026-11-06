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

def responseSecondBound  (C : ModelConstants d) : ℝ :=
  C.holderBound ^ 2 + C.varianceUpper

def responseFourthBound  (C : ModelConstants d) : ℝ :=
  8 * (C.holderBound ^ 4 + C.fourthBound)

theorem responseSecondBound_pos  (C : ModelConstants d) :
    0 < responseSecondBound C := by
  have : 0 < C.varianceUpper := C.varianceLower_pos.trans C.variance_interval
  unfold responseSecondBound
  positivity

theorem responseFourthBound_pos  (C : ModelConstants d) :
    0 < responseFourthBound C := by
  have : 0 < C.fourthBound := lt_of_le_of_lt (sq_nonneg _) C.fourth_margin
  unfold responseFourthBound
  positivity

/-- Single-observation Tonelli disintegration for the model's actual law. -/
theorem observationLaw_lintegral_conditioning  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (g ) (hg : Measurable g) :
    (∫⁻ z, g z ∂observationLaw θ) =
      ∫⁻ x, ∫⁻ u, g (x, θ.regression x + u) ∂θ.errors x ∂designLaw θ := by
  let := designLaw_isProbability C θ hθ
  have hm : Measurable (fun z : Covariate d × ℝ =>
      (z.1, θ.regression z.1 + z.2)) :=
    measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)
  unfold observationLaw
  rw [lintegral_map' hg.aemeasurable hm.aemeasurable]
  simpa only [Function.comp_def] using Measure.lintegral_compProd (hg.comp hm)

/-- Single-observation Bochner disintegration, with integrability explicit. -/
theorem observationLaw_integral_conditioning  
    [NormedAddCommGroup E] [NormedSpace ℝ E] (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (g : Observation d → E) (hg : Integrable g (observationLaw θ)) :
    (∫ z, g z ∂observationLaw θ) =
      ∫ x, ∫ u, g (x, θ.regression x + u) ∂θ.errors x ∂designLaw θ := by
  let := designLaw_isProbability C θ hθ
  have hm : Measurable (fun z : Covariate d × ℝ =>
      (z.1, θ.regression z.1 + z.2)) :=
    measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)
  unfold observationLaw at hg ⊢
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable]
  simpa only [Function.comp_def] using Measure.integral_compProd (hg.comp_measurable hm)

/-- A shift of an unbounded fourth-integrable error is fourth integrable. -/
theorem integrable_shift_fourth (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ) (h4 : Integrable (fun u : ℝ => u ^ 4) μ) :
    Integrable (fun u => (f + u) ^ 4) μ := by
  apply (((integrable_const (f ^ 4)).add h4).const_mul 8).mono' ((measurable_const.add measurable_id).pow_const 4).aestronglyMeasurable
  filter_upwards [] with u
  change ‖(f + u) ^ 4‖ ≤ 8 * (f ^ 4 + u ^ 4)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (f + u) ^ 4)]
  have hp := (show Even 4 by decide).add_pow_le (a := f) (b := u)
  norm_num at hp
  exact hp

theorem integral_shift_fourth_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f H B : ℝ) (_hH : 0 ≤ H) (hf : |f| ≤ H)
    (h4 : Integrable (fun u : ℝ => u ^ 4) μ)
    (hB : (∫ u : ℝ, u ^ 4 ∂μ) ≤ B) :
    (∫ u : ℝ, (f + u) ^ 4 ∂μ) ≤ 8 * (H ^ 4 + B) := by
  have hmono : (∫ u : ℝ, (f + u) ^ 4 ∂μ) ≤
      ∫ u : ℝ, 8 * (f ^ 4 + u ^ 4) ∂μ := by
    apply integral_mono (integrable_shift_fourth μ f h4) (((integrable_const (f ^ 4)).add h4).const_mul 8)
    intro u
    have hp := (show Even 4 by decide).add_pow_le (a := f) (b := u)
    norm_num at hp
    exact hp
  have : f ^ 4 ≤ H ^ 4 := by
    calc f ^ 4 = |f| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
         _ ≤ H ^ 4 := pow_le_pow_left₀ (abs_nonneg f) hf 4
  rw [integral_const_mul, integral_add (integrable_const _) h4, integral_const] at hmono
  simp at hmono
  nlinarith

theorem admissible_conditional_response_second  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    ∀ᵐ x ∂designLaw θ,
      Integrable (fun u => (θ.regression x + u) ^ 2) (θ.errors x) ∧
      (∫ u : ℝ, (θ.regression x + u) ^ 2 ∂θ.errors x) =
        θ.regression x ^ 2 + θ.variance ∧
      (∫ u : ℝ, (θ.regression x + u) ^ 2 ∂θ.errors x) ≤ responseSecondBound C := by
  filter_upwards [designLaw_cube_ae θ, hθ.2.2.2.2.2.2.2] with x hx hm
  have h2 : MemLp (fun u => u) 2 (θ.errors x) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hm.2.1
  have heq := response_second_moment_of_centered_error h2 hm.2.2.2.1 hm.2.2.2.2.1
    (θ.regression x)
  refine ⟨((memLp_const (θ.regression x)).add h2).integrable_sq, heq, ?_⟩
  rw [heq]
  have hfsq : θ.regression x ^ 2 ≤ C.holderBound ^ 2 := by
    calc θ.regression x ^ 2 = |θ.regression x| ^ 2 := by rw [sq_abs]
         _ ≤ C.holderBound ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (admissible_regression_value_bound C θ hθ x hx) 2
  exact add_le_add hfsq hθ.2.2.2.2.2.2.1

/-- Arbitrary nonnegative design weights may localize the response fourth moment. -/
theorem observationLaw_weighted_fourth_le  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (w ) (hw : Measurable w) :
    (∫⁻ z, w z.1 * ENNReal.ofReal (z.2 ^ 4) ∂observationLaw θ) ≤
      ENNReal.ofReal (responseFourthBound C) * ∫⁻ x, w x ∂designLaw θ := by
  rw [observationLaw_lintegral_conditioning C θ hθ
    (fun z => w z.1 * ENNReal.ofReal (z.2 ^ 4))
    ((hw.comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const 4)))]
  calc
    _ ≤ ∫⁻ x, w x * ENNReal.ofReal (responseFourthBound C) ∂designLaw θ := by
      apply lintegral_mono_ae
      have h_admissible_conditional_response_fourth : ∀ᵐ x ∂designLaw θ,
      Integrable (fun u => (θ.regression x + u) ^ 4) (θ.errors x) ∧
      (∫ u : ℝ, (θ.regression x + u) ^ 4 ∂θ.errors x) ≤ responseFourthBound C := by
        filter_upwards [designLaw_cube_ae θ, hθ.2.2.2.2.2.2.2] with x hx hm
        exact ⟨integrable_shift_fourth _ _ hm.2.2.1,
          integral_shift_fourth_le _ _ _ _ C.holderBound_pos.le
            (admissible_regression_value_bound C θ hθ x hx) hm.2.2.1 hm.2.2.2.2.2⟩
      filter_upwards [h_admissible_conditional_response_fourth] with x hx
      rw [lintegral_const_mul (w x)
        (f := fun u => ENNReal.ofReal ((θ.regression x + u) ^ 4)) (by fun_prop)]
      gcongr
      rw [← ofReal_integral_eq_lintegral_ofReal hx.1
        (Eventually.of_forall (fun u => by positivity))]
      exact ENNReal.ofReal_mono hx.2
    _ = _ := by rw [lintegral_mul_const _ hw, mul_comm]

/-- The observed covariate has exactly the original design marginal. -/
theorem observationLaw_fst_measurePreserving  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    MeasurePreserving (Prod.fst : Observation d → Covariate d)
      (observationLaw θ) (designLaw θ) := by
  let := designLaw_isProbability C θ hθ
  refine ⟨measurable_fst, ?_⟩
  have hm : Measurable (fun z : Covariate d × ℝ =>
      (z.1, θ.regression z.1 + z.2)) :=
    measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)
  unfold observationLaw
  rw [Measure.map_map measurable_fst hm]
  exact Measure.fst_compProd (designLaw θ) θ.errors

theorem observationLaw_response_fourth_integrable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    Integrable (fun z : Observation d => z.2 ^ 4) (observationLaw θ) := by
  refine ⟨(measurable_snd.pow_const 4).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have heq : (fun z : Observation d => ‖z.2 ^ 4‖ₑ) =
      (fun z => ENNReal.ofReal (z.2 ^ 4)) := by
    funext z
    exact Real.enorm_of_nonneg (by positivity)
  rw [heq]
  let := designLaw_isProbability C θ hθ
  exact lt_of_le_of_lt (by simpa using observationLaw_weighted_fourth_le C θ hθ (fun _ => 1) measurable_const) ENNReal.ofReal_lt_top

theorem observationLaw_response_memLp_two  (C θ) (hθ : Admissible C θ) :
    MemLp (Prod.snd : Observation d → ℝ) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  have h_observationLaw_response_memLp_four : MemLp (Prod.snd : Observation d → ℝ) 4 (observationLaw θ) := by
    apply (integrable_norm_rpow_iff (f := Prod.snd) (p := 4)
      measurable_snd.aestronglyMeasurable (by norm_num) (by simp)).mp
    have heq : (fun z : Observation d => ‖z.2‖ ^ ((4 : ℝ≥0∞).toReal)) =
        (fun z => z.2 ^ 4) := by
      funext z
      norm_num only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
      calc
        |z.2| ^ 4 = |z.2| ^ 4 := Real.rpow_natCast _ _
        _ = |z.2 ^ 4| := (abs_pow z.2 4).symm
        _ = z.2 ^ 4 := abs_of_nonneg (by positivity)
    rw [heq]
    exact observationLaw_response_fourth_integrable C θ hθ
  exact h_observationLaw_response_memLp_four.mono_exponent (by norm_num)

theorem observationLaw_localized_second_integral_le  (C θ) (hθ : Admissible C θ)
    (A : Set (Covariate d)) (hA : MeasurableSet A) :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z => z.2 ^ 2) z
      ∂observationLaw θ) ≤ responseSecondBound C * (designLaw θ).real A := by
  have hi := (observationLaw_response_memLp_two C θ hθ).integrable_sq.indicator
    (measurable_fst hA)
  have h_observationLaw_weighted_second_le (w) (hw : Measurable w) : (∫⁻ z, w z.1 * ENNReal.ofReal (z.2 ^ 2) ∂observationLaw θ) ≤
      ENNReal.ofReal (responseSecondBound C) * ∫⁻ x, w x ∂designLaw θ := by
    rw [observationLaw_lintegral_conditioning C θ hθ
      (fun z => w z.1 * ENNReal.ofReal (z.2 ^ 2))
      ((hw.comp measurable_fst).mul
        (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const 2)))]
    calc
      _ ≤ ∫⁻ x, w x * ENNReal.ofReal (responseSecondBound C) ∂designLaw θ := by
        apply lintegral_mono_ae
        filter_upwards [admissible_conditional_response_second C θ hθ] with x hx
        rw [lintegral_const_mul (w x)
          (f := fun u => ENNReal.ofReal ((θ.regression x + u) ^ 2)) (by fun_prop)]
        gcongr
        rw [← ofReal_integral_eq_lintegral_ofReal hx.1
          (Eventually.of_forall (fun u => by positivity))]
        exact ENNReal.ofReal_mono hx.2.2
      _ = _ := by rw [lintegral_mul_const _ hw, mul_comm]
  have hh := h_observationLaw_weighted_second_le (A.indicator (fun _ => 1)) (measurable_const.indicator hA)
  have heq : (fun z => A.indicator (fun _ => (1 : ℝ≥0∞)) z.1 *
      ENNReal.ofReal (z.2 ^ 2)) = (fun z => ENNReal.ofReal
      ((Prod.fst ⁻¹' A).indicator (fun z => z.2 ^ 2) z)) := by
    funext z
    by_cases hz : z.1 ∈ A <;> simp [hz]
  have hh := (by rw [heq, lintegral_indicator_const hA, one_mul] at hh; exact hh)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun z => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _))] at hh
  have hb := responseSecondBound_pos C
  let := designLaw_isProbability C θ hθ
  have hfinite := measure_ne_top (designLaw θ) A
  have heq : ENNReal.ofReal (responseSecondBound C) * designLaw θ A =
      ENNReal.ofReal (responseSecondBound C * (designLaw θ).real A) := by
    rw [ENNReal.ofReal_mul hb.le, measureReal_def, ENNReal.ofReal_toReal hfinite]
  rw [heq] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

theorem observationLaw_localized_fourth_integral_le  (C θ) (hθ : Admissible C θ)
    (A : Set (Covariate d)) (hA : MeasurableSet A) :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 4) z
      ∂observationLaw θ) ≤ responseFourthBound C * (designLaw θ).real A := by
  have hi := (observationLaw_response_fourth_integrable C θ hθ).indicator
    (measurable_fst hA)
  have hh := observationLaw_weighted_fourth_le C θ hθ
    (A.indicator (fun _ => 1)) (measurable_const.indicator hA)
  have heq : (fun z : Observation d => A.indicator (fun _ => (1 : ℝ≥0∞)) z.1 *
      ENNReal.ofReal (z.2 ^ 4)) = (fun z => ENNReal.ofReal
      ((Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 4) z)) := by
    funext z
    by_cases hz : z.1 ∈ A <;> simp [hz]
  have hh := (by rw [heq, lintegral_indicator_const hA, one_mul] at hh; exact hh)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun z => Set.indicator_nonneg (fun _ _ => by positivity) _))] at hh
  have hb := responseFourthBound_pos C
  let := designLaw_isProbability C θ hθ
  have hfinite := measure_ne_top (designLaw θ) A
  have heq : ENNReal.ofReal (responseFourthBound C) * designLaw θ A =
      ENNReal.ofReal (responseFourthBound C * (designLaw θ).real A) := by
    rw [ENNReal.ofReal_mul hb.le, measureReal_def, ENNReal.ofReal_toReal hfinite]
  rw [heq] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

end NearlyMinimax
