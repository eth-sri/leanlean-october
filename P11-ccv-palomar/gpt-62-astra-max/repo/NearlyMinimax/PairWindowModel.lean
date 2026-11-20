module

public import NearlyMinimax.PairWindowMoments


@[expose] public section

/-! Same-cell score moments specialized to the original statistical model. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

variable {d : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) {k : ℕ}
    (hk : 0 < k)

def regularObservationLabel :
    Observation d → (Fin d → Fin k) := fun z => regularGridCell k hk z.1

theorem regularObservationLabel_measurable :
    Measurable (regularObservationLabel (d := d) hk) :=
  (regular_grid_cell_measurable k hk).comp measurable_fst

theorem regularObservationLabel_fiber
    (c : Fin d → Fin k) :
    (regularObservationLabel hk) ⁻¹' {c} =
      Prod.fst ⁻¹' ((regularGridCell k hk) ⁻¹' {c}) := rfl

include hθ in
theorem regularObservationLabel_mass
    (c : Fin d → Fin k) :
    (observationLaw θ).real ((regularObservationLabel hk) ⁻¹' {c}) =
      regularGridProbability θ hk c := (observationLaw_fst_measurePreserving hθ).measureReal_preimage
    ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk)).nullMeasurableSet

def regularPairScore (θ : RegressionParameter d) {k : ℕ} (hk : 0 < k) :
    Observation d × Observation d → ℝ :=
  pairWindowScore (regularObservationLabel hk) Prod.snd θ.variance

include hθ in
theorem regularPairScore_memLp :
    MemLp (regularPairScore θ hk) 2 ((observationLaw θ).prod (observationLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact pairWindowScore_memLp (observationLaw θ) _
    (regularObservationLabel_measurable hk) measurable_snd θ.variance
    (observationLaw_response_fourth_integrable hθ)

include hθ in
theorem regularPairScore_kernel_energy_le :
    (∫ z, regularPairScore θ hk z ^ 2
      ∂(observationLaw θ).prod (observationLaw θ)) ≤
      (8 * responseFourthBound C + 2 * θ.variance ^ 2) *
        regularGridCollisionMass θ hk := by
  let := observationLaw_isProbability C θ hθ
  have hh := pairWindowScore_energy_le (observationLaw θ) _
    (regularObservationLabel_measurable hk) measurable_snd
    θ.variance (responseFourthBound C)
    (observationLaw_response_fourth_integrable hθ) (fun c => by
      rw [regularObservationLabel_mass hθ hk c,
        regularObservationLabel_fiber hk c]
      exact observationLaw_localized_fourth_integral_le hθ (A := ((regularGridCell k hk) ⁻¹' {c})) ((measurableSet_singleton _).preimage (regular_grid_cell_measurable k hk)))
  simpa only [regularObservationLabel_mass hθ hk,
    regularPairScore, regularGridCollisionMass] using hh

include hθ in
theorem regularPairScore_row_energy_le :
    (∫ x, (∫ y, regularPairScore θ hk (x, y) ∂observationLaw θ) ^ 2
      ∂observationLaw θ) ≤
      2 * (C.densityUpper / k ^ d) ^ 2 *
        (responseFourthBound C + (|θ.variance| + responseSecondBound C) ^ 2) := by
  let := observationLaw_isProbability C θ hθ
  let := designLaw_isProbability C θ hθ
  have hρ  := (by norm_num : (0 : ℝ) < 1).trans C.one_lt_densityUpper
  apply pairWindowScore_row_energy_le (observationLaw θ) _
    (regularObservationLabel_measurable hk) measurable_snd
    θ.variance (responseSecondBound C) (responseFourthBound C)
    (C.densityUpper / k ^ d) (responseSecondBound_pos C).le
    (by positivity) (observationLaw_response_memLp_two hθ).integrable_sq
    (observationLaw_response_fourth_integrable hθ) (by
      simpa using observationLaw_localized_fourth_integral_le hθ MeasurableSet.univ)
  · intro c
    rw [regularObservationLabel_mass hθ hk c,
      regularObservationLabel_fiber hk c]
    exact observationLaw_localized_second_integral_le hθ (A := ((regularGridCell k hk) ⁻¹' {c})) ((measurableSet_singleton _).preimage (regular_grid_cell_measurable k hk))
  · intro c
    rw [regularObservationLabel_mass hθ hk c]
    exact regularGridProbability_cap hθ hk c

include hθ in
/-- The regression, evaluated at the observed covariate, is genuinely L². -/
theorem observationLaw_regression_memLp_two :
    MemLp (fun z => θ.regression z.1) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  apply MemLp.of_bound (hθ.2.1.comp measurable_fst).aestronglyMeasurable C.holderBound
  filter_upwards [(observationLaw_fst_measurePreserving hθ).quasiMeasurePreserving.ae
    (designLaw_cube_ae θ)] with z hz
  exact admissible_regression_value_bound hθ hz

include hθ in
theorem designLaw_regression_memLp_two :
    MemLp θ.regression 2 (designLaw θ) := by
  let := designLaw_isProbability C θ hθ
  apply MemLp.of_bound hθ.2.1.aestronglyMeasurable C.holderBound
  filter_upwards [designLaw_cube_ae θ] with x hx
  exact admissible_regression_value_bound hθ hx

include hθ in
theorem observationLaw_covariate_integral
    {g : Covariate d → ℝ} (hg : Measurable g) :
    (∫ z, g z.1 ∂observationLaw θ) = ∫ x, g x ∂designLaw θ := by
  have hh := integral_map (μ := observationLaw θ) measurable_fst.aemeasurable
    hg.aestronglyMeasurable
  rw [(observationLaw_fst_measurePreserving hθ).map_eq] at hh
  exact hh.symm

include hθ in
theorem observationLaw_localized_regression_second
    {A : Set (Covariate d)} (hA : MeasurableSet A) :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z => z.2 ^ 2) z
      ∂observationLaw θ) =
      (∫ z, (Prod.fst ⁻¹' A).indicator (fun z => θ.regression z.1 ^ 2) z
        ∂observationLaw θ) + θ.variance * (designLaw θ).real A := by
  rw [observationLaw_localized_second_integral hθ hA]
  have hh := observationLaw_covariate_integral hθ ((hθ.2.1.pow_const 2).indicator hA)
  have hc : (∫ z, (Prod.fst ⁻¹' A).indicator
      (fun z => θ.regression z.1 ^ 2) z ∂observationLaw θ) =
      ∫ x, A.indicator (fun x => θ.regression x ^ 2) x ∂designLaw θ := by
    assumption
  rw [hc, integral_indicator hA, integral_indicator hA]
  let := designLaw_isProbability C θ hθ
  rw [integral_add (designLaw_regression_memLp_two hθ).integrable_sq.restrict
      (integrable_const θ.variance), integral_const]
  simp <;> ring

include hθ in
/-- Conditional centering makes the score's population mean exactly the
same-cell squared regression increment. -/
theorem regularPairScore_mean_eq_signal :
    (∫ z, regularPairScore θ hk z
      ∂(observationLaw θ).prod (observationLaw θ)) =
      ∫ z, pairWindowScore (regularObservationLabel hk)
        (fun z => θ.regression z.1) 0 z
        ∂(observationLaw θ).prod (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  rw [regularPairScore,
    pairWindowScore_integral (observationLaw θ) _
      (regularObservationLabel_measurable hk) measurable_snd θ.variance
      (observationLaw_response_memLp_two hθ),
    pairWindowScore_integral (observationLaw θ) _
      (regularObservationLabel_measurable hk)
      (r := (fun z => θ.regression z.1)) (hθ.2.1.comp measurable_fst) 0
      (observationLaw_regression_memLp_two hθ)]
  apply Finset.sum_congr rfl
  intro c hc
  have hA : MeasurableSet ((regularGridCell k hk) ⁻¹' {c}) :=
    (measurableSet_singleton _).preimage (regular_grid_cell_measurable k hk)
  have hfirst := (by rw [observationLaw_localized_first_integral hθ hA]; have hh := observationLaw_covariate_integral hθ (hθ.2.1.indicator hA); exact hh.symm : ∫ (z : Observation d), (Prod.fst ⁻¹' regularGridCell k hk ⁻¹' {c}).indicator Prod.snd z ∂observationLaw θ = ∫ (z : Observation d), (Prod.fst ⁻¹' regularGridCell k hk ⁻¹' {c}).indicator (fun z => θ.regression z.1) z ∂observationLaw θ)
  rw [regularObservationLabel_mass hθ hk c,
    regularObservationLabel_fiber hk c, hfirst, (observationLaw_localized_regression_second hθ hA)]
  simp [regularGridProbability] <;> ring

def regularGridOscillation (C : ModelConstants d) (k : ℕ) : ℝ :=
  (2 * (d + 1) * C.holderBound) *
    (Real.sqrt d * (1 / k)) ^ elementarySmoothness C

include hθ in
theorem regularPairScore_mean_nonneg :
    0 ≤ ∫ z, regularPairScore θ hk z
      ∂(observationLaw θ).prod (observationLaw θ) := by
  rw [regularPairScore_mean_eq_signal hθ hk]
  simp [pairWindowScore] <;> positivity

include hθ in
theorem regularPairSignal_integrable :
    Integrable (pairWindowScore (regularObservationLabel hk)
      (fun z => θ.regression z.1) 0)
      ((observationLaw θ).prod (observationLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  let R := fun z : Observation d => θ.regression z.1
  have h2 := (observationLaw_regression_memLp_two hθ).integrable_sq
  apply ((h2.comp_fst _).add (h2.comp_snd _)).mono'
    (pairWindowScore_measurable _ (regularObservationLabel_measurable hk)
      (r := R) (hθ.2.1.comp measurable_fst) 0).aestronglyMeasurable
  filter_upwards [] with z
  simpa using pairWindowScore_abs_le (regularObservationLabel hk) R 0 z

include hθ in
theorem regularPairScore_mean_le :
    let jointLaw := (observationLaw θ).prod (observationLaw θ)
    (∫ z, regularPairScore θ hk z
      ∂jointLaw) ≤
      (regularGridOscillation C k ^ 2 / 2) * regularGridCollisionMass θ hk := by
  intro jointLaw
  let := observationLaw_isProbability C θ hθ
  have hcube := (observationLaw_fst_measurePreserving hθ).quasiMeasurePreserving.ae
    (designLaw_cube_ae θ)
  rw [regularPairScore_mean_eq_signal hθ hk]
  have hD := (sameLabelKernel_memLp (observationLaw θ) _
    (regularObservationLabel_measurable hk)).integrable (by norm_num)
  have hb : (∫ z, pairWindowScore (regularObservationLabel hk)
      (fun z => θ.regression z.1) 0 z
      ∂jointLaw) ≤
      ∫ z, (regularGridOscillation C k ^ 2 / 2) *
        sameLabelKernel (regularObservationLabel hk) z
        ∂jointLaw := by
    apply integral_mono_ae (regularPairSignal_integrable hθ hk)
      (hD.const_mul _)
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcube,
      Measure.quasiMeasurePreserving_snd.ae hcube] with z hz1 hz2
    by_cases he : regularObservationLabel hk z.1 = regularObservationLabel hk z.2
    · have hs := pow_le_pow_left₀ (abs_nonneg _) (regular_grid_same_cell_regression_difference hθ hk hz1 hz2 he) 2
      simp only [sq_abs] at hs
      simp [pairWindowScore, sameLabelKernel]
      bound
    · simp_all [pairWindowScore, sameLabelKernel]
  rw [integral_const_mul, sameLabelKernel_integral (observationLaw θ) _
    (regularObservationLabel_measurable hk)] at hb
  simpa only [regularObservationLabel_mass hθ hk, regularGridCollisionMass] using hb

end NearlyMinimax
