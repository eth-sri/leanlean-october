module

public import NearlyMinimax.HighDesignEnergySeries


@[expose] public section

/-! True selected normalized-design score energies. The squared likelihood
ratio cancels against the genuine response and design density, leaving
the source fixed denominator constant and the raw spatial numerator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem fintype_probability_pi_restrict_withDensity {κ α : Type*} [Fintype κ]
    [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ≥0∞} (hf : Measurable f) (hprob : IsProbabilityMeasure (μ.withDensity f))
    {A : Set α} (hA : MeasurableSet A) :
    Measure.pi (fun _ => (μ.withDensity f).restrict A) =
      (Measure.pi (fun _ : κ => μ.restrict A)).withDensity (fun x => ∏ i, f (x i)) := by
  rw [← Measure.restrict_pi_pi (fun _ => μ.withDensity f) (fun _ => A),
    fintype_probability_pi_withDensity hf hprob,
    restrict_withDensity (MeasurableSet.univ_pi (fun _ => hA)),
    Measure.restrict_pi_pi]

section
variable {κ α : Type*} [Fintype κ] {m pMinus cMass : ℝ} (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    (hm : 0 < m) (p : α → ℝ) (q : α → Fin 3 → ℝ) (hq : ∀ x y, 0 ≤ q x y) (R : (κ → α) → (κ → Fin 3) → ℝ)
    (x : κ → α)

def selectedRawLikelihood (y : κ → Fin 3) : ℝ :=
  (∏ i, p (x i)) * ∏ i, q (x i) (y i)

def selectedConditionalScoreEnergy : ℝ :=
  ∑ y, (∏ i, q (x i) (y i)) * (R x y / selectedRawLikelihood p q x y) ^ 2

def selectedRawSquareEnergy : ℝ :=
  ∑ y, (R x y) ^ 2

theorem selected_raw_likelihood_positive (y : κ → Fin 3)
    (hp : ∀ i, 0 < p (x i)) (hq : ∀ i, 0 < q (x i) (y i)) :
    0 < selectedRawLikelihood p q x y :=
  mul_pos (Finset.prod_pos (fun i _ => hp i)) (Finset.prod_pos (fun i _ => hq i))

include hm in
theorem selected_score_density_cancel
    (hp : ∀ i, 0 < p (x i)) (hq : ∀ i y, 0 < q (x i) y) :
    (∏ i, p (x i) / m) * selectedConditionalScoreEnergy p q R x =
      ∑ y,
        (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2 := by
  unfold selectedConditionalScoreEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.prod_div_distrib]
  simp
  grind [selectedRawLikelihood]

include hpMinus hcMass in
theorem selected_raw_inverse_floor
    (hm : pMinus ≤ m) (p : α → ℝ) (q : α → Fin 3 → ℝ)
    (x : κ → α) (y : κ → Fin 3)
    (hp : ∀ i, pMinus ≤ p (x i)) (hq : ∀ i, cMass ≤ q (x i) (y i)) :
    (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ ≤
      highFixedScoreDenominator pMinus cMass ^ Fintype.card κ := by
  let minus := pMinus ^ 2 * cMass
  have hfac i : minus ≤ m * (p (x i) * q (x i) (y i)) := by
    have hpq := mul_le_mul (hp i) (hq i) hcMass.le (hpMinus.le.trans (hp i))
    linarith [mul_le_mul hm hpq (mul_nonneg hpMinus.le hcMass.le) (hpMinus.le.trans hm)]
  have hprod : (minus) ^ Fintype.card κ ≤
      m ^ Fintype.card κ * selectedRawLikelihood p q x y := by
    calc
      _ = ∏ _i, minus := by simp
      _ ≤ _ :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hfac i)
      _ = _ := by unfold selectedRawLikelihood; rw [Finset.prod_mul_distrib]; simp [Finset.prod_mul_distrib]
  have hleft : 0 < (minus) ^ Fintype.card κ := by positivity
  unfold highFixedScoreDenominator
  rw [inv_pow]
  gcongr <;> assumption

end

variable {κ α : Type*} [Fintype κ] [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {A : Set α}

theorem normalized_selected_score_density_cancel_ae (μ : Measure α) [IsProbabilityMeasure μ]
    {A : Set α} (hA : MeasurableSet A) {m : ℝ} (hm : 0 < m)
    {p : α → ℝ} {q : α → Fin 3 → ℝ}
    (R : (κ → α) → (κ → Fin 3) → ℝ)
    (hp : ∀ x ∈ A, 0 < p x) (hq : ∀ x ∈ A, ∀ y, 0 < q x y) :
    (fun x => (∏ i, ENNReal.ofReal (p (x i) / m)).toReal *
      selectedConditionalScoreEnergy p q R x) =ᵐ[Measure.pi (fun _ => μ.restrict A)]
      (fun x => ∑ y,
        (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2) := by
  have hmem : ∀ᵐ x ∂Measure.pi (fun _ : κ => μ.restrict A), ∀ i, x i ∈ A :=
    ae_all_iff.mpr (fun i => Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem hA))
  filter_upwards [hmem] with x hx
  have he : (∏ i, ENNReal.ofReal (p (x i) / m)).toReal = ∏ i, p (x i) / m := by
    rw [ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i hi
    exact ENNReal.toReal_ofReal (div_nonneg (hp _ (hx i)).le hm.le)
  grind [selected_score_density_cancel]

theorem normalized_selected_score_energy_integral_eq_raw (hA : MeasurableSet A) {m : ℝ} (hm : 0 < m)
    {p : α → ℝ} (hpMeas : Measurable p) {q : α → Fin 3 → ℝ}
    (R : (κ → α) → (κ → Fin 3) → ℝ)
    (hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (p x / m))))
    (hp : ∀ x ∈ A, 0 < p x) (hq : ∀ x ∈ A, ∀ y, 0 < q x y) :
    (∫ x, selectedConditionalScoreEnergy p q R x
      ∂Measure.pi (fun _ => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) =
      ∫ x, ∑ y,
        (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2
          ∂Measure.pi (fun _ => μ.restrict A) := by
  have hf : Measurable (fun x => ENNReal.ofReal (p x / m)) :=
    ENNReal.measurable_ofReal.comp (hpMeas.div_const m)
  rw [fintype_probability_pi_restrict_withDensity hf hprob hA]
  have hfP : Measurable (fun x : κ → α => ∏ i, ENNReal.ofReal (p (x i) / m)) :=
    Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))
  have he := integral_withDensity_eq_integral_toReal_smul
    (μ := Measure.pi (fun _ => μ.restrict A)) hfP
    (Filter.Eventually.of_forall (fun _ => ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)))
    (selectedConditionalScoreEnergy p q R)
  rw [he]
  apply integral_congr_ae
  exact normalized_selected_score_density_cancel_ae μ hA hm R hp hq

theorem normalized_selected_score_energy_integrable_bound (hA : MeasurableSet A) {m pMinus cMass : ℝ}
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hm : pMinus ≤ m)
    {p : α → ℝ} (hpMeas : Measurable p) {q : α → Fin 3 → ℝ}
    (hqMeas : ∀ y, Measurable (fun x => q x y))
    {R : (κ → α) → (κ → Fin 3) → ℝ} (hR : ∀ y, Measurable (fun x => R x y))
    (hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (p x / m))))
    (hp : ∀ x ∈ A, pMinus ≤ p x) (hq : ∀ x ∈ A, ∀ y, cMass ≤ q x y)
    (hRaw : Integrable (selectedRawSquareEnergy R) (Measure.pi (fun _ => μ.restrict A))) :
    Integrable (selectedConditionalScoreEnergy p q R)
      (Measure.pi (fun _ => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) ∧
    (∫ x, selectedConditionalScoreEnergy p q R x
      ∂Measure.pi (fun _ => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) ≤
      highFixedScoreDenominator pMinus cMass ^ Fintype.card κ *
        ∫ x, selectedRawSquareEnergy R x ∂Measure.pi (fun _ => μ.restrict A) := by
  have hm0  := hpMinus.trans_le hm
  have hpp x hx  := hpMinus.trans_le (hp x hx)
  have hqp x hx y  := hcMass.trans_le (hq x hx y)
  let W  := fun x => ∑ y,
    (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2
  have hWMeas : Measurable W := by
    apply Finset.measurable_sum
    intro y hy
    unfold selectedRawLikelihood
    fun_prop
  have hmem : ∀ᵐ x ∂Measure.pi (fun _ : κ => μ.restrict A), ∀ i, x i ∈ A :=
    ae_all_iff.mpr (fun i => Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem hA))
  have hWbound : ∀ᵐ x ∂Measure.pi (fun _ => μ.restrict A),
      0 ≤ W x ∧ W x ≤ highFixedScoreDenominator pMinus cMass ^ Fintype.card κ * selectedRawSquareEnergy R x := by
    filter_upwards [hmem] with x hx
    constructor
    · apply Finset.sum_nonneg
      intro y hy
      positivity [selected_raw_likelihood_positive p q x y (fun i => hpp _ (hx i)) (fun i => hqp _ (hx i) (y i))]
    · unfold W selectedRawSquareEnergy
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_right
        (selected_raw_inverse_floor hpMinus hcMass hm p q x y
          (fun i => hp _ (hx i)) (fun i => hq _ (hx i) _)) (sq_nonneg _)
  have hJ := hRaw.const_mul (highFixedScoreDenominator pMinus cMass ^ Fintype.card κ)
  have hWI : Integrable W (Measure.pi (fun _ => μ.restrict A)) := by
    apply hJ.mono' hWMeas.aestronglyMeasurable
    filter_upwards [hWbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  constructor
  · have hf : Measurable (fun x => ENNReal.ofReal (p x / m)) :=
      ENNReal.measurable_ofReal.comp (hpMeas.div_const m)
    rw [fintype_probability_pi_restrict_withDensity hf hprob hA]
    apply (integrable_withDensity_iff_integrable_smul' (Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i)))
      (Filter.Eventually.of_forall (fun _ => ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)))).mpr
    exact hWI.congr (normalized_selected_score_density_cancel_ae μ hA hm0 R hpp hqp).symm
  rw [normalized_selected_score_energy_integral_eq_raw hA hm0 hpMeas R hprob hpp hqp]
  calc
    _ ≤ _ :=
      integral_mono_ae hWI hJ (hWbound.mono (fun x hx => hx.2))
    _ = _ := integral_const_mul _ _

end NearlyMinimax
