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

section
variable {κ α : Type*} [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ≥0∞) (hf : Measurable f) (hprob : IsProbabilityMeasure (μ.withDensity f))
include hf hprob

theorem fintype_probability_pi_restrict_withDensity
    (A : Set α) (hA : MeasurableSet A) :
    Measure.pi (fun _ : κ => (μ.withDensity f).restrict A) =
      (Measure.pi (fun _ : κ => μ.restrict A)).withDensity (fun x => ∏ i, f (x i)) := by
  rw [← Measure.restrict_pi_pi (fun _ : κ => μ.withDensity f) (fun _ => A),
    fintype_probability_pi_withDensity μ f hf hprob,
    restrict_withDensity (MeasurableSet.univ_pi (fun _ => hA)),
    Measure.restrict_pi_pi]

end

def selectedRawLikelihood {κ α : Type*} [Fintype κ]
    (p : α → ℝ) (q : α → Fin 3 → ℝ) (x : κ → α) (y : κ → Fin 3) : ℝ :=
  (∏ i, p (x i)) * ∏ i, q (x i) (y i)

def selectedConditionalScoreEnergy {κ α : Type*} [Fintype κ]
    (p : α → ℝ) (q : α → Fin 3 → ℝ)
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α) : ℝ :=
  ∑ y : κ → Fin 3, (∏ i, q (x i) (y i)) * (R x y / selectedRawLikelihood p q x y) ^ 2

def selectedRawSquareEnergy {κ α : Type*} [Fintype κ]
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α) : ℝ :=
  ∑ y : κ → Fin 3, (R x y) ^ 2

section
variable {κ α : Type*} [Fintype κ]

section
variable (p : α → ℝ) (q : α → Fin 3 → ℝ)

theorem selected_conditional_score_energy_nonneg (hq : ∀ x y, 0 ≤ q x y)
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α) :
    0 ≤ selectedConditionalScoreEnergy p q R x :=
  Finset.sum_nonneg (fun y _ => mul_nonneg (Finset.prod_nonneg (fun i _ => hq _ _)) (sq_nonneg _))

theorem selected_raw_likelihood_positive (x : κ → α) (y : κ → Fin 3)
    (hp : ∀ i, 0 < p (x i)) (hq : ∀ i, 0 < q (x i) (y i)) :
    0 < selectedRawLikelihood p q x y :=
  mul_pos (Finset.prod_pos (fun i _ => hp i)) (Finset.prod_pos (fun i _ => hq i))

end

theorem selected_score_density_cancel
    (m : ℝ) (p : α → ℝ) (q : α → Fin 3 → ℝ)
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α)
    (hp : ∀ i, 0 < p (x i)) (hq : ∀ i y, 0 < q (x i) y) :
    (∏ i, p (x i) / m) * selectedConditionalScoreEnergy p q R x =
      ∑ y : κ → Fin 3,
        (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2 := by
  unfold selectedConditionalScoreEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have hpP : (∏ i, p (x i)) ≠ 0 := ne_of_gt (Finset.prod_pos (fun i _ => hp i))
  have hqP : (∏ i, q (x i) (y i)) ≠ 0 := ne_of_gt (Finset.prod_pos (fun i _ => hq i (y i)))
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  unfold selectedRawLikelihood
  grind

theorem selected_raw_inverse_floor
    (m pMinus cMass : ℝ) (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    (hm : pMinus ≤ m) (p : α → ℝ) (q : α → Fin 3 → ℝ)
    (x : κ → α) (y : κ → Fin 3)
    (hp : ∀ i, pMinus ≤ p (x i)) (hq : ∀ i, cMass ≤ q (x i) (y i)) :
    (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ ≤
      highFixedScoreDenominator pMinus cMass ^ Fintype.card κ := by
  have hfac (i : κ) : pMinus ^ 2 * cMass ≤ m * (p (x i) * q (x i) (y i)) := by
    have hp0 := hpMinus.le.trans (hp i)
    have hpq := mul_le_mul (hp i) (hq i) hcMass.le hp0
    have hh := mul_le_mul hm hpq (mul_nonneg hpMinus.le hcMass.le) (hpMinus.le.trans hm)
    nlinarith
  have hprod : (pMinus ^ 2 * cMass) ^ Fintype.card κ ≤
      m ^ Fintype.card κ * selectedRawLikelihood p q x y := by
    calc
      _ = ∏ _i : κ, pMinus ^ 2 * cMass := by simp
      _ ≤ ∏ i, m * (p (x i) * q (x i) (y i)) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hfac i)
      _ = _ := by unfold selectedRawLikelihood; simp [Finset.prod_mul_distrib]
  have hleft : 0 < (pMinus ^ 2 * cMass) ^ Fintype.card κ := by positivity
  unfold highFixedScoreDenominator
  rw [inv_pow] <;> gcongr

section
variable [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (A : Set α) (hA : MeasurableSet A)
include hA

section
variable (m : ℝ) (hm : 0 < m)
    (p : α → ℝ)
include hm

theorem normalized_selected_score_density_cancel_ae (q : α → Fin 3 → ℝ)
    (R : (κ → α) → (κ → Fin 3) → ℝ)
    (hp : ∀ x ∈ A, 0 < p x) (hq : ∀ x ∈ A, ∀ y, 0 < q x y) :
    (fun x => (∏ i, ENNReal.ofReal (p (x i) / m)).toReal *
      selectedConditionalScoreEnergy p q R x) =ᵐ[Measure.pi (fun _ : κ => μ.restrict A)]
      (fun x => ∑ y : κ → Fin 3,
        (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2) := by
  filter_upwards [ae_pi_forall (ι := κ) (ae_restrict_mem (μ := μ) hA)] with x hx
  have he : (∏ i, ENNReal.ofReal (p (x i) / m)).toReal = ∏ i, p (x i) / m := by
    rw [ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i hi
    exact ENNReal.toReal_ofReal (div_nonneg (hp _ (hx i)).le hm.le)
  rw [he]
  apply selected_score_density_cancel <;> solve_by_elim


end

theorem normalized_selected_score_energy_integrable_bound (m pMinus cMass : ℝ)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hm : pMinus ≤ m)
    (p : α → ℝ) (hpMeas : Measurable p) (q : α → Fin 3 → ℝ)
    (hqMeas : ∀ y, Measurable (fun x => q x y))
    (R : (κ → α) → (κ → Fin 3) → ℝ) (hR : ∀ y, Measurable (fun x => R x y))
    (hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (p x / m))))
    (hp : ∀ x ∈ A, pMinus ≤ p x) (hq : ∀ x ∈ A, ∀ y, cMass ≤ q x y)
    (hRaw : Integrable (selectedRawSquareEnergy R) (Measure.pi (fun _ : κ => μ.restrict A))) :
    Integrable (selectedConditionalScoreEnergy p q R)
      (Measure.pi (fun _ : κ => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) ∧
    (∫ x, selectedConditionalScoreEnergy p q R x
      ∂Measure.pi (fun _ : κ => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) ≤
      highFixedScoreDenominator pMinus cMass ^ Fintype.card κ *
        ∫ x, selectedRawSquareEnergy R x ∂Measure.pi (fun _ : κ => μ.restrict A) := by
  have hm0 : 0 < m := hpMinus.trans_le hm
  have hpp (x : α) (hx : x ∈ A) : 0 < p x := hpMinus.trans_le (hp x hx)
  have hqp (x : α) (hx : x ∈ A) (y : Fin 3) : 0 < q x y := hcMass.trans_le (hq x hx y)
  let W : (κ → α) → ℝ := fun x => ∑ y : κ → Fin 3,
    (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2
  have hWMeas : Measurable W := by
    apply Finset.measurable_sum
    intro y hy
    unfold selectedRawLikelihood
    fun_prop
  have hWbound : ∀ᵐ x ∂Measure.pi (fun _ : κ => μ.restrict A),
      0 ≤ W x ∧ W x ≤ highFixedScoreDenominator pMinus cMass ^ Fintype.card κ * selectedRawSquareEnergy R x := by
    filter_upwards [ae_pi_forall (ae_restrict_mem (μ := μ) hA)] with x hx
    constructor
    · apply Finset.sum_nonneg
      intro y hy
      have hL := selected_raw_likelihood_positive p q x y (fun i => hpp _ (hx i))
        (fun i => hqp _ (hx i) (y i))
      apply mul_nonneg <;> positivity
    · unfold W selectedRawSquareEnergy
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_right
        (selected_raw_inverse_floor m pMinus cMass hpMinus hcMass hm p q x y
          (fun i => hp _ (hx i)) (fun i => hq _ (hx i) (y i))) (sq_nonneg _)
  have hJ := hRaw.const_mul (highFixedScoreDenominator pMinus cMass ^ Fintype.card κ)
  have hWI : Integrable W (Measure.pi (fun _ : κ => μ.restrict A)) := by
    apply hJ.mono' hWMeas.aestronglyMeasurable
    filter_upwards [hWbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hf : Measurable (fun x => ENNReal.ofReal (p x / m)) := by fun_prop
  let μ₀ := Measure.pi (fun _ : κ => μ.restrict A)
  let f : (κ → α) → ℝ≥0∞ := fun x => ∏ i, ENNReal.ofReal (p (x i) / m)
  have hfP : Measurable f := Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))
  have hfin : ∀ᵐ x ∂μ₀, f x < ⊤ := Filter.Eventually.of_forall fun _ =>
    ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
  have he := normalized_selected_score_density_cancel_ae μ A hA m hm0 p q R hpp hqp
  rw [fintype_probability_pi_restrict_withDensity μ _ hf hprob A hA]
  change Integrable (selectedConditionalScoreEnergy p q R) (μ₀.withDensity f) ∧ _
  refine ⟨(integrable_withDensity_iff_integrable_smul' hfP hfin).mpr (hWI.congr he.symm), ?_⟩
  calc
    _ = ∫ x, W x ∂μ₀ := (integral_withDensity_eq_integral_toReal_smul hfP hfin _).trans (integral_congr_ae he)
    _ ≤ ∫ x, highFixedScoreDenominator pMinus cMass ^ Fintype.card κ * selectedRawSquareEnergy R x ∂μ₀ :=
      integral_mono_ae hWI hJ (hWbound.mono fun _ hx => hx.2)
    _ = _ := integral_const_mul _ _

end

end

end NearlyMinimax
