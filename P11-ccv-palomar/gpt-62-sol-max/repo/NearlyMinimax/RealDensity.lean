module

public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {f : α → ℝ}

section
variable (hf : Integrable f μ) (hn : 0 ≤ᵐ[μ] f)
    (hm : 0 < ∫ x, f x ∂μ)
include hf hn hm

/-- Normalize a nonnegative integrable real density with positive mass. -/
theorem realDensity_normalized :
    (∫⁻ x, ENNReal.ofReal (f x / (∫ y, f y ∂μ)) ∂μ) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.div_const _)
    (hn.mono fun _ hx => div_nonneg hx hm.le), integral_div, div_self hm.ne', ENNReal.ofReal_one]

theorem realDensity_probability :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x / (∫ y, f y ∂μ)))) :=
  ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    realDensity_normalized hf hn hm]⟩

end

section
variable (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
include hf hn

section
variable (g : α → ℝ)

theorem integral_realDensity :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) = ∫ x, f x * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

theorem integrable_realDensity_iff :
    Integrable g (μ.withDensity (fun x => ENNReal.ofReal (f x))) ↔ Integrable (fun x => f x * g x) μ := by
  rw [integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

end

theorem integral_realDensity_div {c : ℝ}
    (hc : 0 ≤ c) (g : α → ℝ) :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x / c))) = (∫ x, f x * g x ∂μ) / c := by
  rw [integral_realDensity (hf.div_const c) (fun x => div_nonneg (hn x) hc), ← integral_div]
  simp_rw [div_mul_eq_mul_div]

end

theorem integrable_of_ae_mem_nonneg_Icc [IsFiniteMeasure μ] (hf : Measurable f)
    {a b : ℝ} (ha : 0 ≤ a) (hb : ∀ᵐ x ∂μ, f x ∈ Icc a b) : Integrable f μ :=
  (integrable_const b).mono_nonneg hf.aestronglyMeasurable
    (hb.mono fun _ hx => ha.trans hx.1) (hb.mono fun _ hx => hx.2)

theorem integral_mem_Icc_of_ae_mem_Icc [IsProbabilityMeasure μ] (hf : Integrable f μ)
    {a b : ℝ} (hb : ∀ᵐ x ∂μ, f x ∈ Icc a b) : (∫ x, f x ∂μ) ∈ Icc a b := by
  exact ⟨by simpa using integral_mono_ae (integrable_const a) hf (hb.mono fun _ hx => hx.1),
    by simpa using integral_mono_ae hf (integrable_const b) (hb.mono fun _ hx => hx.2)⟩

theorem integral_prod_nonneg_domination {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [SFinite μ] [SFinite ν] {W : α × β → ℝ} (hW : Measurable W) (hn : ∀ z, 0 ≤ W z)
    {g : α → ℝ} (hg : Integrable g μ) (h : ∀ x, (∫ y, W (x,y) ∂ν) ≤ g x)
    (hi : ∀ x, Integrable (fun y => W (x,y)) ν) :
    Integrable W (μ.prod ν) ∧ (∫ z, W z ∂μ.prod ν) ≤ ∫ x, g x ∂μ := by
  have hI : Integrable (fun x => ∫ y, W (x,y) ∂ν) μ :=
    hg.mono_nonneg hW.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      (.of_forall fun x => integral_nonneg fun y => hn (x,y)) (.of_forall h)
  have hP : Integrable W (μ.prod ν) := (integrable_prod_iff hW.aestronglyMeasurable).2
    ⟨.of_forall hi, by simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _)] using hI⟩
  exact ⟨hP, by rw [integral_prod _ hP]; exact integral_mono hI hg h⟩

end NearlyMinimax
