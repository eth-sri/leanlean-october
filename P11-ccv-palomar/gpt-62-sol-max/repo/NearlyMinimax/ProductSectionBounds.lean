module

public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory
namespace NearlyMinimax

/-- An integrable envelope for the section norms gives joint integrability. -/
theorem integrable_prod_of_section_norm_le {X Y E : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [NormedAddCommGroup E] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {f : X × Y → E} {g : Y → ℝ}
    (hm : AEStronglyMeasurable f (μ.prod ν)) (hg : Integrable g ν)
    (hi : ∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ)
    (hb : ∀ᵐ y ∂ν, (∫ x, ‖f (x, y)‖ ∂μ) ≤ g y) : Integrable f (μ.prod ν) := by
  refine (integrable_prod_iff' hm).2 ⟨hi, hg.mono' hm.norm.prod_swap.integral_prod_right' ?_⟩
  exact hb.mono fun _ h => (Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)).trans_le h

/-- For nonnegative sections, the same envelope bounds the joint integral. -/
theorem integrable_prod_and_integral_le {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : X × Y → ℝ} {g : Y → ℝ} (hm : AEStronglyMeasurable f (μ.prod ν)) (hg : Integrable g ν)
    (hs : ∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ ∧
      (∀ x, 0 ≤ f (x, y)) ∧ (∫ x, f (x, y) ∂μ) ≤ g y) :
    Integrable f (μ.prod ν) ∧ (∫ z, f z ∂μ.prod ν) ≤ ∫ y, g y ∂ν := by
  have hi := integrable_prod_of_section_norm_le hm hg (hs.mono fun _ h => h.1) (by
    filter_upwards [hs] with y h
    simpa only [Real.norm_of_nonneg (h.2.1 _)] using h.2.2)
  exact ⟨hi, (integral_prod_symm _ hi).trans_le
    (integral_mono_ae hi.integral_prod_right hg (hs.mono fun _ h => h.2.2))⟩

end NearlyMinimax
