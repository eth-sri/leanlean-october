module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Tactic

/-! Banach-valued fundamental theorem on a finite real interval. -/

public section

open MeasureTheory Set Filter AbsolutelyContinuousOnInterval
open scoped Topology

namespace PolyaNeumann

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Control increments of the vector primitive by those of the scalar primitive of the norm. -/
theorem absolutelyContinuousOnInterval_intervalIntegral_banach
    {f : ℝ → V} {a b c : ℝ} (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, f t) a b := by
  refine squeeze_zero' (.of_forall fun E => Finset.sum_nonneg fun _ _ => dist_nonneg) ?_
    (hf.norm.absolutelyContinuousOnInterval_intervalIntegral hc)
  rw [eventually_inf_principal]
  filter_upwards with E hE
  refine Finset.sum_le_sum fun i hi => ?_
  obtain ⟨hx, hy⟩ := hE.1 i hi
  have h₁ := hf.mono_set (uIcc_subset_uIcc hc hx)
  have h₂ := hf.mono_set (uIcc_subset_uIcc hc hy)
  rw [dist_eq_norm, Real.dist_eq, intervalIntegral.integral_interval_sub_left h₁ h₂,
    intervalIntegral.integral_interval_sub_left h₁.norm h₂.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- The actual a.e. derivative of an interval primitive. -/
theorem ae_hasDerivAt_intervalIntegral_banach
    {f : ℝ → V} {L : ℝ} (hL : 0 ≤ L) (hf : IntervalIntegrable f volume 0 L) :
    ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, f t) (f x) x := by
  filter_upwards [hf.ae_hasDerivAt_integral] with x hx h
  exact hx (uIcc_of_le hL ▸ Ioo_subset_Icc_self h) 0 left_mem_uIcc

/-- Recover an absolutely continuous function from its integrable a.e. derivative. -/
theorem eq_add_intervalIntegral_of_ac_ae_hasDerivAt {f g : ℝ → V} {L : ℝ} (hL : 0 ≤ L)
    (hf : AbsolutelyContinuousOnInterval f 0 L) (hg : IntegrableOn g (Icc 0 L))
    (hd : ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt f (g x) x) :
    ∀ θ ∈ Icc 0 L, f θ = f 0 + ∫ s in (0 : ℝ)..θ, g s := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hL).mpr hg
  let P := fun x => ∫ t in (0 : ℝ)..x, g t
  have hP := absolutelyContinuousOnInterval_intervalIntegral_banach hi left_mem_uIcc
  have hz : ∀ᵐ x, x ∈ uIcc 0 L → HasDerivAt (f - P) 0 x := by
    filter_upwards [hd, hi.ae_hasDerivAt_integral, Measure.ae_ne (volume : Measure ℝ) 0,
      Measure.ae_ne (volume : Measure ℝ) L] with x hx hD hx0 hxL h
    have hc : x ∈ Icc 0 L := uIcc_of_le hL ▸ h
    simpa using (hx ⟨hc.1.lt_of_ne hx0.symm, hc.2.lt_of_ne hxL⟩).sub (hD h 0 left_mem_uIcc)
  obtain ⟨c, hc⟩ := (hf.sub hP).const_of_ae_hasDerivAt_zero hz
  intro θ hθ
  have hθ' := hc θ (uIcc_of_le hL ▸ hθ)
  have h₀ := hc 0 left_mem_uIcc
  simpa [P, sub_eq_iff_eq_add, ← h₀] using hθ'

/-- Lipschitz special case; the derivative does not have to be bounded. -/
theorem eq_add_integral_of_ae_hasDerivAt {f g : ℝ → V} {L : ℝ} {K : NNReal}
    (hf : LipschitzOnWith K f (Icc 0 L)) (hg : IntegrableOn g (Icc 0 L))
    (hd : ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt f (g x) x) :
    ∀ θ ∈ Icc 0 L, f θ = f 0 + ∫ s in (0 : ℝ)..θ, g s := by
  intro θ hθ
  have hL := hθ.1.trans hθ.2
  rw [← uIcc_of_le hL] at hf
  exact eq_add_intervalIntegral_of_ac_ae_hasDerivAt hL hf.absolutelyContinuousOnInterval hg hd θ hθ

end PolyaNeumann
