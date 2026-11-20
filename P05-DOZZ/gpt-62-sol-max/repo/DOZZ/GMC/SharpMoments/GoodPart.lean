/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Comparing two weighted masses on a region where the weights are close

On a measurable region where two weights are bounded and uniformly close away from one point, the
difference of the two weighted masses, against two finite measures without an atom at that point,
is at most the uniform distance times the mass of the region plus the difference of the integrals
of one fixed bounded function against the two measures. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem setLIntegral_ne_top_of_bound {μ : Measure ℂ} [IsFiniteMeasure μ]
    {S : Set ℂ} (hS : MeasurableSet S) {f : ℂ → ℝ≥0∞} {L : ℝ}
    (h : ∀ x ∈ S, f x ≤ ENNReal.ofReal L) : (∫⁻ x in S, f x ∂μ) ≠ ∞ := by
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal L * μ S) (by finiteness) ?_
  rw [← setLIntegral_const]
  exact setLIntegral_mono' hS h

/-- The difference of two weighted masses on a region where the weights are uniformly close. -/
theorem goodPart_ofReal_abs_le (μr μ : Measure ℂ) [IsFiniteMeasure μr] [IsFiniteMeasure μ]
    (Good : Set ℂ) (hGood : MeasurableSet Good) (G F : ℂ → ℝ≥0∞) (hG : Measurable G)
    (hF : Measurable F) (L e : ℝ) (he : 0 ≤ e)
    (hbound : ∀ x ∈ Good, G x ≤ ENNReal.ofReal L ∧ F x ≤ ENNReal.ofReal L ∧
      |(G x).toReal - (F x).toReal| ≤ e) :
    ENNReal.ofReal |(∫⁻ x in Good, G x ∂μr).toReal - (∫⁻ x in Good, F x ∂μ).toReal| ≤
      ENNReal.ofReal e * μr Good +
        ENNReal.ofReal |∫ x, Good.indicator (fun x => (F x).toReal) x ∂μr -
          ∫ x, Good.indicator (fun x => (F x).toReal) x ∂μ| := by
  have h (ν : Measure ℂ) [IsFiniteMeasure ν] {f : ℂ → ℝ≥0∞} (hf : Measurable f)
      (hb : ∀ x ∈ Good, f x ≤ ENNReal.ofReal L) :
      IntegrableOn (fun x => (f x).toReal) Good ν ∧
        (∫ x in Good, (f x).toReal ∂ν) = (∫⁻ x in Good, f x ∂ν).toReal := by
    have ht := setLIntegral_ne_top_of_bound (μ := ν) hGood hb
    exact ⟨integrable_toReal_of_lintegral_ne_top hf.aemeasurable ht,
      integral_toReal hf.aemeasurable (ae_lt_top' hf.aemeasurable ht)⟩
  obtain ⟨hGi, hGr⟩ := h μr hG fun x hx => (hbound x hx).1
  obtain ⟨hFi, -⟩ := h μr hF fun x hx => (hbound x hx).2.1
  obtain ⟨-, hF0⟩ := h μ hF fun x hx => (hbound x hx).2.1
  rw [← hGr, ← hF0, integral_indicator hGood, integral_indicator hGood]
  have ht : |∫ x in Good, (G x).toReal ∂μr - ∫ x in Good, (F x).toReal ∂μr| ≤
      e * (μr Good).toReal := by
    rw [← integral_sub hGi hFi, ← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top _ _)
      ((ae_restrict_mem hGood).mono fun x hx => by simpa using (hbound x hx).2.2)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (∫ x in Good, (G x).toReal ∂μr) (∫ x in Good, (F x).toReal ∂μr) (∫ x in Good, (F x).toReal ∂μ)
  simp only [Real.norm_eq_abs] at htri
  refine (ENNReal.ofReal_le_ofReal (htri.trans (add_le_add_left ht _))).trans
    (ENNReal.ofReal_add_le.trans ?_)
  rw [ENNReal.ofReal_mul he, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end DOZZ.Proofs
