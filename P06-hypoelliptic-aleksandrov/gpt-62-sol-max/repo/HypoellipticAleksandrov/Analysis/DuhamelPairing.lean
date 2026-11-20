module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Integrating a source-time family of weak identities -/

@[expose] public section

namespace HypoellipticAleksandrov.Analysis

open MeasureTheory Set Filter
open scoped Topology

/-- Continuity of an integral with moving lower time endpoint. The slice at the endpoint
is immaterial, and the remaining slices have a common integrable bound. -/
theorem continuousWithinAt_integral_Ioc {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {S : Set X} {p₀ : X} {t : X → ℝ} (ht : Continuous t) {T a b C : ℝ} {f : X → ℝ → ℝ}
    (hm : ∀ p, Measurable (f p)) (hC : 0 ≤ C) (hb : ∀ p r, |f p r| ≤ C)
    (hz : ∀ p r, r ∉ Icc a b → f p r = 0)
    (hc : ∀ r, t p₀ < r → r ≤ T → ContinuousWithinAt (fun p => f p r) S p₀) :
    ContinuousWithinAt (fun p => ∫ r in Ioc (t p) T, f p r) S p₀ := by
  simp_rw [← integral_indicator measurableSet_Ioc]
  refine continuousWithinAt_of_dominated
    (bound := (Icc a b).indicator (fun _ => C))
    (.of_forall fun p => ((hm p).indicator measurableSet_Ioc).aestronglyMeasurable)
    (.of_forall fun p => .of_forall fun r => ?_)
    ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))) ?_
  · by_cases hr : r ∈ Icc a b
    · by_cases h : r ∈ Ioc (t p) T <;> simp [hr, h, Real.norm_eq_abs, hb, hC]
    · simp [hr, hz p r hr, indicator_apply]
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (t p₀))] with r hr
    by_cases hT : r ≤ T
    · rcases lt_or_gt_of_ne (show r ≠ t p₀ from hr) with h | h
      · have he : (fun p => (Ioc (t p) T).indicator (f p) r) =ᶠ[𝓝[S] p₀] fun _ => 0 := by
          filter_upwards [mem_nhdsWithin_of_mem_nhds
            ((isOpen_lt continuous_const ht).mem_nhds h)] with p hp
          exact indicator_of_notMem (fun hr => (not_lt_of_ge hp.le) hr.1) _
        exact continuousWithinAt_const.congr_of_eventuallyEq he
          (indicator_of_notMem (fun hr => (not_lt_of_ge h.le) hr.1) _)
      · have he : (fun p => (Ioc (t p) T).indicator (f p) r) =ᶠ[𝓝[S] p₀] fun p => f p r := by
          filter_upwards [mem_nhdsWithin_of_mem_nhds
            ((isOpen_lt ht continuous_const).mem_nhds h)] with p hp
          exact indicator_of_mem (show r ∈ Ioc (t p) T from ⟨hp, hT⟩) _
        exact (hc r h hT).congr_of_eventuallyEq he (indicator_of_mem (show r ∈ Ioc (t p₀) T from ⟨h, hT⟩) _)
    · simp only [show ∀ p, (Ioc (t p) T).indicator (f p) r = 0 from
        fun p => indicator_of_notMem (fun hr => hT hr.2) _]
      exact continuousWithinAt_const

/-- Integrate the slice identities and swap the order of integration. The
    source-time integrand is bounded and vanishes outside a finite interval. -/
theorem integral_duhamel_of_slice {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    (t : X → ℝ) (ht : Measurable t) (A : ℝ × X → ℝ) (L V : X → ℝ) (G : ℝ × Y → ℝ)
    (hA : Measurable A) (hL : Integrable L μ) (hG : Integrable G ((volume : Measure ℝ).prod ν))
    {a b C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, |A z| ≤ C) (hzero : ∀ z, z.1 ∉ Icc a b → A z = 0)
    (hV : ∀ q, V q = ∫ r in Ioi (t q), A (r, q))
    (per : ∀ r, (∫ q, {q | t q < r}.indicator (fun q => A (r, q) * L q) q ∂μ) +
      ∫ w, G (r, w) ∂ν = 0) :
    (∫ q, V q * L q ∂μ) = -∫ z, G z ∂((volume : Measure ℝ).prod ν) := by
  let F (z : ℝ × X) := {z | t z.2 < z.1}.indicator (fun z => A z * L z.2) z
  let B (r : ℝ) := (Icc a b).indicator (fun _ => C) r
  have hB : Integrable B := (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hF : Integrable F ((volume : Measure ℝ).prod μ) := by
    refine (hB.mul_prod hL.norm).mono' (((hA.aestronglyMeasurable.mul hL.aestronglyMeasurable.comp_snd).indicator
      (measurableSet_lt (ht.comp measurable_snd) measurable_fst))) (.of_forall fun z => ?_)
    have hAb : ‖A z‖ ≤ B z.1 := by
      by_cases hz : z.1 ∈ Icc a b
      · simpa [B, hz, Real.norm_eq_abs] using hbound z
      · simp [B, hz, hzero z hz]
    by_cases hz : t z.2 < z.1
    · simpa [F, hz, norm_mul] using mul_le_mul_of_nonneg_right hAb (norm_nonneg (L z.2))
    · simpa [F, hz] using mul_nonneg ((norm_nonneg _).trans hAb) (norm_nonneg (L z.2))
  have hq (q : X) : (∫ r, F (r, q)) = V q * L q := by
    have e : (fun r => F (r, q)) = (Ioi (t q)).indicator (fun r => A (r, q) * L q) := by
      funext r
      by_cases h : t q < r <;> simp [F, h]
    rw [e, integral_indicator measurableSet_Ioi, integral_mul_const, hV]
  have hr (r : ℝ) : (∫ q, F (r, q) ∂μ) = -∫ w, G (r, w) ∂ν := by
    have e : (fun q => F (r, q)) = fun q => {q | t q < r}.indicator (fun q => A (r, q) * L q) q := by
      funext q
      by_cases h : t q < r <;> simp [F, h]
    change (∫ q, (fun q => F (r, q)) q ∂μ) = _
    rw [e]
    exact eq_neg_of_add_eq_zero_left (per r)
  calc
    _ = ∫ q, (∫ r, F (r, q)) ∂μ := integral_congr_ae (.of_forall fun q => (hq q).symm)
    _ = ∫ r, ∫ q, F (r, q) ∂μ := (integral_integral_swap hF).symm
    _ = -∫ r, ∫ w, G (r, w) ∂ν := by simp_rw [hr, integral_neg]
    _ = _ := congrArg Neg.neg (integral_prod G hG).symm

end HypoellipticAleksandrov.Analysis
