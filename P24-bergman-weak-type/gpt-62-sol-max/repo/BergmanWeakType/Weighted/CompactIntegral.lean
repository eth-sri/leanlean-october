/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Order.Compact

/-! # Integration and differentiation of compactly supported families -/

public section

open MeasureTheory Set Filter

namespace BergmanWeakType

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K)

include hK hμ

lemma integrable_compact_slice {Y E : Type*} [TopologicalSpace Y] [NormedAddCommGroup E]
    {S : Set Y} {F : Y → X → E} (hF : ContinuousOn (Function.uncurry F) (S ×ˢ K))
    {y : Y} (hy : y ∈ S) : Integrable (F y) μ := by
  rw [← Measure.restrict_eq_self_of_ae_mem hμ]
  exact (hF.uncurry_left y hy).integrableOn_compact hK

/-- Compactness of the support gives a local dominating bound for a continuous family. -/
theorem continuousOn_integral_of_compact_support {Y E : Type*}
    [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set Y} {F : Y → X → E} (hF : ContinuousOn (Function.uncurry F) (S ×ˢ K)) :
    ContinuousOn (fun z ↦ ∫ w, F z w ∂μ) S := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine (_root_.continuousOn_integral_of_compact_support (μ := μ.comap Subtype.val)
    (f := fun y (w : K) ↦ F y w) isCompact_univ
    (hF.comp (f := fun p : Y × K ↦ (p.1, (p.2 : X))) (by fun_prop) (fun p hp ↦ ⟨hp.1, p.2.2⟩))
    (by simp)).congr fun y _ ↦ ?_
  change _ = ∫ w : K, F y w ∂(μ.comap Subtype.val)
  rw [integral_subtype_comap hK.measurableSet, Measure.restrict_eq_self_of_ae_mem hμ]

/-- A continuous derivative on a compact source family can be passed under the integral. -/
theorem hasDerivAt_integral_of_compact {S : Set ℝ} (hS : IsOpen S) {x : ℝ} (hx : x ∈ S)
    {F F' : ℝ → X → ℝ}
    (hF : ContinuousOn (fun p : ℝ × X ↦ F p.1 p.2) (S ×ˢ K))
    (hF' : ContinuousOn (fun p : ℝ × X ↦ F' p.1 p.2) (S ×ˢ K))
    (hd : ∀ w ∈ K, ∀ u ∈ S, HasDerivAt (fun v ↦ F v w) (F' u w) u) :
    HasDerivAt (fun u ↦ ∫ w, F u w ∂μ) (∫ w, F' x w ∂μ) x := by
  obtain ⟨U, hU, hxU, hsub⟩ := exists_compact_subset hS hx
  have hU' := mem_interior_iff_mem_nhds.mp hxU
  obtain ⟨M, hM⟩ := (hU.prod hK).exists_bound_of_continuousOn (hF'.mono (prod_mono hsub Subset.rfl))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU'
    (Filter.mem_of_superset hU' fun u hu ↦ (integrable_compact_slice hK hμ hF (hsub hu)).aestronglyMeasurable)
    (integrable_compact_slice hK hμ hF hx) (integrable_compact_slice hK hμ hF' hx).aestronglyMeasurable
    (hμ.mono fun w hw u hu ↦ hM (u, w) ⟨hu, hw⟩)
    (integrable_const M) (hμ.mono fun w hw u hu ↦ hd w hw u (hsub hu))).2

end BergmanWeakType
