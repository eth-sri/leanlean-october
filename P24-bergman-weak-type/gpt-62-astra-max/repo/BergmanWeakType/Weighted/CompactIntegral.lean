/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Calculus
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Order.Compact

/-! # Differentiating compact families against integrable densities -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BergmanWeakType.Weighted

section
variable {X A E : Type*} [TopologicalSpace A] [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set X} (hk : IsCompact K) (hm : ∀ᵐ w ∂μ, w ∈ K)

include hk hm

theorem integrable_on_support {f : X → E} (hc : ContinuousOn f K) : Integrable f μ := by
  rw [← Measure.restrict_eq_self_of_ae_mem hm]; exact hc.integrableOn_compact hk

/-- Continuity on the support compact suffices; no extension of the integrand
across its boundary is required. -/
theorem continuousOn_average {S : Set A} {f : A → X → E} (hc : ContinuousOn f.uncurry (S ×ˢ K)) :
    ContinuousOn (fun p ↦ ∫ w, f p w ∂μ) S := by
  let := isCompact_iff_compactSpace.mp hk
  have h := continuousOn_integral_of_compact_support (μ := μ.comap ((↑) : K → X)) isCompact_univ
    (f := fun p w ↦ f p w.val) (hc.comp (f := fun z : A × K ↦ (z.1,z.2.val)) (by fun_prop)
      (s := S ×ˢ univ) (fun z hz ↦ (by simp_all))) (by simp)
  simp_all [integral_subtype_comap, hk.isClosed.measurableSet, Measure.restrict_eq_self_of_ae_mem]

/-- Differentiate an integral supported on a compact set: continuous derivatives on
one compact parameter neighborhood have a common constant majorant. -/
theorem integral_jet {ι : Type*} {S : Set A}
    {F : ι → A → X → ℝ} (hc : ∀ i, ContinuousOn (F i).uncurry (S ×ˢ K))
    {g : ℝ → A} (hg : Continuous g) {x : ℝ} (hx : g ⁻¹' S ∈ 𝓝 x) {i j k : ι}
    (h : ∀ w ∈ K, ∀ u, g u ∈ S → JetAt (fun y ↦ F i (g y) w) (fun y ↦ F j (g y) w) (F k (g u) w) u) :
    JetAt (fun y ↦ ∫ w, F i (g y) w ∂μ) (fun y ↦ ∫ w, F j (g y) w ∂μ) (∫ w, F k (g x) w ∂μ) x := by
  obtain ⟨T, ht, hs, hcT⟩ := local_compact_nhds hx
  have hi i {u : ℝ} (hu : u ∈ T) :=
    integrable_on_support hk hm ((hc i).comp (continuous_const.prodMk continuous_id).continuousOn fun _ hw ↦ ⟨hs hu,hw⟩)
  have D i j (d : ∀ w ∈ K, ∀ u, g u ∈ S → HasDerivAt (fun y ↦ F i (g y) w) (F j (g u) w) u) :
      HasDerivAt (fun y ↦ ∫ w, F i (g y) w ∂μ) (∫ w, F j (g x) w ∂μ) x := by
    obtain ⟨M,hM⟩ := ((hcT.image hg).prod hk).bddAbove_image ((hc j).mono (by grind)).norm
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le ht
      (Filter.mem_of_superset ht fun _ hu ↦ (hi i hu).1) (by simp_all [mem_of_mem_nhds]) (hi j (mem_of_mem_nhds ht)).1
      (hm.mono (by aesop)) (integrable_const M) (hm.mono (by grind))).2
  simp_all [JetAt]

end
end BergmanWeakType.Weighted
