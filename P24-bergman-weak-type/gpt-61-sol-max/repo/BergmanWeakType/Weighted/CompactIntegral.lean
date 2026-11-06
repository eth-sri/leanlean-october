/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Differentiating compact families against integrable densities -/




open MeasureTheory Set Real


namespace BergmanWeakType.Weighted

theorem measurable_circleAverage {Y : Type*} [MeasurableSpace Y]
    {ρ : Y → ℝ} {F : Y → ℂ → ℝ} (hρ : Measurable ρ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun y ↦ circleAverage (F y) 0 (ρ y)) := by
  simp [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le]
  exact measurable_const.mul ((hF.comp (measurable_fst.prodMk
    (circleMap.continuous.measurable.comp ((hρ.comp measurable_fst).prodMk measurable_snd)))).stronglyMeasurable.integral_prod_right'
    ).measurable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {K : Set X} (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K)

include hK hμ

def integrable_mul_of_continuousOn_compact {E : Type*} [RCLike E] {f g : X → E}
    (hf : Integrable f μ) (hg : ContinuousOn g K) := by
  simpa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] using
    hf.integrableOn.continuousOn_mul hg hK

theorem continuousOn_integral_mul_of_compact {Y E : Type*} [RCLike E] [TopologicalSpace Y] {S : Set Y} {f : X → E}
    (hf : Integrable f μ) {F : Y → X → E} (hF : ContinuousOn (fun p : Y × X ↦ F p.1 p.2) (S ×ˢ K)) :
    ContinuousOn (fun z ↦ ∫ w, F z w * f w ∂μ) S :=
  by
  let := isCompact_iff_compactSpace.mp hK
  have h :=
    continuousOn_integral_bilinear_of_locally_integrable_of_compact_support (ContinuousLinearMap.mul ℝ E)  (f := fun y (w : K) ↦ F y w)  isCompact_univ
      (hF.comp (f := fun p : Y × K ↦ (p.1, (p.2 : X))) (by fun_prop) (fun p hp ↦ ⟨hp.1, p.2.property⟩)) (by simp)
      ((integrableOn_iff_comap_subtypeVal hK.isClosed.measurableSet).mp hf.integrableOn).integrableOn
  apply h.congr
  intro y hy
  simpa [Measure.restrict_eq_self_of_ae_mem hμ, mul_comm] using
    (integral_subtype_comap (μ := μ) hK.isClosed.measurableSet _).symm

/-- Continuous kernel derivatives on a compact parameter cylinder can be integrated against any
integrable density. Compactness supplies the common domination needed by differentiation. -/
theorem hasDerivAt_integral_mul_of_continuousOn_nhds {S : Set ℝ}
    {x } (hSx : S ∈ nhds x) {f : X → ℝ}
    (hf : Integrable f μ) {F F' : ℝ → X → ℝ}
    (hF : ContinuousOn (fun p : ℝ × X ↦ F p.1 p.2) (S ×ˢ K))
    (hF' : ContinuousOn (fun p : ℝ × X ↦ F' p.1 p.2) (S ×ˢ K))
    (hderiv : ∀ w ∈ K, ∀ u ∈ S, HasDerivAt (fun v ↦ F v w) (F' u w) u) :
    HasDerivAt (fun u ↦ ∫ w, F u w * f w ∂μ) (∫ w, F' x w * f w ∂μ) x := by
  obtain ⟨T, hTx, hsub, hT⟩ := local_compact_nhds hSx
  have hx := mem_of_mem_nhds hSx
  obtain ⟨M, hM⟩ := (hT.prod hK).bddAbove_image
    (hF'.mono (prod_mono hsub Subset.rfl)).norm
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
     (F' := fun u w ↦ F' u w * f w) hTx ?_
    (integrable_mul_of_continuousOn_compact hK hμ hf (hF.uncurry_left x hx))
    (integrable_mul_of_continuousOn_compact hK hμ hf (hF'.uncurry_left x hx)).aestronglyMeasurable
     ?_ (hf.norm.const_mul M) ?_).2
  · exact Filter.mem_of_superset hTx fun u hu ↦
      (integrable_mul_of_continuousOn_compact hK hμ hf (hF.uncurry_left u (hsub hu))).aestronglyMeasurable
  · exact hμ.mono fun w hw u hu ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hM ⟨(u, w), ⟨hu, hw⟩, rfl⟩) (norm_nonneg _)
  · exact hμ.mono fun w hw u hu ↦ (hderiv w hw u (hsub hu)).mul_const _

end BergmanWeakType.Weighted
