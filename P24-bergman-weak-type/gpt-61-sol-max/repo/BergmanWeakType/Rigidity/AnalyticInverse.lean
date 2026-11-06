/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Rigidity.RiemannMapping
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

variable {U V : Set ℂ} {f g : ℂ → ℂ} {x : ℂ}



open Set Filter Metric
open scoped Topology

namespace BergmanWeakType

variable (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
include hU hV hf

/-- A set-theoretic inverse of a holomorphic bijection between open complex sets is holomorphic.
Continuity follows from the open mapping theorem; isolated possible critical points are removable
singularities of the inverse. -/
theorem differentiableOn_inverse  
    (hinv : InvOn g f U V) (hgmap : MapsTo g V U) : DifferentiableOn ℂ g V := by
  have hnot {x} (hx : x ∈ U) : ¬∀ᶠ z in 𝓝 x, f z = f x := by
    intro h
    exact not_isOpen_singleton x <| isOpen_singleton_of_finite_mem_nhds x (by
      filter_upwards [h, hU.eventually_mem hx] with z hz hzU
      exact hinv.1.injOn hzU hx hz
    ) (finite_singleton x)
  have hderiv {x : ℂ} (hx : x ∈ U) : ∀ᶠ z in 𝓝[≠] x, deriv f z ≠ 0 := by
  
    rcases (hf.analyticOnNhd hU).deriv x hx |>.eventually_eq_zero_or_eventually_ne_zero
      with hzero | hne
    · have hc := analyticOrderAt_deriv_eq_top_iff_of_eq_zero
        (f := fun z ↦ f z - f x)
        ((hf.analyticAt (hU.mem_nhds hx)).sub analyticAt_const) (by simp)
      simp only [deriv_sub_const_fun, analyticOrderAt_eq_top, sub_eq_zero] at hc
      exact (hnot hx (hc.mp hzero)).elim
    · exact hne
  have hcont : ∀ y ∈ V, ContinuousAt g y := by
    intro y hy
    have hx := hgmap hy
    have hopen :=
      (hf.analyticAt (hU.mem_nhds hx)).eventually_constant_or_nhds_le_map_nhds.resolve_left
        (hnot hx)
    rw [hinv.2 hy] at hopen
    exact (tendsto_map' (tendsto_id.congr' <|
      (hU.eventually_mem hx).mono fun z hz ↦ (hinv.1 hz).symm)).mono_left hopen
  intro y hy
  apply DifferentiableAt.differentiableWithinAt
  apply AnalyticAt.differentiableAt
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ (hcont y hy)
  have hcrit := hderiv (hgmap hy)
  rw [eventually_nhdsWithin_iff] at hcrit ⊢
  filter_upwards [(hcont y hy).tendsto.eventually hcrit, hV.eventually_mem hy] with z hz hzV hzneq
  exact ((hf.differentiableAt (hU.mem_nhds (hgmap hzV))).hasDerivAt.of_local_left_inverse
    (hcont z hzV) (hz ((hinv.2.injOn.ne_iff hzV hy).mpr hzneq)) ((hV.eventually_mem hzV).mono fun w hw ↦ hinv.2 hw)).differentiableAt

theorem deriv_inverse_mul  
    (hg : DifferentiableOn ℂ g V) (hinv : InvOn g f U V) (hmap : MapsTo f U V)
     (hx : x ∈ U) : deriv g (f x) * deriv f x = 1 := by
  have hid  :=
    ((hg.differentiableAt (hV.mem_nhds (hmap hx))).hasDerivAt.comp x
    (hf.differentiableAt (hU.mem_nhds hx)).hasDerivAt).congr_of_eventuallyEq ((hU.eventually_mem hx).mono fun w hw ↦ (hinv.1 hw).symm)
  exact hid.unique (hasDerivAt_id x)


end BergmanWeakType
