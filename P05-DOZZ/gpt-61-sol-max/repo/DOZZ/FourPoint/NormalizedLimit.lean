/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Shared estimates for normalized spatial limits. -/
public section
open Filter Topology
namespace DOZZ.Proofs

/-- Near the punctured origin the spatial points avoid both marked points. -/
theorem eventually_punctured_zero_small :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 ∧ z ≠ 1 ∧ ‖z‖ ≤ 1 := by
  have hn : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖(0 : ℂ)‖) := (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    hn.eventually (gt_mem_nhds (by simp : ‖(0 : ℂ)‖ < 1))] with z hz hzn
  exact ⟨hz, by rintro rfl; simp at hzn, hzn.le⟩

/-- An error dominated by a vanishing normalized moment does not affect the leading limit. -/
theorem tendsto_div_of_error_bound {ι : Type*} {l : Filter ι}
    {D L F w : ι → ℝ} {Λ c S C J : ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hL : Tendsto (fun i => L i / w i) l (𝓝 Λ))
    (hF : Tendsto (fun i => F i / w i) l (𝓝 0))
    (hb : ∀ᶠ i in l, |D i - c * L i * S| ≤ C * F i * J) :
    Tendsto (fun i => D i / w i) l (𝓝 (c * Λ * S)) := by
  have herr : Tendsto (fun i => (D i - c * L i * S) / w i) l (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (by simpa using hF.const_mul (C * J))
    filter_upwards [hb] with i hi
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (hw i)]
    convert div_le_div_of_nonneg_right hi (hw i) using 1; ring
  convert herr.add ((hL.const_mul c).mul_const S) using 1
  · funext i; ring
  · simp

end DOZZ.Proofs
