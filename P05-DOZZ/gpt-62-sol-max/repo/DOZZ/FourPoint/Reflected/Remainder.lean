/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.IsComplexLittleOAtZero
import Mathlib.Tactic

/-! # Remainder calculus at the punctured complex origin -/

public section

open Filter Topology

namespace DOZZ.Proofs

/-- Approaching the origin on the positive real axis also approaches it in the punctured plane. -/
theorem tendsto_ofReal_nhdsGT_zero :
    Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa only [Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_ne_zero] using ht.ne'

/-- A real-valued normalized radial limit restricts to the positive real axis. -/
theorem radial_limit_along_reals {f : ℂ → ℝ} {κ L : ℝ}
    (h : Tendsto (fun z => f z / ‖z‖ ^ κ) (𝓝[≠] (0 : ℂ)) (𝓝 L)) :
    Tendsto (fun t : ℝ => f (t : ℂ) / t ^ κ) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  refine (h.comp tendsto_ofReal_nhdsGT_zero).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [Function.comp_apply, Complex.norm_real, Real.norm_of_nonneg ht.le]

/-- The complex norm convention agrees with a signed real remainder limit. -/
theorem isComplexLittleOAtZero_ofReal_iff (κ : ℝ) (f : ℂ → ℝ) :
    IsComplexLittleOAtZero κ (fun z => (f z : ℂ)) ↔
      Tendsto (fun z => f z / ‖z‖ ^ κ)
        (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
  unfold IsComplexLittleOAtZero
  conv_rhs => rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg
    (norm_nonneg _) _)]

/-- Addition preserves the little-o remainder convention. -/
theorem IsComplexLittleOAtZero.add {κ : ℝ} {f g : ℂ → ℂ}
    (hf : DOZZ.IsComplexLittleOAtZero κ f) (hg : DOZZ.IsComplexLittleOAtZero κ g) :
    DOZZ.IsComplexLittleOAtZero κ (fun z => f z + g z) := by
  unfold DOZZ.IsComplexLittleOAtZero at hf hg ⊢
  apply squeeze_zero (fun z => div_nonneg (norm_nonneg _) (Real.rpow_nonneg
    (norm_nonneg _) _))
  · exact fun z =>
      Trans.trans (div_le_div_of_nonneg_right (norm_add_le (f z) (g z)) (Real.rpow_nonneg (norm_nonneg z) κ))
        (add_div ‖f z‖ ‖g z‖ (‖z‖ ^ κ))
  · simpa only [add_zero] using hf.add hg

/-- A strictly higher power of the radius is negligible at the reflected scale. -/
theorem reflected_radius_power_ratio_tendsto (κ η : ℝ) (hη : κ < η) :
    Tendsto (fun z : ℂ => ‖z‖ ^ η / ‖z‖ ^ κ)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
  have he : 0 < η - κ := sub_pos.mpr hη
  have hn := (tendsto_norm_zero (E := ℂ)).mono_left
    (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  apply (hn.rpow_const_nhds_zero he).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact Real.rpow_sub (norm_pos_iff.mpr hz) η κ

/-- Uniform power bounds suffice for every decorrelation and buffer remainder. -/
theorem isComplexLittleOAtZero_of_norm_le_power {κ η C : ℝ} {f : ℂ → ℂ}
    (hη : κ < η)
    (hb : ∀ᶠ z in nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}, ‖f z‖ ≤ C * ‖z‖ ^ η) :
    DOZZ.IsComplexLittleOAtZero κ f := by
  unfold DOZZ.IsComplexLittleOAtZero
  have ht := (reflected_radius_power_ratio_tendsto κ η hη).const_mul C
  apply squeeze_zero' (Filter.Eventually.of_forall (fun z =>
    div_nonneg (norm_nonneg (f z)) (Real.rpow_nonneg (norm_nonneg z) κ)))
  · filter_upwards [hb] with z hz
    calc
      ‖f z‖ / ‖z‖ ^ κ ≤ (C * ‖z‖ ^ η) / ‖z‖ ^ κ :=
        div_le_div_of_nonneg_right hz (Real.rpow_nonneg (norm_nonneg z) κ)
      _ = C * (‖z‖ ^ η / ‖z‖ ^ κ) := mul_div_assoc _ _ _
  · simpa only [mul_zero] using ht

end DOZZ.Proofs
