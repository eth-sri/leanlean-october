/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib

/-! Uniform sizes of positions and weighted charges on compact parameter sets. -/
public section
open Set
namespace DOZZ.Proofs

theorem compact_coulomb_parameter_bounds {N : ℕ}
    {S : Set (ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ))} (hS : IsCompact S) :
    ∃ Zs E : ℝ, 0 ≤ Zs ∧ 0 ≤ E ∧
      (∀ c ∈ S, ∑ j, ‖c.2.1 j‖ ≤ Zs) ∧
      (∀ c ∈ S, ∑ j, |c.1*c.2.2.1 j| + |c.1*c.2.2.2| ≤ E) ∧
      (∀ c ∈ S, ∀ j, |c.1*c.2.2.1 j| ≤ E) ∧
      (∀ c ∈ S, |c.1*c.2.2.2| ≤ E) := by
  classical
  obtain ⟨Z, hZ⟩ := hS.exists_bound_of_continuousOn
    (f := fun c => ∑ j, ‖c.2.1 j‖) (by fun_prop)
  obtain ⟨E, hE⟩ := hS.exists_bound_of_continuousOn
    (f := fun c => ∑ j, |c.1*c.2.2.1 j| + |c.1*c.2.2.2|) (by fun_prop)
  have hsum : ∀ c ∈ S, ∑ j, |c.1*c.2.2.1 j| + |c.1*c.2.2.2| ≤ max E 0 :=
    fun c hc => ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hE c hc)).trans
      (le_max_left _ _)
  refine ⟨max Z 0, max E 0, le_max_right _ _, le_max_right _ _, ?_, hsum, ?_, ?_⟩
  · exact fun c hc => ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hZ c hc)).trans
      (le_max_left _ _)
  · intro c hc j
    exact ((Finset.single_le_sum (fun k _ => abs_nonneg (c.1*c.2.2.1 k))
      (Finset.mem_univ j)).trans (le_add_of_nonneg_right (abs_nonneg _))).trans (hsum c hc)
  · intro c hc
    exact (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => abs_nonneg (c.1*c.2.2.1 j))).trans
      (hsum c hc)

end DOZZ.Proofs
