/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.Brownian.TwoSidedReflectionMassMomentRange
public import DOZZ.Brownian.Lateral.ReflectionInverse
import Mathlib.Tactic
import DOZZ.Brownian.TwoSided.TwoSidedReflectionMassMomentRange
/-! # The actual supplied reflection mass has the moments needed for Pareto integration -/
public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- Every strict subcritical order of the actual supplied reflection mass is finite. -/
theorem reflected_reflection_mass_moment_lt_top
    (γ α q : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hα : α < Q γ) (hData : IsReflectionData P γ α B Z) (hq : q < 4 / γ ^ 2) :
    (∫⁻ ω, twoSidedReflectionMass γ B Z ω ^ q ∂P) < ⊤ := by
  obtain ⟨C, hC, hb⟩ := DOZZ.Proofs.twoSidedReflectionMass_moment_range P
    {γ} {Q γ - α} {q} isCompact_singleton isCompact_singleton isCompact_singleton
    (fun _ => B) (fun _ => Z) (by
      aesop)
    (by simp_all)
    (by simp_all)
  exact (hb γ (mem_singleton _) _ (mem_singleton _) q (mem_singleton _)).trans_lt hC
section
variable (γ α : ℝ) (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < Q γ) (hData : IsReflectionData P γ α B Z)
include hγ hγ₂ hα hData

/-- The first moment required by the explicit Pareto remainder is finite for every gamma in (0,2). -/
theorem reflected_reflection_mass_first_moment
    :
    (∫⁻ ω, twoSidedReflectionMass γ B Z ω ∂P) < ⊤ := by
  have hc : 1 < 4 / γ ^ 2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hγ)]
    nlinarith
  simpa using
    reflected_reflection_mass_moment_lt_top P γ α 1 B Z hα hData hc

/-- The actual reflection mass is positive and finite on one full-measure event. -/
theorem reflected_reflection_mass_positive_finite_ae
    :
    ∀ᵐ ω ∂P, 0 < twoSidedReflectionMass γ B Z ω ∧ twoSidedReflectionMass γ B Z ω < ⊤ := by
  have hB := conditionedPair_aemeasurable P B _ hData.1
  have hneg := reflected_reflection_mass_moment_lt_top P γ α (-1) B Z hα hData (lt_trans (by norm_num : (-1 : ℝ) < 0) (by positivity))
  have hp := twoSidedReflectionMass_pos_ae_of_negative_moment P γ (-1) B Z hB hData.2.1
    (by norm_num) hneg
  have hf := twoSidedReflectionMass_finite_ae_of_positive_moment P γ 1 B Z hB hData.2.1
    zero_lt_one (by simpa using (reflected_reflection_mass_first_moment P γ α B Z hγ hγ₂ hα hData))
  simp_all

end

end

end DOZZ.Proofs
