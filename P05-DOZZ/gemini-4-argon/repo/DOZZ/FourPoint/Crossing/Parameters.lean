/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussPhysicalParameterRange
import Mathlib.Tactic

/-! # Nonresonance and the `K₂ ≠ 0` guard for ordinary half-charge crossing

The guard is the missing hypothesis of erratum K27, see docs/ERRATA-AND-DEVIATIONS.md. -/

public section
namespace DOZZ.Proofs

/-- Exchanging the finite charges changes c into the one-channel parameter. -/
theorem crossing_gammaHalf_channel_parameter γ a b c (hγ : γ ≠ 0) :
    gaussParameterC γ (γ / 2) b =
      1 + gaussParameterA γ (γ / 2) a b c +
        gaussParameterB γ (γ / 2) a b c - gaussParameterC γ (γ / 2) a := by
  unfold gaussParameterA gaussParameterB gaussParameterC Q
  field_simp
  ring

/-- The strict crossing hypotheses discharge both integer exclusions and the explicit `K₂ ≠ 0`
requirement (erratum K27, see docs/ERRATA-AND-DEVIATIONS.md) via
`gauss_physical_parameter_range`. -/
theorem crossing_gammaHalf_parameter_guards γ a ε c
    (hγ : 0 < γ) (hγ2 : γ < 2) (hε : ε < 2 / γ)
    (ha : a < Q γ) (hc : c < Q γ)
    (hs : 2 * Q γ < c + a + ε - γ / 2) :
    let A := gaussParameterA γ (γ / 2) a ε c
    let B := gaussParameterB γ (γ / 2) a ε c
    let C := gaussParameterC γ (γ / 2) a
    (∀ n : ℤ, C ≠ (n : ℝ)) ∧
      (∀ n : ℤ, C - A - B ≠ (n : ℝ)) ∧ gaussK₂ A B C ≠ 0 := by
  obtain ⟨hA, hAB, hBC, hC, hδ, hδ1, _, hK₂⟩ :=
    DOZZ.gauss_physical_parameter_range γ (γ / 2) a ε c hγ hγ2 (Or.inl rfl)
      (by linarith only [hs]) ha (by unfold Q; linarith only [hε, hγ]) hc
  dsimp only
  refine ⟨?_, ?_, hK₂.ne'⟩
  · intro n hn
    have hn0 : (0 : ℤ) < n := by exact_mod_cast (hn ▸ (lt_trans (lt_trans hA hAB) hBC))
    have hn1 : n < (1 : ℤ) := by exact_mod_cast (hn ▸ hC)
    omega
  · intro n hn
    have hn0 : (0 : ℤ) < n := by exact_mod_cast (hn ▸ hδ)
    have hn1 : n < (1 : ℤ) := by exact_mod_cast (hn ▸ hδ1)
    omega

end DOZZ.Proofs
