/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Residual.Calibration
public import DOZZ.ShiftEquations.DualFirstCase.Assembly
import DOZZ.Roots.CubeContinuation

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

theorem unitVolume_residual_factor_eq_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (M : Ω → Measure ℂ) (γ μ η : ℝ) U
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ ∧ 3 * η < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hU : IsUpsilon γ U) :
    ∀ α₁ α₂ α₃ : ℝ,
      Q γ - η < α₁ → α₁ < Q γ →
      Q γ - η < α₂ → α₂ < Q γ →
      Q γ - η < α₃ → α₃ < Q γ →
        (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ) =
          ((μ : ℂ) ^ (sExp γ α₁ α₂ α₃ : ℂ) /
            Complex.Gamma (sExp γ α₁ α₂ α₃ : ℂ)) *
              dozzFormula γ μ U (α₁ : ℂ) (α₂ : ℂ) (α₃ : ℂ) := by
  obtain ⟨hη0, hηγ, hη3⟩ := hη
  set η₀ : ℝ := min η (γ / 4)
  have : η₀ ≤ η := min_le_left _ _
  have hη₀0 : 0 < η₀ := lt_min hη0 (by positivity)
  have hη₀γ : Q γ - 2 * η₀ > γ := by linarith
  intro α₁ α₂ α₃ h1 h2 h3 h4 h5 h6
  exact roots_unitVolume_of_cube P X M γ μ η₀ hγ hγ2 hμ hη₀0 (by linarith) U hU hX hM (by intro a b c ha1 ha2 hb1 hb2 hc1 hc2; obtain ⟨c₀, hc₀⟩ := slice_constant_of_joint P M hγ hγ2 hγirr hμ ⟨hη₀0, hη₀γ⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩ hU (structureConstant_dual_shift_strip_first_case_joint P X M γ μ η₀ hγ hγ2 hγirr hμ ⟨hη₀0, hη₀γ⟩ hX hM b c ⟨hb1, hb2⟩ ⟨hc1, hc2⟩ (min_le_right _ _)); exact slice_identity_calibrated P X M hγ hγ2 hμ hX hM hU ⟨hη₀0, hη₀γ⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩ hc₀ a (by linarith) ha2) α₁ α₂ α₃
    (roots_extended_cube hγ hη3 h1 h2 h3 h4 h5 h6)
    (fun n _ => by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have : 0 < sExp γ α₁ α₂ α₃ := div_pos (by linarith) hγ
      linarith)

end DOZZ.Proofs

end
