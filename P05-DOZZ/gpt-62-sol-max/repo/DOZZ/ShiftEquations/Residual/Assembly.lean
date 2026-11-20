/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import DOZZ.ShiftEquations.DualFirstCase.Assembly

public import DOZZ.ShiftEquations.Residual.Calibration
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.BrownianPath
import DOZZ.Roots.CubeContinuation

/-! # The DOZZ formula for irrational γ²

In the near-`Q` cube the first-case construction gives both shifts on a single meromorphic
representative. Their incommensurable periods make the quotient constant, and calibration
at the zero mode fixes this constant to one. Charge continuation extends the identity to
all pole-free extended triples. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The source's sufficiently small cube can always be chosen in the first-case regime. -/
private theorem roots_small_cube (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ η : ℝ, 0 < η ∧ η ≤ γ / 4 ∧ Q γ - 2 * η > γ ∧ 3 * η < Q γ := by
  have hQ := gamma_lt_Q hγ hγ2
  let η := min ((Q γ - γ) / 8) (γ / 4)
  have hη : 0 < η := lt_min (by linarith only [hQ]) (by positivity)
  have hη1 : η ≤ (Q γ - γ) / 8 := min_le_left _ _
  exact ⟨η, hη, min_le_right _ _, by linarith only [hQ, hη1], by linarith only [hQ, hγ, hη1]⟩

/-- Charge continuation of the calibrated formula when the squared coupling is irrational. -/
theorem dozz_main_irrational {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (U : ℂ → ℂ) (hU : IsUpsilon γ U) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (a b c : ℝ) (hα : ExtendedSeiberg3 γ a b c) (hs : ∀ n : ℕ, sExp γ a b c ≠ -(n : ℝ)) :
    (structureConstant P M γ μ a b c : ℂ) = dozzFormula γ μ U a b c := by
  obtain ⟨η₀, hη₀0, hη₀4, hη₀γ, hη₀3⟩ := roots_small_cube γ hγ hγ2
  exact roots_structureConstant_of_unitVolume_value P M γ μ a b c hμ hs _
    (roots_unitVolume_of_cube P X M γ μ η₀ hγ hγ2 hμ hη₀0 hη₀3 U hU hX hM (by
    intro a b c ha1 ha2 hb1 hb2 hc1 hc2
    obtain ⟨-, -, -, -, h, hh, C, -, hCm, -, hCv, -, -, -, hdual, hfirst⟩ :=
      structureConstant_dual_shift_strip_first_case_joint P X M γ μ η₀ hγ hγ2 hγirr hμ
        ⟨hη₀0, hη₀γ⟩ hX hM b c ⟨hb1, hb2⟩ ⟨hc1, hc2⟩ hη₀4
    obtain ⟨c₀, hc₀⟩ := slice_constant_of_joint P M hγ hγ2 hγirr hμ ⟨hη₀0, hη₀γ⟩
      ⟨hb1, hb2⟩ ⟨hc1, hc2⟩ hU ⟨h, hh, C, hCm, hCv, hfirst, hdual⟩
    exact slice_identity_calibrated P X M hγ hγ2 hμ hX hM hU ⟨hη₀0, hη₀γ⟩ ⟨hb1, hb2⟩
      ⟨hc1, hc2⟩ hc₀ a (by linarith) ha2) a b c hα hs)

end DOZZ.Proofs

end
