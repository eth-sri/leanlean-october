/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Roots.ChargeGeometry
public import DOZZ.Roots.FormulaLine
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
/-! # Regularity at pole-free extended charges -/
@[expose] public section
open Complex Set
namespace DOZZ.Proofs
/-- Every denominator factor of the DOZZ expression is nonzero at finite extended charges. -/
theorem roots_dozz_denominator_ne_zero {γ a b c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {U : ℂ → ℂ} (hU : IsUpsilon γ U) (h : ExtendedSeiberg3 γ a b c)
    (hs : ∀ n : ℕ, sExp γ a b c ≠ -(n : ℝ)) :
    roots_dozz_denominator γ U a b c ≠ 0 := by
  unfold roots_dozz_denominator
  obtain ⟨ht1, ht2, ht3⟩ := roots_extended_triangle hγ h
  obtain ⟨ha, hb, hc⟩ := roots_extended_positive hγ h
  have hu (x : ℝ) (hx : 0 < x) (hxQ : x < Q γ) : U (x : ℂ) ≠ 0 := by
    rw [hU.2 (x : ℂ) hx hxQ]
    exact Complex.exp_ne_zero _
  have h0 := roots_upsilon_zeroMode_ne_zero hγ hγ2 hU h hs
  have h1 := hu ((a + b + c) / 2 - a) (by linarith only [ht1]) (by linarith only [h.2.1, h.2.2.1, ha])
  have h2 := hu ((a + b + c) / 2 - b) (by linarith only [ht2]) (by linarith only [h.1, h.2.2.1, hb])
  have h3 := hu ((a + b + c) / 2 - c) (by linarith only [ht3]) (by linarith only [h.1, h.2.1, hc])
  norm_cast at h0 h1 h2 h3 ⊢
  positivity
/-- The normalized DOZZ expression is analytic along a charge curve at each finite extended triple. -/
theorem roots_formula_line_analyticAt {γ μ : ℝ} {U : ℂ → ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) (hU : IsUpsilon γ U)
    (A : Fin 3 → ℂ → ℂ) (z : ℂ) (hA : ∀ i, AnalyticAt ℂ (A i) z)
    (a b c : ℝ) (h0 : A 0 z = a) (h1 : A 1 z = b) (h2 : A 2 z = c)
    (hα : ExtendedSeiberg3 γ a b c) (hs : ∀ n : ℕ, sExp γ a b c ≠ -(n : ℝ)) :
    AnalyticAt ℂ (fun w => ((μ : ℂ) ^ ((A 0 w + A 1 w + A 2 w - 2 * Q γ) / γ) /
      Complex.Gamma ((A 0 w + A 1 w + A 2 w - 2 * Q γ) / γ)) *
        dozzFormula γ μ U (A 0 w) (A 1 w) (A 2 w)) z := by
  obtain ⟨hnorm, hnum, hden⟩ := roots_formula_line_factors hγ hγ2 hμ hU A z hA
  exact hnorm.mul (hnum.div hden (by
    rw [h0, h1, h2]
    exact roots_dozz_denominator_ne_zero hγ hγ2 hU hα hs))
end DOZZ.Proofs
