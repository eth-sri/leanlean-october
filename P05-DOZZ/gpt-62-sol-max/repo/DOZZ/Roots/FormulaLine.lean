/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.ShiftEquations.Quotient.Divisors
import DOZZ.Brownian.Reflection.RtheorAnalytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
/-! # Meromorphic DOZZ expressions along analytic charge lines -/
@[expose] public section
open Complex Set
namespace DOZZ.Proofs
/-- The product of the four Upsilon factors in the denominator of the DOZZ formula. -/
noncomputable def roots_dozz_denominator (γ : ℝ) (U : ℂ → ℂ) (a b c : ℂ) : ℂ :=
  U ((a + b + c - 2 * Q γ) / 2) * U ((a + b + c) / 2 - a) *
    U ((a + b + c) / 2 - b) * U ((a + b + c) / 2 - c)

section
variable {γ μ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) (hU : IsUpsilon γ U)
  (A : Fin 3 → ℂ → ℂ)
include hγ hγ2 hμ hU

/-- Along an analytic charge line the normalized prefactor, numerator and denominator are
analytic; the only division needing a local nonvanishing condition is by the Upsilon product. -/
theorem roots_formula_line_factors (z : ℂ) (hA : ∀ i, AnalyticAt ℂ (A i) z) :
    (AnalyticAt ℂ (fun w => (μ : ℂ) ^ ((A 0 w + A 1 w + A 2 w - 2 * Q γ) / γ) /
      Gamma ((A 0 w + A 1 w + A 2 w - 2 * Q γ) / γ)) z) ∧
    (AnalyticAt ℂ (fun w =>
      ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^
        ((2 * Q γ - (A 0 w + A 1 w + A 2 w)) / γ) *
        (deriv U 0 * U (A 0 w) * U (A 1 w) * U (A 2 w))) z) ∧
    (AnalyticAt ℂ (fun w => roots_dozz_denominator γ U (A 0 w) (A 1 w) (A 2 w)) z) := by
  have hsum : AnalyticAt ℂ (fun w => A 0 w + A 1 w + A 2 w) z := ((hA 0).add (hA 1)).add (hA 2)
  have hshift : AnalyticAt ℂ (fun w => A 0 w + A 1 w + A 2 w - 2 * Q γ) z :=
    hsum.sub analyticAt_const
  have hs := hshift.div_const (c := (γ : ℂ))
  have hu {f : ℂ → ℂ} (hf : AnalyticAt ℂ f z) : AnalyticAt ℂ (fun w => U (f w)) z :=
    (hU.1.analyticAt (f z)).comp hf
  have hh := hsum.div_const (c := (2 : ℂ))
  refine ⟨?_, ?_, (((hu (hshift.div_const (c := 2))).mul (hu (hh.sub (hA 0)))).mul
    (hu (hh.sub (hA 1)))).mul (hu (hh.sub (hA 2)))⟩
  · exact (analyticAt_const.cpow hs (ofReal_mem_slitPlane.mpr hμ)).fun_mul
            (differentiable_one_div_Gamma.analyticAt _ |>.comp hs)
  · exact (analyticAt_const.cpow ((analyticAt_const.sub hsum).div_const)
      (ofReal_mem_slitPlane.mpr (dozzFormula_base_pos hγ hγ2 hμ))).mul
      (((analyticAt_const.mul (hu (hA 0))).mul (hu (hA 1))).mul (hu (hA 2)))

/-- The normalized formula is meromorphic along every entire analytic charge curve. -/
theorem roots_formula_line_meromorphic (hA : ∀ i, Differentiable ℂ (A i)) :
    MeromorphicOn (fun z : ℂ =>
      ((μ : ℂ) ^ ((A 0 z + A 1 z + A 2 z - 2 * Q γ) / γ) /
        Complex.Gamma ((A 0 z + A 1 z + A 2 z - 2 * Q γ) / γ)) *
          dozzFormula γ μ U (A 0 z) (A 1 z) (A 2 z)) univ := by
  intro z _
  obtain ⟨hnorm, hnum, hden⟩ := roots_formula_line_factors hγ hγ2 hμ hU A z
    (fun i => (hA i).analyticAt z)
  exact hnorm.meromorphicAt.fun_mul (hnum.meromorphicAt.fun_div hden.meromorphicAt)

end
end DOZZ.Proofs
