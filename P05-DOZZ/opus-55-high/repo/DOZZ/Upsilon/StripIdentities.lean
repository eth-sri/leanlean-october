/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu

/-!
# DOZZ — elementary strip identities for the defining Υ integral

These lemmas concern the literal integral definition on the strip. They do not
use or assert an entire continuation.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace DOZZ.Proofs

/-- At the midpoint, the defining integrand vanishes pointwise. -/
theorem upsilonLog_center (γ : ℝ) :
    upsilonLog γ (Q γ / 2) = 0 := by
  simp [upsilonLog, upsilonLogIntegrand]

/-- Every entire continuation has the normalization `Υ(Q/2) = 1`. -/
theorem IsUpsilon.center {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hU : IsUpsilon γ U) :
    U (Q γ / 2) = 1 := by
  have hQ : 0 < Q γ := by
    unfold Q
    positivity
  have hleft : 0 < (Q γ / 2 : ℂ).re := by
    simp_all
  have hright : (Q γ / 2 : ℂ).re < Q γ := by
    simp_all
  rw [hU.2 _ hleft hright, upsilonLog_center, Complex.exp_zero]

/-- Literal reflection of the logarithmic integral across the strip midpoint. -/
theorem upsilonLog_reflect (γ : ℝ) (z : ℂ)
    (_hz₀ : 0 < z.re) (_hzQ : z.re < Q γ) :
    upsilonLog γ ((Q γ : ℂ) - z) = upsilonLog γ z := by
  have hcenter :
      (Q γ / 2) - ((Q γ) - z) = -((Q γ / 2) - z) := by
    ring
  change
    (∫ t in Ioi 0, upsilonLogIntegrand γ _ t ∂volume) =
      ∫ t in Ioi 0, upsilonLogIntegrand γ z t ∂volume
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [upsilonLogIntegrand, upsilonLogIntegrand, hcenter]
  simp only [neg_sq, neg_mul, Complex.sinh_neg]

end DOZZ.Proofs
