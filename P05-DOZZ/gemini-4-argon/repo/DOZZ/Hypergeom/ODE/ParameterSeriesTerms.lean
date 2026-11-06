/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.SeriesRecurrence

/-! Parameter-dependent terms of the ordinary Gauss series. -/

@[expose] public section

open Nat Polynomial

namespace DOZZ.Proofs

/-- The `n`th ordinary Gauss series term, packaged as a function of the three parameters. -/
noncomputable def gaussParameterSeriesTerm
    (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n * z ^ n

theorem gaussParameterSeriesTerm_sum a b c z :
    ordinaryHypergeometric a b c z =
      ∑' n : ℕ, gaussParameterSeriesTerm (a, b, c) z n := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp [gaussParameterSeriesTerm, smul_eq_mul, mul_assoc]

/-- The parameter series term is holomorphic wherever its denominator Pochhammer factor is
nonzero. -/
theorem gaussParameterSeriesTerm_differentiableOn
    {U} (hU : ∀ p ∈ U, ∀ k : ℕ, p.2.2 ≠ -(k : ℂ))
    z n :
    DifferentiableOn ℂ (fun p => gaussParameterSeriesTerm p z n) U := by
  change DifferentiableOn ℂ
    (fun p : ℂ × ℂ × ℂ =>
      ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n * z ^ n) U
  exact (show DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n) U by change DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => (n !⁻¹ : ℂ) * (ascPochhammer ℂ n).eval p.1 * (ascPochhammer ℂ n).eval p.2.1 * ((ascPochhammer ℂ n).eval p.2.2)⁻¹) U; exact (((differentiableOn_const _).mul (by fun_prop)).mul (by fun_prop)).mul ((show DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => (ascPochhammer ℂ n).eval p.2.2) U by fun_prop).inv (by intro p hp; exact ordinaryHypergeometric_pochhammer_denominator_ne_zero n (hU p hp)))).mul_const _

/-- Successive parameterized terms obey the pointwise Gauss coefficient recurrence. -/
theorem gaussParameterSeriesTerm_recurrence (p : ℂ × ℂ × ℂ) z (n : ℕ)
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) :
    ((n + 1 : ℂ) * ((n : ℂ) + p.2.2)) * gaussParameterSeriesTerm p z (n + 1) =
      ((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) * z *
        gaussParameterSeriesTerm p z n := by
  rw [gaussParameterSeriesTerm, gaussParameterSeriesTerm, pow_succ]
  calc
    ((n + 1 : ℂ) * ((n : ℂ) + p.2.2)) *
        (ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 (n + 1) * (z ^ n * z))
        = (((n + 1 : ℂ) * ((n : ℂ) + p.2.2)) *
            ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 (n + 1)) * z ^ n * z := by ring
    _ = (((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) *
          ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n) * z ^ n * z := by
      rw [(ordinaryHypergeometricCoefficient_gauss_recurrence p.1 p.2.1 p.2.2 n hc)]
    _ = ((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) * z *
          (ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n * z ^ n) := by ring

end DOZZ.Proofs
