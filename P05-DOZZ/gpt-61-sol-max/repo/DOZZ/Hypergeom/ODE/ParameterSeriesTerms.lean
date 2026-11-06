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

variable (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ)

include p z n in
/-- The `n`th ordinary Gauss series term, packaged as a function of the three parameters. -/
noncomputable def gaussParameterSeriesTerm
     : ℂ :=
  ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n * z ^ n

theorem gaussParameterSeriesTerm_sum (a b c z : ℂ) :
    ordinaryHypergeometric a b c z =
      ∑' n : ℕ, gaussParameterSeriesTerm (a, b, c) z n := by
  rw [ordinaryHypergeometric_eq_tsum]
  continuity

/-- The parameter series term is holomorphic wherever its denominator Pochhammer factor is
nonzero. -/
theorem gaussParameterSeriesTerm_differentiableOn
    {U : Set (ℂ × ℂ × ℂ)} (hU : ∀ p ∈ U, ∀ k : ℕ, p.2.2 ≠ -(k : ℂ))
    (z : ℂ) (n : ℕ) :
    DifferentiableOn ℂ (fun p => gaussParameterSeriesTerm p z n) U := by
  have hA : DifferentiableOn ℂ
      (fun p : ℂ × ℂ × ℂ => (ascPochhammer ℂ n).eval p.1) U := by
    fun_prop
  have hB : DifferentiableOn ℂ
      (fun p : ℂ × ℂ × ℂ => (ascPochhammer ℂ n).eval p.2.1) U := by
    fun_prop
  have hC : DifferentiableOn ℂ
      (fun p : ℂ × ℂ × ℂ => (ascPochhammer ℂ n).eval p.2.2) U := by
    fun_prop
  have hCne : ∀ p ∈ U, (ascPochhammer ℂ n).eval p.2.2 ≠ 0 := by
    intro p hp
    exact ordinaryHypergeometric_pochhammer_denominator_ne_zero n (hU p hp)

  have hcoeff : DifferentiableOn ℂ
      (fun p : ℂ × ℂ × ℂ => ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n) U := by
    fun_prop (disch := positivity)
  exact DifferentiableOn.mul_const hcoeff (z ^ n)

include p z n in
/-- Successive parameterized terms obey the pointwise Gauss coefficient recurrence. -/
theorem gaussParameterSeriesTerm_recurrence
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) :
    ((n + 1 : ℂ) * ((n : ℂ) + p.2.2)) * gaussParameterSeriesTerm p z (n + 1) =
      ((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) * z *
        gaussParameterSeriesTerm p z n := by
  rw [gaussParameterSeriesTerm, gaussParameterSeriesTerm, pow_succ]
  have hcoeff := ordinaryHypergeometricCoefficient_gauss_recurrence
    p.1 p.2.1 p.2.2 n hc
  grind

end DOZZ.Proofs
