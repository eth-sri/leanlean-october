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

theorem gaussParameterSeriesTerm_sum (a b c z : ℂ) :
    ordinaryHypergeometric a b c z =
      ∑' n : ℕ, gaussParameterSeriesTerm (a, b, c) z n := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp [gaussParameterSeriesTerm, smul_eq_mul, mul_assoc]

/-- The scalar multiplier from the `n`th parameterized Gauss term to its successor. -/
noncomputable def gaussParameterSeriesRatio
    (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  (((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) * z) /
    ((n + 1 : ℂ) * ((n : ℂ) + p.2.2))

/-- Parameters away from denominator poles form an open subset of the three-parameter space. -/
def gaussParameterPoleFreeDomain : Set (ℂ × ℂ × ℂ) :=
  {p | ∀ n : ℕ, p.2.2 ≠ -(n : ℂ)}

private theorem gaussNegNatCastRange_isClosed :
    IsClosed (Set.range (fun n : ℕ => -(n : ℂ))) := by
  have hIso : Isometry (fun n : ℕ => -(n : ℂ)) := by
    apply Isometry.of_dist_eq
    intro m n
    calc
      dist (-(m : ℂ)) (-(n : ℂ)) = dist (m : ℂ) (n : ℂ) := by simp
      _ = dist (m : ℤ) (n : ℤ) := Complex.isometry_intCast.dist_eq m n
      _ = dist m n := by norm_cast
  exact hIso.isClosedEmbedding.isClosed_range

theorem gaussParameterPoleFreeDomain_isOpen :
    IsOpen gaussParameterPoleFreeDomain := by
  have hpre : gaussParameterPoleFreeDomain =
      (fun p : ℂ × ℂ × ℂ => p.2.2) ⁻¹'
        (Set.range (fun n : ℕ => -(n : ℂ)))ᶜ := by
    ext p
    simp [gaussParameterPoleFreeDomain, eq_comm]
  rw [hpre]
  exact gaussNegNatCastRange_isClosed.isOpen_compl.preimage
    (continuous_snd.comp continuous_snd)

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
  have hCinv := hC.inv hCne
  have hcoeff : DifferentiableOn ℂ
      (fun p : ℂ × ℂ × ℂ => ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n) U := by
    fun_prop (disch := positivity)
  apply hcoeff.mul_const

/-- Successive parameterized terms obey the pointwise Gauss coefficient recurrence. -/
theorem gaussParameterSeriesTerm_recurrence (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ)
    (hc : p.2.2 ≠ -(n : ℂ)) :
    gaussParameterSeriesTerm p z (n + 1) =
      gaussParameterSeriesRatio p z n * gaussParameterSeriesTerm p z n := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hp : (n : ℂ) + p.2.2 ≠ 0 := by grind
  rw [gaussParameterSeriesRatio, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hn hp)]
  simp only [gaussParameterSeriesTerm, pow_succ]
  linear_combination (z ^ n * z) *
    ordinaryHypergeometricCoefficient_gauss_recurrence p.1 p.2.1 p.2.2 n hc

end DOZZ.Proofs
