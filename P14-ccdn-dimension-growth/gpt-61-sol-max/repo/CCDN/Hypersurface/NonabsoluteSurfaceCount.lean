/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Height.Box
public import CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Ideal.Height
import CCDN.Algebra.PolynomialLinearDescent
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hypersurface.CurveBoxDegreeBound
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! CCDN Corollary 4.1.4 for irreducible affine hypersurfaces in three
variables. Splitting of the full equation over any field extension gives
an auxiliary equation of degree at most d. The prime curve
components of the resulting section have total degree at most d², giving
the sharp elementary bound d²(2B+1), whatever the highest homogeneous
component. -/

public section
namespace CCDN
open MvPolynomial

/-- Linear descent of both proper factors produces a base-field auxiliary
equation vanishing at every base-field zero, with degree at most d. -/
theorem nonabsolute_affine_auxiliary {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n : ℕ}
    (f : MvPolynomial (Fin n) k) (hir : Irreducible f)
    (hred : ¬ Irreducible (map (algebraMap k K) f)) :
    ∃ q : MvPolynomial (Fin n) k,
      q.totalDegree ≤ f.totalDegree ∧ ¬ f ∣ q ∧
      ∀ x : Fin n → k, eval x f = 0 → eval x q = 0 := by
  obtain ⟨g, h, hfac, hg0, hh0, hgd, hhd⟩ := exists_proper_polynomial_factors f hir hred
  have hmapd := totalDegree_map_of_injective (algebraMap k K).injective f
  have hdegrees : g.totalDegree + h.totalDegree = f.totalDegree := by
    simp_all [totalDegree_mul_of_isDomain]
  obtain ⟨g₀, hg₀, hgd₀, hgz⟩ := exists_nonzero_polynomial_linear_descent (k := k) g hg0
  obtain ⟨h₀, hh₀, hhd₀, hhz⟩ := exists_nonzero_polynomial_linear_descent (k := k) h hh0
  refine ⟨g₀ * h₀, ?_, ?_, ?_⟩
  · grind [totalDegree_mul_of_isDomain]
  · intro hdiv
    rcases hir.prime.dvd_or_dvd hdiv with hgdiv | hhdiv
    · have he := totalDegree_le_of_dvd_of_isDomain hgdiv hg₀
      omega
    · have he := totalDegree_le_of_dvd_of_isDomain hhdiv hh₀
      omega
  · intro x hx
    have he := congrArg (algebraMap k K) hx
    rw [map_eval, hfac, eval_mul, map_zero] at he
    rw [eval_mul]
    rcases mul_eq_zero.mp he with hgzero | hhzero
    · rw [hgz x hgzero, zero_mul]
    · rw [hhz x hhzero, mul_zero]

/-- A finite union of affine curves in three-space, given by height-two primes `P` of degree
`d P`, has at most `(∑ P, d P) * (2 * B + 1)` integral points of height at most `B`. -/
theorem finite_curve_union_count_le_box_side
    (S : Finset (CCDN.CoordinateIdeal 3))
    (d : CCDN.CoordinateIdeal 3 → ℕ)
    (hcurve : ∀ P ∈ S, P.IsPrime ∧ P.height = 2 ∧ HasAffineCurveDegree P (d P))
    {B : ℝ} (hB : 0 ≤ B) :
    (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤
      (∑ P ∈ S, (d P : ℝ)) * (2 * B + 1) := by
  classical
  calc
    _ ≤ ∑ P ∈ S, (count (idealZeroLocus P) B : ℝ) := by
      exact_mod_cast count_biUnion_finset_le S idealZeroLocus B
    _ ≤ ∑ P ∈ S, (d P : ℝ) * (2 * B + 1) := by
      apply Finset.sum_le_sum
      intro P hP
      have := (hcurve P hP).1
      exact curve_count_le_degree_mul_box_side P (hcurve P hP).2.1 (hcurve P hP).2.2 hB
    _ = _ := (Finset.sum_mul _ _ _).symm

end CCDN
