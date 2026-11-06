/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.Height.Box
import CCDN.Hilbert.AffineCurveDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Height
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

namespace CCDN
section
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
  obtain ⟨g, h, hfac, hg0, hh0, hgd, hhd, hdegrees⟩ :=
    exists_map_factorization (totalDegree_pos_of_irreducible hir) hred
  obtain ⟨g₀, hg₀, hgd₀, hgz⟩ := exists_nonzero_polynomial_linear_descent (k := k) g hg0
  obtain ⟨h₀, hh₀, hhd₀, hhz⟩ := exists_nonzero_polynomial_linear_descent (k := k) h hh0
  refine ⟨g₀ * h₀, ?_, ?_, ?_⟩
  · rw [totalDegree_mul_of_isDomain hg₀ hh₀]
    omega
  · intro hdiv
    rcases hir.prime.dvd_or_dvd hdiv with hgdiv | hhdiv
    · have he := totalDegree_le_of_dvd_of_isDomain hgdiv hg₀
      omega
    · have he := totalDegree_le_of_dvd_of_isDomain hhdiv hh₀
      omega
  · intro x hx
    have he := congrArg (algebraMap k K) hx
    rw [map_eval, hfac, eval_mul, map_zero] at he
    aesop

/-- A finite union of affine curves in three-space, given by height-two primes `P` of degree
`d P`, has at most `(∑ P, d P) * (2 * B + 1)` integral points of height at most `B`. -/
theorem finite_curve_union_count_le_box_side
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (d : Ideal (CoordinatePolynomial 3) → ℕ)
    (hcurve : ∀ P ∈ S, P.IsPrime ∧ P.height = 2 ∧ HasAffineCurveDegree P (d P))
    {B : ℝ} (hB : 0 ≤ B) :
    (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤
      (∑ P ∈ S, (d P : ℝ)) * (2 * B + 1) := by
  induction S using Finset.induction_on with
  | empty => simp [count, integralPoints]
  | @insert P S hPS ih =>
    have hP := hcurve P (Finset.mem_insert_self _ _)
    have : P.IsPrime := hP.1
    have hS := ih (fun Q hQ => hcurve Q (Finset.mem_insert_of_mem hQ))
    rw [Finset.set_biUnion_insert, Finset.sum_insert hPS, add_mul]
    have hcount : (count (idealZeroLocus P ∪ ⋃ Q ∈ S, idealZeroLocus Q) B : ℝ) ≤
        count (idealZeroLocus P) B + count (⋃ Q ∈ S, idealZeroLocus Q) B := by
      exact_mod_cast count_union_le (idealZeroLocus P) (⋃ Q ∈ S, idealZeroLocus Q) B
    exact hcount.trans (add_le_add (curve_count_le_degree_mul_box_side P hP.2.1 hP.2.2 hB) hS)

