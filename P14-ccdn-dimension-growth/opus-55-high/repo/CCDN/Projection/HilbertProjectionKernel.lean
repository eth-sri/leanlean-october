/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import CCDN.Algebra.BinomialSectionBound
import CCDN.Hilbert.LinearCoordinates
import CCDN.Hilbert.PolynomialComparison
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleModule.Basic

/-! Hypersurface projection kernels in arbitrary dimension.
The proper-intersection estimate excludes a second independent equation. -/

namespace CCDN
section
open MvPolynomial

variable {n : ℕ}

theorem proper_intersection_hilbert_dimension_le
    {K : Type*} [Field K]
    {f g : MvPolynomial (Fin (n + 2)) K} (hf : Prime f) (hfg : ¬ f ∣ g)
    (I : Ideal (MvPolynomial (Fin (n + 2)) K)) (hI : I ≠ ⊤)
    (hIf : f ∈ I) (hIg : g ∈ I) :
    (filteredHilbertPolynomial I).natDegree ≤ n := by
  let Q := Polynomial.C ((f.totalDegree * g.totalDegree : ℕ) : ℚ) *
    Polynomial.preHilbertPoly ℚ n 0
  have hQ : Q.natDegree ≤ n := by
    apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_C, Polynomial.natDegree_preHilbertPoly, zero_add]
    exact le_rfl
  apply (polynomial_natDegree_le_of_eventual_nat_eval_le
    (filteredHilbertPolynomial I) Q (filteredHilbertPolynomial_leadingCoeff_pos I hI) ?_).trans hQ
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
  refine ⟨max M (f.totalDegree + g.totalDegree), fun N hN => ?_⟩
  rw [hM N ((le_max_left _ _).trans hN)]
  dsimp [Q]
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.preHilbertPoly_eq_choose_add_sub ℚ n (by grind)]
  simp only [Nat.sub_zero, Nat.add_comm N n]
  exact_mod_cast filteredCoordinateSpace_codim_two_bound hf hfg I hIf hIg
    ((le_max_right _ _).trans hN)

