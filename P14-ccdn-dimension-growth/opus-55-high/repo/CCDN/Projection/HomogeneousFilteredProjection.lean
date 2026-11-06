/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.Algebra.MvPolynomial.Monad

/-! A linear homogeneous projection of a homogeneous quotient is strict
for the total-degree filtration: any image element of bounded degree has a
preimage of the same bounded degree. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {K σ : Type*} [Field K] (N : ℕ)

def degreeTruncation :
    MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  ∑ i ∈ Finset.range (N + 1), homogeneousComponent i

lemma degreeTruncation_apply
    (p : MvPolynomial σ K) :
    degreeTruncation N p = ∑ i ∈ Finset.range (N + 1), homogeneousComponent i p := by
  simp [degreeTruncation]

end

section
variable {K σ τ : Type*} [Field K] (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1) (N : ℕ) (p : MvPolynomial σ K)
include ha

/-- Substituting homogeneous linear forms commutes with taking homogeneous components: the
degree-`N` component of `aeval a p` is `aeval a` of the degree-`N` component of `p`. -/
lemma homogeneousComponent_aeval_linear
    :
    homogeneousComponent N (aeval a p) = aeval a (homogeneousComponent N p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial e c =>
    have hm := isHomogeneous_monomial c (rfl : e.degree = e.degree)
    have hm' : (aeval a (monomial e c)).IsHomogeneous e.degree := by
      simpa using hm.aeval a ha
    rw [homogeneousComponent_of_mem hm, homogeneousComponent_of_mem hm']
    split_ifs <;> simp

lemma degreeTruncation_aeval_linear
    :
    degreeTruncation N (aeval a p) = aeval a (degreeTruncation N p) := by
  simp only [degreeTruncation_apply, map_sum, homogeneousComponent_aeval_linear a ha]

end

/-- The projection of a homogeneous quotient by homogeneous linear forms `a` is strict for the
total-degree filtration: if the image of `p` has degree at most `N` in the quotient by `I`, then it
is the image of some `q` of total degree at most `N`. -/
theorem homogeneous_projection_filtered_lift
    {K σ τ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial τ K))
    (hI : IsHomogeneousIdeal I)
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (p : MvPolynomial σ K) (N : ℕ)
    (hp : projectionCoordinateMap I a p ∈ filteredCoordinateSpace I N) :
    ∃ q : MvPolynomial σ K, q.totalDegree ≤ N ∧
      projectionCoordinateMap I a q = projectionCoordinateMap I a p := by
  obtain ⟨f, hf, he⟩ := Submodule.mem_map.mp hp
  have hfd := (mem_restrictTotalDegree _ _ _).mp hf
  have htmem : degreeTruncation N (aeval a p - f) ∈ I := by
    rw [degreeTruncation_apply]
    exact I.sum_mem (fun i _ => hI _ (by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change projectionCoordinateMap I a p - (Ideal.Quotient.mk I) f = 0
      simp_all) i)
  rw [map_sub, degreeTruncation_aeval_linear a ha, (show degreeTruncation N f = f by
      rw [degreeTruncation_apply]
      conv_rhs => rw [← sum_homogeneousComponent (φ := f)]
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hfd 1))
      intro i hi hnot
      apply homogeneousComponent_eq_zero
      have hh : ¬ i < f.totalDegree + 1 := by grind
      omega)] at htmem
  refine ⟨degreeTruncation N p, (show (degreeTruncation N p).totalDegree ≤ N by
      rw [degreeTruncation_apply]
      apply totalDegree_finsetSum_le
      intro i hi
      exact (homogeneousComponent_isHomogeneous i p).totalDegree_le.trans
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))), ?_⟩
  have ht := Ideal.Quotient.eq_zero_iff_mem.mpr htmem
  rw [map_sub, sub_eq_zero] at ht
  exact ht.trans he

