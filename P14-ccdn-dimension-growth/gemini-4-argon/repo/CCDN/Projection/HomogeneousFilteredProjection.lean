/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.Algebra.MvPolynomial.Monad

/-! A linear homogeneous projection of a homogeneous quotient is strict
for the total-degree filtration: any image element of bounded degree has a
preimage of the same bounded degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Substituting homogeneous linear forms commutes with taking homogeneous components: the
degree-`N` component of `aeval a p` is `aeval a` of the degree-`N` component of `p`. -/
lemma homogeneousComponent_aeval_linear {K σ τ : Type*} [Field K]
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (N : ℕ) (p : MvPolynomial σ K) :
    homogeneousComponent N (aeval a p) = aeval a (homogeneousComponent N p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial e c =>
    have hm := isHomogeneous_monomial c (rfl : e.degree = e.degree)
    have hm' : (aeval a (monomial e c)).IsHomogeneous e.degree := by
      simpa only [one_mul] using hm.aeval a ha
    rw [homogeneousComponent_of_mem hm, homogeneousComponent_of_mem hm']
    split_ifs <;> simp

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
  have hmem : aeval a p - f ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    change projectionCoordinateMap I a p - (Ideal.Quotient.mkₐ K I).toLinearMap f = 0
    rw [he, sub_self]
  let q := ∑ i ∈ Finset.range (N + 1), homogeneousComponent i p
  have htf : ∑ i ∈ Finset.range (N + 1), homogeneousComponent i f = f := by
    conv_rhs => rw [← sum_homogeneousComponent (φ := f)]
    exact (Finset.sum_subset
      (Finset.range_mono (Nat.add_le_add_right ((mem_restrictTotalDegree _ _ _).mp hf) 1))
      fun i _ hnot => homogeneousComponent_eq_zero i f (by simp at hnot; omega)).symm
  have htmem : aeval a q - f ∈ I := by
    simpa only [q, map_sum, map_sub, Finset.sum_sub_distrib,
      homogeneousComponent_aeval_linear a ha, htf] using
      I.sum_mem (t := Finset.range (N + 1)) fun i _ => hI _ hmem i
  refine ⟨q, totalDegree_finsetSum_le fun i hi =>
    (homogeneousComponent_isHomogeneous i p).totalDegree_le.trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), ?_⟩
  have ht := Ideal.Quotient.eq_zero_iff_mem.mpr htmem
  rw [map_sub, sub_eq_zero] at ht
  exact ht.trans he

end
end CCDN
