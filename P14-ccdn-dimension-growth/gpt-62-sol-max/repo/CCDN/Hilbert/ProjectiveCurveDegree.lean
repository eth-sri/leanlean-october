/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveSection
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Algebra.PolynomialPredicates
import CCDN.ForMathlib.LinearMap
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! Replacing a prime by its homogeneous core preserves the graded Hilbert function.
For the resulting cone, summing the graded pieces gives its affine dimension and degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem projectiveHilbertFunction_core {n : ℕ} (I : Ideal (CoordinatePolynomial (n + 1)))
    (m : ℕ) :
    projectiveHilbertFunction (I.homogeneousCore (homogeneousSubmodule (Fin (n + 1)) ℚ)).toIdeal m =
      projectiveHilbertFunction I m := by
  let J := (I.homogeneousCore (homogeneousSubmodule (Fin (n + 1)) ℚ)).toIdeal
  let V := homogeneousSubmodule (Fin (n + 1)) ℚ m
  let L := (Ideal.Quotient.mkₐ ℚ I).toLinearMap
  let T := (Ideal.Quotient.mkₐ ℚ J).toLinearMap
  have he : V ⊓ L.ker = V ⊓ T.ker := by
    ext p
    change p.IsHomogeneous m ∧ Ideal.Quotient.mk I p = 0 ↔
      p.IsHomogeneous m ∧ Ideal.Quotient.mk J p = 0
    simp only [Ideal.Quotient.eq_zero_iff_mem]
    exact ⟨fun ⟨hp, h⟩ => ⟨hp, Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨m, hp⟩ h⟩,
      fun ⟨hp, h⟩ => ⟨hp, Ideal.toIdeal_homogeneousCore_le _ I h⟩⟩
  let : Module.Finite ℚ V := Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  have hl := L.finrank_map_add_finrank_inf_ker V
  have ht := T.finrank_map_add_finrank_inf_ker V
  rw [he] at hl
  change Module.finrank ℚ (V.map T) = Module.finrank ℚ (V.map L)
  omega

private theorem filtered_finrank_succ {n : ℕ} (I : Ideal (CoordinatePolynomial (n + 1)))
    (hI : IsHomogeneousIdeal I) (m : ℕ) :
    affineHilbertFunction I (m + 1) = affineHilbertFunction I m + projectiveHilbertFunction I (m + 1) := by
  let V := filteredCoordinateSpace I m
  let W := homogeneousCoordinateSpace I (m + 1)
  have hsup : filteredCoordinateSpace I (m + 1) = V ⊔ W := by
    apply le_antisymm
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := mem_filteredCoordinateSpace.mp hx
      have hs : (∑ i ∈ Finset.range (m + 2), homogeneousComponent i p) = p := by
        conv_rhs => rw [← sum_homogeneousComponent (φ := p)]
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro i hi hi'
        apply homogeneousComponent_eq_zero
        simp only [Finset.mem_range] at hi'
        omega
      rw [Finset.sum_range_succ] at hs
      change Ideal.Quotient.mk I p ∈ V ⊔ W
      rw [← hs, map_add]
      apply Submodule.add_mem_sup
      · refine mem_filteredCoordinateSpace.mpr ⟨_, totalDegree_finsetSum_le ?_, rfl⟩
        exact fun i hi => (homogeneousComponent_isHomogeneous i p).totalDegree_le.trans
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      · exact ⟨_, homogeneousComponent_isHomogeneous _ _, rfl⟩
    · refine sup_le (filteredCoordinateSpace_mono I (Nat.le_succ m)) ?_
      rintro _ ⟨p, hp, rfl⟩
      exact mem_filteredCoordinateSpace.mpr ⟨p, IsHomogeneous.totalDegree_le hp, rfl⟩
  have hdis : Disjoint V W := by
    apply Submodule.disjoint_def.mpr
    rintro x hx hy
    obtain ⟨p, hp, rfl⟩ := mem_filteredCoordinateSpace.mp hx
    obtain ⟨q, hq, he⟩ := hy
    change Ideal.Quotient.mk I q = Ideal.Quotient.mk I p at he
    have hmem := hI (q - p) (Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, he, sub_self])) (m + 1)
    have hz : homogeneousComponent (m + 1) p = 0 := homogeneousComponent_eq_zero _ _ (by omega)
    rw [map_sub, homogeneousComponent_eq_self hq, hz, sub_zero] at hmem
    change Ideal.Quotient.mk I p = 0
    rw [← he]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have h := Submodule.finrank_sup_add_finrank_inf_eq V W
  rw [← hsup, hdis.eq_bot, finrank_bot, add_zero] at h
  exact h

private theorem homogeneous_curve_dimension_degree {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) (hI : IsHomogeneousIdeal I)
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) : HasProjectiveDimensionDegree I 1 d := by
  obtain ⟨N, c, hN⟩ := hdegree
  let P : Polynomial ℚ := Polynomial.C ((d : ℚ) / 2) * Polynomial.X ^ 2 +
    Polynomial.C ((c : ℚ) + (d : ℚ) / 2) * Polynomial.X
  let e : ℚ := affineHilbertFunction I N - P.eval (N : ℚ)
  have hP : filteredHilbertPolynomial I = P + Polynomial.C e := by
    apply filteredHilbertPolynomial_eq_of_eventual
    refine ⟨N, fun m hm => ?_⟩
    change (P + Polynomial.C e).eval (m : ℚ) = affineHilbertFunction I m
    induction m, hm using Nat.le_induction with
    | base => simp [e]
    | succ m hm ih =>
      have h := hN (m + 1) (by omega)
      rw [filtered_finrank_succ I hI]
      push_cast
      simp only [Polynomial.eval_add, Polynomial.eval_C] at ih ⊢
      have he : P.eval ((m : ℚ) + 1) = P.eval (m : ℚ) + (d : ℚ) * (m + 1) + c := by
        simp [P]
        ring
      have h' : (projectiveHilbertFunction I (m + 1) : ℚ) = (d : ℚ) * (m + 1) + c := by
        exact_mod_cast h
      linarith
  exact ⟨by rw [hP]; exact Polynomial.natDegree_quadratic (by positivity), by
    rw [hP, Polynomial.leadingCoeff_quadratic (by positivity)]; norm_num⟩

/-- The homogeneous core is a prime with the required Hilbert degree, and its zero locus
contains that of the original ideal. -/
theorem exists_homogeneous_projective_curve {n d : ℕ} (I : Ideal (CoordinatePolynomial (n + 1)))
    [I.IsPrime] (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) :
    ∃ J : Ideal (CoordinatePolynomial (n + 1)), J.IsPrime ∧ IsHomogeneousIdeal J ∧ J ≤ I ∧
      HasProjectiveCurveDegree J d ∧ HasProjectiveDimensionDegree J 1 d := by
  let J := I.homogeneousCore (homogeneousSubmodule (Fin (n + 1)) ℚ)
  have hhom : IsHomogeneousIdeal J.toIdeal := fun f hf i =>
    (mem_iff_homogeneousComponent_mem J.isHomogeneous f).mp hf i
  have hdeg : HasProjectiveCurveDegree J.toIdeal d := by
    obtain ⟨N, c, hN⟩ := hdegree
    exact ⟨N, c, fun m hm => by rw [show projectiveHilbertFunction J.toIdeal m = _ from
      projectiveHilbertFunction_core I m]; exact hN m hm⟩
  exact ⟨J.toIdeal, Ideal.IsPrime.homogeneousCore ‹I.IsPrime›, hhom, Ideal.toIdeal_homogeneousCore_le _ I,
    hdeg, homogeneous_curve_dimension_degree J.toIdeal hhom hd hdeg⟩

end
end CCDN
