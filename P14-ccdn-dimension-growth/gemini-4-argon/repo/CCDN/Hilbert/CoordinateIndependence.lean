/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.MonomialOrthants
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import CCDN.Hilbert.OrthantMultiplicity

/-! Maximal standard-monomial orthants construct algebraically
independent original coordinates of cardinality equal to Hilbert dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The independent coordinates are constructed from a maximal
standard orthant, with exactly the degree of the Hilbert polynomial. -/
theorem exists_hilbert_dimension_independent_coordinates
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) :
    ∃ U : Set σ, Nat.card U = (filteredHilbertPolynomial I).natDegree ∧
      AlgebraicIndependent K (fun i : U => (Ideal.Quotient.mk I) (X i.val)) := by
  classical
  let S := standardExponentVectors I MonomialOrder.degLex
  obtain ⟨B, _, hB⟩ := lowerSet_clamp_stabilizes S
    (standardExponentVectors_lower I MonomialOrder.degLex)
  let s := lowerSetOrthantPatterns S B
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := standardExponentVectors_nonempty I hI
    refine ⟨exponentPattern B a, ?_⟩
    simp only [s, lowerSetOrthantPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hB a).mp ha
  have hpoly : filteredHilbertPolynomial I = lowerSetOrthantPolynomial S B := by
    apply filteredHilbertPolynomial_eq_of_eventual
    refine ⟨Fintype.card σ * B, fun n hn => ?_⟩
    rw [lowerSetOrthantPolynomial_eval S B hB n hn,
      filteredCoordinateSpace_finrank_eq_vector_card]
  obtain ⟨_, hdeg, _⟩ := sum_preHilbertPoly_leading s hs
    (fun b => Fintype.card (orthantFree b)) orthantBaseDegree
  obtain ⟨b, hb, he⟩ := Finset.exists_mem_eq_sup s hs
    (fun b => Fintype.card (orthantFree b))
  refine ⟨{i | (b i).val = B}, ?_, algebraicIndependent_iff.mpr fun p hp => ?_⟩
  · rw [Nat.card_eq_fintype_card, hpoly, lowerSetOrthantPolynomial_eq_sum, hdeg, he]
    exact Fintype.card_congr (Equiv.refl _)
  · have hev : aeval (fun i : {i | (b i).val = B} => (Ideal.Quotient.mk I) (X i.val)) =
        (Ideal.Quotient.mkₐ K I).comp (rename Subtype.val) := by ext i; simp
    rw [hev] at hp
    have hmem : rename Subtype.val p ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hp
    have hsupp : rename Subtype.val p ∈
        restrictSupport K (Ideal.standardExponents I MonomialOrder.degLex) := by
      intro a ha
      change a ∈ (rename Subtype.val p).support at ha
      rw [support_rename_of_injective Subtype.val_injective] at ha
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ha
      have hexp : orthantExpand b t ∈ S := by
        apply (hB _).mpr
        rw [clamp_orthantExpand]
        exact (Finset.mem_filter.mp hb).2
      refine Ideal.isLowerSet_standardExponents I MonomialOrder.degLex
        (a := Finsupp.equivFunOnFinite.symm (orthantExpand b t)) (fun i => ?_) hexp
      change (t.mapDomain Subtype.val) i ≤ orthantExpand b t i
      by_cases hi : (b i).val = B
      · have hh := Finsupp.mapDomain_apply_of_injective
          (Subtype.val_injective : Function.Injective (fun i : {i | (b i).val = B} => i.val))
          t ⟨i, hi⟩
        rw [hh]
        simp [orthantExpand, hi]
      · rw [Finsupp.mapDomain_of_notMem_range]
        · exact Nat.zero_le _
        · rintro ⟨j, rfl⟩; exact hi j.property
    exact (rename_injective Subtype.val Subtype.val_injective) (by
      simpa only [map_zero] using
        Ideal.eq_zero_of_mem_restrictSupport_standardExponents I MonomialOrder.degLex hsupp hmem)

end
end CCDN
