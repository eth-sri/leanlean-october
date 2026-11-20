/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredPrimeDecomposition
public import CCDN.Surface.CurveComponents
import CCDN.Algebra.BinomialSectionBound
import CCDN.Hilbert.FilteredComponentDegreeBudget
import CCDN.Hilbert.FilteredHilbertLinearity
import CCDN.Hilbert.PrimeComponentTranscendence
import CCDN.Hilbert.PrimeIdealDimensionDrop

/-!
A finite decomposition of a proper affine surface section into
rational prime curves, with a proved additive degree budget. Components with
no rational points are discarded before requiring positive curve degrees.

An eventual linear upper bound gives an eventual linear Hilbert
formula, with its slope bounded by the original coefficient.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A proper section in affine three-space has at most linear Hilbert growth, hence an eventual slope. -/
private theorem proper_intersection_eventual_linear_degree {K : Type*} [Field K]
    {f g : MvPolynomial (Fin 3) K} (hf : Prime f) (hfg : ¬ f ∣ g)
    (I : Ideal (MvPolynomial (Fin 3) K)) (hI : I ≠ ⊤) (hIf : f ∈ I) (hIg : g ∈ I) :
    ∃ d, HasFilteredCurveDegree I d := by
  apply filteredCoordinateSpace_eventually_linear I hI
    (f.totalDegree * g.totalDegree) (f.totalDegree + g.totalDegree)
  intro N hN
  have hh := filteredCoordinateSpace_codim_two_bound hf hfg I hIf hIg hN
  simp only [Nat.choose_one_right] at hh
  nlinarith

/-- Distinct positive-degree prime curves in a proper section satisfy the section's degree budget. -/
theorem surface_prime_curve_degree_sum_le
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (δ : Ideal (CoordinatePolynomial 3) → ℕ)
    (hS : ∀ P ∈ S, IsSurfaceCurve f P (δ P) ∧ g ∈ P) :
    ∑ P ∈ S, δ P ≤ f.totalDegree * g.totalDegree := by
  rw [← Finset.sum_coe_sort]
  have h (P : S) := hS P P.property
  apply polynomialSection_prime_curveDegree_sum_le f g hf.prime hfg (fun P : S => P.val)
    (fun P => (h P).1.isPrime) ?_ ?_ _ (fun P => (h P).1.degree)
  · intro P
    rw [polynomialSectionIdeal, Ideal.span_le]
    rintro a (rfl | ha)
    · exact (h P).1.mem
    · exact (Set.mem_singleton_iff.mp ha).symm ▸ (h P).2
  · intro P Q hPQ
    have : P.val.IsPrime := (h P).1.isPrime
    have : Q.val.IsPrime := (h Q).1.isPrime
    have hP : HasFilteredCurveDegree P.val (δ P) := (h P).1.degree
    have hQ : HasFilteredCurveDegree Q.val (δ Q) := (h Q).1.degree
    by_contra hne
    exact prime_ideal_not_le_of_same_positive_dimension P.val Q.val
      (hP.natDegree_eq_one (h P).1.pos) (hQ.natDegree_eq_one (h Q).1.pos)
      (fun he => hne (Subtype.ext he)) hPQ

/-- Discard only components with no rational points; all other components of a proper
section have positive Hilbert slope. -/
theorem exists_completeIntersection_curve_components
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g) :
    ∃ S : Finset (Ideal (CoordinatePolynomial 3)),
      ∃ d : Ideal (CoordinatePolynomial 3) → ℕ,
        (∀ P ∈ S, IsSectionCurve f g P (d P)) ∧
        zeroLocus f ∩ zeroLocus g = ⋃ P ∈ S, idealZeroLocus P ∧
        (∑ P ∈ S, d P) ≤ f.totalDegree * g.totalDegree := by
  classical
  let T := minimalPrimeComponents (polynomialSectionIdeal f g)
  let S := T.filter (fun P => (idealZeroLocus P).Nonempty)
  have hex (P) (hP : P ∈ S) : ∃ d, IsSectionCurve f g P d := by
    obtain ⟨hPT, z, hz⟩ := Finset.mem_filter.mp hP
    have hminimal := mem_minimalPrimeComponents.mp hPT
    have : P.IsPrime := hminimal.isPrime
    have hfP := hminimal.le (polynomialSectionIdeal_first_mem f g)
    have hgP := hminimal.le (polynomialSectionIdeal_second_mem f g)
    obtain ⟨d, hd⟩ := proper_intersection_eventual_linear_degree hf.prime hfg P
      hminimal.isPrime.ne_top hfP hgP
    have hheight := Ideal.height_le_two_of_mem_minimalPrimes_span_pair hminimal
    exact ⟨d, ⟨⟨hminimal.isPrime, height_two_eventual_slope_pos_of_point P hheight z hz hd,
      hfP, hd⟩, hgP⟩⟩
  let d (P) := if h : P ∈ S then (hex P h).choose else 0
  have hd (P) (hP : P ∈ S) : IsSectionCurve f g P (d P) := by
    simpa [d, hP] using (hex P hP).choose_spec
  refine ⟨S, d, hd, ?_, surface_prime_curve_degree_sum_le f g hf hfg S d
    (fun P hP => ⟨(hd P hP).toIsSurfaceCurve, (hd P hP).mem_right⟩)⟩
  rw [← idealZeroLocus_polynomialSectionIdeal, idealZeroLocus_eq_union_minimalPrimeComponents]
  ext x
  simp only [Set.mem_iUnion, S, Finset.mem_filter]
  exact ⟨fun ⟨P, hp, hx⟩ => ⟨P, ⟨hp, x, hx⟩, hx⟩, fun ⟨P, ⟨hp, _⟩, hx⟩ => ⟨P, hp, hx⟩⟩

end
end CCDN
