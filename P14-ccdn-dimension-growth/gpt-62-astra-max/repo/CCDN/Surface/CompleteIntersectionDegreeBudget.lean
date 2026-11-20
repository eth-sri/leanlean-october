/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredPrimeDecomposition
public import CCDN.Surface.CurveComponents
import CCDN.ForMathlib.MvPolynomial
import CCDN.Algebra.BinomialSectionBound
import CCDN.Algebra.CoordinatePowerGeneration
import CCDN.Hilbert.FilteredComponentDegreeBudget
import CCDN.Hilbert.FilteredHilbertLinearity
import CCDN.Hilbert.PrimeComponentTranscendence

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

variable (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)

include hf hfg in
/-- Every minimal-prime component has an eventual affine Hilbert
degree. The slope is allowed to be zero until a rational point is exhibited. -/
theorem polynomialSection_minimalPrime_degrees_exist :
    ∃ d : minimalPrimeComponents (polynomialSectionIdeal f g) → ℕ,
      (∀ P, HasAffineCurveDegree P.val (d P)) ∧
        ∑ P, d P ≤ f.totalDegree * g.totalDegree := by
  classical
  have hex (P : minimalPrimeComponents (polynomialSectionIdeal f g))  := by
    have hm := mem_minimalPrimeComponents.mp P.property
    apply curve_degree_of_linear_growth _ hm.isPrime.ne_top
      (f.totalDegree * g.totalDegree) (f.totalDegree + g.totalDegree)
    intro N hN
    have hh := filteredCoordinateSpace_codim_two_bound hf.prime hfg P.val
      (hm.le (polynomialSectionIdeal_first_mem f g)) (hm.le (polynomialSectionIdeal_second_mem f g)) hN
    simp only [Nat.choose_one_right] at hh
    grind
  choose d hd using hex
  exact ⟨d, hd, polynomialSection_minimalPrime_curveDegree_sum_le f g hf hfg d hd⟩

include hf hfg in
/-- A proper section in affine three-space is covered exactly by a finite
set of rational prime curves. Their positive Hilbert degrees sum to
at most the product of the two equation degrees. All components and degrees
are constructed, including the case of an empty common zero set. -/
theorem exists_completeIntersection_curve_components :
    ∃ S : Finset (Ideal (CoordinatePolynomial 3)),
      ∃ d : Ideal (CoordinatePolynomial 3) → ℕ,
        (∀ P ∈ S, IsSectionCurve f g P (d P)) ∧
        zeroLocus f ∩ zeroLocus g = ⋃ P ∈ S, idealZeroLocus P ∧
        (∑ P ∈ S, d P) ≤ f.totalDegree * g.totalDegree ∧
        (∀ P ∈ S, (polynomialSectionIdeal f g).IsMinimalPrime P) := by
  classical
  let T := minimalPrimeComponents (polynomialSectionIdeal f g)
  obtain ⟨δ, hδ, hsumδ⟩ := polynomialSection_minimalPrime_degrees_exist f g hf hfg
  let d (P : Ideal (CoordinatePolynomial 3)) := if hP : P ∈ T then δ ⟨P, hP⟩ else 0
  have hd (P : T) : d P.val = δ P := by
    grind
  have hTP (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T)  := mem_minimalPrimeComponents.mp hP
  have hcurve (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T) :
      HasAffineCurveDegree P (d P) := by
    grind
  refine ⟨(T.filter (fun P => (idealZeroLocus P).Nonempty)), d, ?_, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨hPT, z, hz⟩ := Finset.mem_filter.mp hP
    have hminimal := hTP P hPT
    have := hminimal.isPrime
    have hheight :=
      Ideal.height_eq_two_of_mem_minimalPrimes_span_pair hf.prime hfg hminimal
    have hdeg := hcurve P hPT
    exact ⟨⟨hminimal.isPrime, hheight, hminimal.le (polynomialSectionIdeal_first_mem f g), hdeg⟩,
      hminimal.le (polynomialSectionIdeal_second_mem f g),
      height_two_eventual_slope_pos_of_point P hheight z hz hdeg⟩
  · ext x
    constructor
    · intro hx
      have hxi : x ∈ idealZeroLocus (polynomialSectionIdeal f g) := by
        rw [idealZeroLocus_polynomialSectionIdeal]
        exact hx
      rw [idealZeroLocus_eq_union_minimalPrimeComponents] at hxi
      obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hxi
      obtain ⟨hPT, hxP⟩ := Set.mem_iUnion.mp hxP
      exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hPT, ⟨x, hxP⟩⟩, hxP⟩⟩
    · intro hx
      obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hPS, hxP⟩ := Set.mem_iUnion.mp hxP
      have hminimal := hTP P (Finset.mem_filter.mp hPS).1
      exact ⟨hxP f (hminimal.le (polynomialSectionIdeal_first_mem f g)),
        hxP g (hminimal.le (polynomialSectionIdeal_second_mem f g))⟩
  · have hsumT : (∑ P ∈ T, d P) = ∑ P, δ P := by
      rw [← Finset.sum_coe_sort T d]
      solve_by_elim [Finset.sum_congr]
    calc
      _ ≤ ∑ P ∈ T, d P :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
      _ = _ := hsumT
      _ ≤ _ := hsumδ
  grind

theorem integer_surface_section {f g : IntegerPolynomial 3} {B : ℝ}
    (hir : Irreducible (rationalEquation f)) (proper : ¬ rationalEquation f ∣ rationalEquation g)
    (vanish : ∀ x : IntPoint 3, InBox x B → eval x f = 0 → eval x g = 0) :
    ∃ S : Finset (Ideal (CoordinatePolynomial 3)), ∃ δ : Ideal (CoordinatePolynomial 3) → ℕ,
      (∀ I ∈ S, IsSectionCurve (rationalEquation f) (rationalEquation g) I (δ I)) ∧
      (∀ x : IntPoint 3, InBox x B → eval x f = 0 → rationalPoint x ∈ ⋃ I ∈ S, idealZeroLocus I) ∧
      (∑ I ∈ S, (δ I : ℝ)) ≤ (f.totalDegree:ℝ)*g.totalDegree := by
  obtain ⟨S,δ,hS,cover,budget,-⟩ := exists_completeIntersection_curve_components _ _ hir proper
  refine ⟨S,δ,hS,?_,?_⟩
  · rw [← cover]; exact fun x hx hf => ⟨mem_integer_zeroLocus.mpr hf,mem_integer_zeroLocus.mpr (vanish x hx hf)⟩
  · simp only [rational_map_totalDegree] at budget; exact_mod_cast budget

end
end CCDN
