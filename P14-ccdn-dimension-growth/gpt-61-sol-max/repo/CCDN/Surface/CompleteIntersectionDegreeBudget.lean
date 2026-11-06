/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Hilbert.FilteredPrimeDecomposition
public import CCDN.Surface.CurveComponents
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

public section
namespace CCDN
open MvPolynomial

variable (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)

include hf hfg in
/-- Every minimal-prime component has an eventual affine Hilbert
degree. The slope is allowed to be zero until a rational point is exhibited. -/
theorem polynomialSection_minimalPrime_degrees_exist
     :
    ∃ d : minimalPrimeComponents (polynomialSectionIdeal f g) → ℕ,
      (∀ P, HasAffineCurveDegree P.val (d P)) ∧
        ∑ P, d P ≤ f.totalDegree * g.totalDegree := by
  classical
  have hex (P : minimalPrimeComponents (polynomialSectionIdeal f g)) :
      ∃ d : ℕ, HasAffineCurveDegree P.val d := by
    apply filteredCoordinateSpace_eventually_linear P.val
      (f.totalDegree * g.totalDegree) (f.totalDegree + g.totalDegree)
    intro N hN
    have hh := filteredCoordinateSpace_codim_two_bound hf.prime hfg P.val
      (le_minimalPrimeComponents P.property (polynomialSectionIdeal_first_mem f g))
      (le_minimalPrimeComponents P.property (polynomialSectionIdeal_second_mem f g)) hN
    simp only [Nat.choose_one_right] at hh
    exact hh.trans (Nat.mul_le_mul_left _ (by omega))
  choose d hd using hex
  exact ⟨d, hd, polynomialSection_minimalPrime_curveDegree_sum_le f g hf hfg d hd⟩

include hf hfg in
/-- A proper section in affine three-space is covered exactly by a finite
set of rational prime curves. Their positive Hilbert degrees sum to
at most the product of the two equation degrees. All components and degrees
are constructed, including the case of an empty common zero set. -/
theorem exists_completeIntersection_curve_components
     :
    ∃ S : Finset (CCDN.CoordinateIdeal 3),
      ∃ d : CCDN.CoordinateIdeal 3 → ℕ,
        (∀ P ∈ S, IsSectionCurve f g P (d P)) ∧
        zeroLocus f ∩ zeroLocus g = ⋃ P ∈ S, idealZeroLocus P ∧
        (∑ P ∈ S, d P) ≤ f.totalDegree * g.totalDegree := by
  classical
  let T := minimalPrimeComponents (polynomialSectionIdeal f g)
  obtain ⟨δ, hδ, hsumδ⟩ := polynomialSection_minimalPrime_degrees_exist f g hf hfg
  let d (P : CCDN.CoordinateIdeal 3) := if hP : P ∈ T then δ ⟨P, hP⟩ else 0
  let S := T.filter (fun P => (idealZeroLocus P).Nonempty)
  have hd (P : T) : d P.val = δ P := by
    grind
  have hTP (P : CCDN.CoordinateIdeal 3) (hP : P ∈ T) :
      (polynomialSectionIdeal f g).IsMinimalPrime P := mem_minimalPrimeComponents.mp hP
  have hcurve (P : CCDN.CoordinateIdeal 3) (hP : P ∈ T) :
      HasAffineCurveDegree P (d P) := by
    simp_all
  refine ⟨S, d, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨hPT, z, hz⟩ := Finset.mem_filter.mp hP
    have hminimal := hTP P hPT
    have : P.IsPrime := hminimal.isPrime
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
        simp_all [idealZeroLocus_polynomialSectionIdeal]
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
      exact Finset.sum_congr rfl (fun P _ => hd P)
    calc
      _ ≤ ∑ P ∈ T, d P :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
      _ = _ := hsumT
      _ ≤ _ := hsumδ

end CCDN
