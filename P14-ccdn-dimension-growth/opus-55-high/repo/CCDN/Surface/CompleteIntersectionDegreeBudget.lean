/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.FilteredPrimeDecomposition
import CCDN.Surface.CurveComponents
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

namespace CCDN
section
open MvPolynomial

theorem filteredCoordinateSpace_eventually_linear_of_eventual_bound
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (C T : ℕ)
    (hbound : ∀ N ≥ T, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 2)) :
    ∃ d, HasFilteredCurveDegree I d := by
  have hglobal (N : ℕ) (_hN : 14 ≤ N) :
      Module.finrank K (filteredCoordinateSpace I N) ≤ (C * (T + 2)) * (N + 2) := by
    by_cases hTN : T ≤ N
    · grind
    · have hNT : N ≤ T := by omega
      have hh := Submodule.finrank_mono (filteredCoordinateSpace_mono I hNT)
      exact (hh.trans (hbound T le_rfl)).trans (Nat.le_mul_of_pos_right _ (by omega))
  let B := 2 * (C * (T + 2)) + 14
  obtain ⟨N, hN⟩ := lowerSet_shell_card_eventually_constant
    (Ideal.standardExponents I MonomialOrder.degLex)
    (Ideal.isLowerSet_standardExponents I MonomialOrder.degLex)
    B (by grind)
    (fun a ha i j hi hj => standard_at_most_one_large I (C * (T + 2)) hglobal ha hi hj)
  let d := Nat.card (fullExponentRays (Ideal.standardExponents I MonomialOrder.degLex) B)
  have hstep (n : ℕ) (hn : N ≤ n) :
      Module.finrank K (filteredCoordinateSpace I (n + 1)) =
        Module.finrank K (filteredCoordinateSpace I n) + d := by
    rw [standard_card_succ, hN (n + 1) (by omega)]
  have hformula (k : ℕ) : Module.finrank K (filteredCoordinateSpace I (N + k)) =
      Module.finrank K (filteredCoordinateSpace I N) + d * k := by
    induction k with
    | zero => simp
    | succ k hk =>
      rw [show N + (k + 1) = (N + k) + 1 by omega, hstep (N + k) (by omega), hk]
      ring
  refine ⟨d, N, (Module.finrank K (filteredCoordinateSpace I N) : ℤ) - d * N, ?_⟩
  intro n hn
  have he := hformula (n - N)
  rw [Nat.add_sub_of_le hn] at he
  rw [he]
  push_cast
  rw [Nat.cast_sub hn]
  ring

variable (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
include hf hfg

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
    apply filteredCoordinateSpace_eventually_linear_of_eventual_bound P.val
      (f.totalDegree * g.totalDegree) (f.totalDegree + g.totalDegree)
    intro N hN
    have hh := filteredCoordinateSpace_codim_two_bound hf.prime hfg P.val (le_minimalPrimeComponents P.property (polynomialSectionIdeal_first_mem f g)) (le_minimalPrimeComponents P.property (polynomialSectionIdeal_second_mem f g)) hN
    simp at hh
    exact hh.trans (Nat.mul_le_mul_left _ (by omega))
  choose d hd using hex
  exact ⟨d, hd, (show ∑ P, d P ≤ f.totalDegree * g.totalDegree by
      apply minimalPrimeComponents_slope_sum_le (polynomialSectionIdeal f g)
        (f.totalDegree * g.totalDegree) (f.totalDegree + g.totalDegree) _ d hd
      intro N hN
      have hh := filteredCoordinateSpace_codim_two_bound hf.prime hfg
        (polynomialSectionIdeal f g) (polynomialSectionIdeal_first_mem f g)
        (polynomialSectionIdeal_second_mem f g) hN
      simpa [Nat.choose_one_right, Nat.add_comm 1] using hh)⟩

/-- A proper section in affine three-space is covered exactly by a finite
set of rational prime curves. Their positive Hilbert degrees sum to
at most the product of the two equation degrees. All components and degrees
are constructed, including the case of an empty common zero set. -/
theorem exists_completeIntersection_curve_components
    :
    ∃ S : Finset (Ideal (CoordinatePolynomial 3)),
      ∃ d : Ideal (CoordinatePolynomial 3) → ℕ,
        (∀ P ∈ S, IsSectionCurve f g P (d P)) ∧
        zeroLocus f ∩ zeroLocus g = ⋃ P ∈ S, idealZeroLocus P ∧
        (∑ P ∈ S, d P) ≤ f.totalDegree * g.totalDegree := by
  classical
  let T := minimalPrimeComponents (polynomialSectionIdeal f g)
  obtain ⟨δ, hδ, hsumδ⟩ := polynomialSection_minimalPrime_degrees_exist f g hf hfg
  let d (P : Ideal (CoordinatePolynomial 3)) := if hP : P ∈ T then δ ⟨P, hP⟩ else 0
  let S := T.filter (fun P => (idealZeroLocus P).Nonempty)
  have hd (P : T) : d P.val = δ P := by grind
  have hTP (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T) :
      (polynomialSectionIdeal f g).IsMinimalPrime P := mem_minimalPrimeComponents.mp hP
  have hcurve (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T) :
      HasAffineCurveDegree P (d P) := by
    rw [hd ⟨P, hP⟩]
    exact hδ ⟨P, hP⟩
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
        rwa [idealZeroLocus_polynomialSectionIdeal]
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
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by grind)
      _ = _ := hsumT
      _ ≤ _ := hsumδ

