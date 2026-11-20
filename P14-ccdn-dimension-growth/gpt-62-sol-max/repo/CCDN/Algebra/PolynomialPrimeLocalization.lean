/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Localization.FractionRing
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Nonconstant prime polynomials remain prime when coefficients are localized. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A nonconstant polynomial over a domain cannot divide a nonzero constant. -/
private theorem mvPolynomial_not_dvd_nonzero_constant
    {R σ : Type*} [CommRing R] [IsDomain R]
    (f : MvPolynomial σ R) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    (a : R) (ha : a ≠ 0) : ¬ f ∣ C a := by
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    aesop
  have hdeg := totalDegree_mul_of_isDomain hf hg0
  rw [← hg, totalDegree_C] at hdeg
  omega

/-- Prime polynomials of positive variable degree survive coefficient
localization at nonzero elements. -/
theorem prime_mvPolynomial_map_localization
    {R S σ : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors R)
    (f : MvPolynomial σ R) (hf : Prime f) (hd : 0 < f.totalDegree) :
    Prime (MvPolynomial.map (algebraMap R S) f) := by
  let N : Submonoid (MvPolynomial σ R) := M.map C
  let I := Ideal.span {f}
  have hI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hf
  have hdis : Disjoint (N : Set (MvPolynomial σ R)) (I : Set (MvPolynomial σ R)) := by
    rw [Set.disjoint_left]
    intro q hq hqi
    obtain ⟨a, ha, rfl⟩ := hq
    exact mvPolynomial_not_dvd_nonzero_constant f hf.ne_zero hd a
      (mem_nonZeroDivisors_iff_ne_zero.mp (hM ha)) (Ideal.mem_span_singleton.mp hqi)
  have hp := IsLocalization.isPrime_of_isPrime_disjoint N (MvPolynomial σ S) I hI hdis
  have hinj := IsLocalization.injective S hM
  apply (Ideal.span_singleton_prime ((map_ne_zero_iff _ (MvPolynomial.map_injective _ hinj)).mpr hf.ne_zero)).mp
  simpa only [I, Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def] using hp

end
end CCDN
