/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Primitive integer multivariate equations, denominator clearing, and
reflection of divisibility from rational coefficients for primitive equations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The integer coefficients have no common nonunit divisor. -/
def PrimitiveIntegerPolynomial {σ : Type*} (f : MvPolynomial σ ℤ) : Prop :=
  ∀ c : ℤ, (∀ m, c ∣ f.coeff m) → IsUnit c

section

variable {σ : Type*}
include σ

private lemma PrimitiveIntegerPolynomial.of_dvd {f g : MvPolynomial σ ℤ}
    (hf : PrimitiveIntegerPolynomial f) (hg : g ∣ f) : PrimitiveIntegerPolynomial g := by
  intro c hc
  exact hf c ((C_dvd_iff_dvd_coeff c f).mp (((C_dvd_iff_dvd_coeff c g).mpr hc).trans hg))

private lemma PrimitiveIntegerPolynomial.isUnit_of_rational_map
    {f : MvPolynomial σ ℤ} (hf : PrimitiveIntegerPolynomial f)
    (hu : IsUnit (MvPolynomial.map (Int.castRingHom ℚ) f)) : IsUnit f := by
  have hd := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
  have he : (MvPolynomial.map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
  have hc := totalDegree_eq_zero_iff_eq_C.mp (he ▸ hd)
  rw [hc]
  exact (hf _ ((C_dvd_iff_dvd_coeff _ f).mp (hc ▸ dvd_rfl))).map C

/-- A primitive integer polynomial whose image over `ℚ` is irreducible is irreducible over `ℤ`. -/
lemma PrimitiveIntegerPolynomial.irreducible_of_rational_map
    {f : MvPolynomial σ ℤ} (hf : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f)) : Irreducible f := by
  refine ⟨fun hu => hir.not_isUnit (hu.map (MvPolynomial.map (Int.castRingHom ℚ))), ?_⟩
  intro g h he
  have hh := hir.isUnit_or_isUnit (by rw [he, map_mul])
  exact hh.imp
    ((hf.of_dvd ⟨h, he⟩).isUnit_of_rational_map)
    ((hf.of_dvd ⟨g, by grind⟩).isUnit_of_rational_map)

/-- Clearing denominators: every rational multivariate polynomial has a nonzero integer multiple
`b • f` with integer coefficients. -/
theorem mvPolynomial_integer_multiple (f : MvPolynomial σ ℚ) :
    ∃ (b : ℤ) (g : MvPolynomial σ ℤ), b ≠ 0 ∧
      MvPolynomial.map (Int.castRingHom ℚ) g = C (b : ℚ) * f := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun i : f.support => f.coeff i.val)
  choose v hv using hb
  refine ⟨b.val, ∑ i : f.support, monomial i.val (v i), nonZeroDivisors.coe_ne_zero b, ?_⟩
  conv_rhs => rw [(f.as_sum.trans (Finset.sum_coe_sort f.support (fun m => monomial m (f.coeff m))).symm), Finset.mul_sum]
  simp only [map_sum, map_monomial, C_mul_monomial]
  apply Finset.sum_congr rfl
  tauto

private lemma PrimitiveIntegerPolynomial.isRelPrime_constant
    {f : MvPolynomial σ ℤ} (hf : PrimitiveIntegerPolynomial f) {c : ℤ} (hc : c ≠ 0) :
    IsRelPrime f (C c) := by
  intro q hqf hqc
  obtain ⟨a, _, rfl⟩ := (dvd_C_iff_exists hc).mp hqc
  exact (hf a ((C_dvd_iff_dvd_coeff a f).mp hqf)).map C

/-- For any primitive equation, integer divisibility is exactly rational
coefficient divisibility. -/
theorem PrimitiveIntegerPolynomial.rational_map_dvd_iff
    {f g : MvPolynomial σ ℤ} (hf : PrimitiveIntegerPolynomial f) :
    MvPolynomial.map (Int.castRingHom ℚ) f ∣ MvPolynomial.map (Int.castRingHom ℚ) g ↔ f ∣ g := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨b, u, hb, hu⟩ := mvPolynomial_integer_multiple q
    have he : C b * g = f * u := by
      apply map_injective (Int.castRingHom ℚ) Int.cast_injective
      rw [map_mul, map_mul, map_C, hu, hq]
      grind [Int.coe_castRingHom]
    exact (hf.isRelPrime_constant hb).dvd_of_dvd_mul_left ⟨u, he⟩
  exact map_dvd (map (Int.castRingHom ℚ))

/-- Extract a primitive integer equation by the gcd of its nonzero
coefficients. The scalar is nonzero. -/
theorem exists_primitive_integer_factor (f : MvPolynomial σ ℤ) (hf : f ≠ 0) :
    ∃ (c : ℤ) (g : MvPolynomial σ ℤ), c ≠ 0 ∧ PrimitiveIntegerPolynomial g ∧ f = C c * g := by
  classical
  obtain ⟨v, hv, hvprim⟩ := f.support.extract_gcd f.coeff (MvPolynomial.support_nonempty.mpr hf)
  let g := ∑ m ∈ f.support, monomial m (v m)
  have hcoeff (m) (hm : m ∈ f.support) : g.coeff m = v m := by
    aesop
  have he : f = C (f.support.gcd f.coeff) * g := by
    nth_rw 1 [f.as_sum]
    simp only [g, Finset.mul_sum, C_mul_monomial]
    apply Finset.sum_congr rfl
    tauto
  have hc : f.support.gcd f.coeff ≠ 0 := by
    grind
  refine ⟨f.support.gcd f.coeff, g, hc, ?_, he⟩
  intro c hc
  apply isUnit_iff_dvd_one.mpr
  rw [← hvprim]
  apply Finset.dvd_gcd
  grind

end

end
end CCDN
