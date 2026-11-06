module

public import ValuedFieldTheory.Valuation.Henselian.Factorization.Assembly
public import ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialBounds

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Hensel obstruction to irreducibility

This file applies the explicit Hensel lemma from the coefficientwise Hensel construction to the
normalized residue input constructed by the coefficient-bound lemmas.  The result here is the
core contradiction for irreducible-polynomial lifting: a nontrivial factorization of
the reduction gives a nontrivial factorization over the complete valuation
ring, hence the mapped field polynomial is not irreducible.
-/


open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- algebraic obstruction: a field polynomial with a factor of
positive degree strictly smaller than its own degree is not irreducible. -/
theorem irreduciblePolynomial_not_irreducible_of_field_factor_natDegree_lt
    {K : Type*} [Field K] {f g h : K[X]}
    (hfactor : f = g * h)
    (hgpos : 0 < g.natDegree)
    (hglt : g.natDegree < f.natDegree) :
    ¬ Irreducible f := by
  intro hirr
  have hg_notunit : ¬ IsUnit g := by
    intro hgunit
    exact (Nat.ne_of_gt hgpos) (Polynomial.natDegree_eq_zero_of_isUnit hgunit)
  rcases hirr.isUnit_or_isUnit hfactor with hgunit | hhunit
  · exact hg_notunit hgunit
  · have hg_ne : g ≠ 0 := by
      intro hgzero
      simp [hgzero] at hgpos
    have hh_ne : h ≠ 0 := hhunit.ne_zero
    have hdeg : f.natDegree = g.natDegree := by
      simpa [hfactor, Polynomial.natDegree_eq_zero_of_isUnit hhunit] using
        (Polynomial.natDegree_mul hg_ne hh_ne)
    omega

/-- transport obstruction: a nontrivial factorization over the
closed-unit-ball valuation ring maps to a nontrivial field factorization. -/
theorem irreduciblePolynomial_not_irreducible_of_valuation_factorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {F G H : (absoluteValueValuationSubring v hnonarch)[X]}
    {f : K[X]} {r : ℕ}
    (hFmap : F.map (algebraMap
        (absoluteValueValuationSubring v hnonarch) K) = f)
    (hFdegree : F.natDegree = f.natDegree)
    (hfactor : F = G * H)
    (hGdegree : G.natDegree = r)
    (hrpos : 0 < r)
    (hrlt : r < F.natDegree) :
    ¬ Irreducible f := by
  let V := absoluteValueValuationSubring v hnonarch
  let φ : V →+* K := algebraMap V K
  have hφinj : Function.Injective φ := by
    intro x y hxy
    exact Subtype.ext (by simpa [φ] using hxy)
  let Gk : K[X] := G.map φ
  let Hk : K[X] := H.map φ
  have hfacK : f = Gk * Hk := by
    calc
      f = F.map φ := hFmap.symm
      _ = (G * H).map φ := by rw [hfactor]
      _ = G.map φ * H.map φ := by simp [Polynomial.map_mul]
      _ = Gk * Hk := rfl
  have hGkDegree : Gk.natDegree = r := by
    calc
      Gk.natDegree = G.natDegree := by
        simpa [Gk] using Polynomial.natDegree_map_eq_of_injective hφinj G
      _ = r := hGdegree
  have hGkpos : 0 < Gk.natDegree := by
    omega
  have hGklt : Gk.natDegree < f.natDegree := by
    simp_all
  exact irreduciblePolynomial_not_irreducible_of_field_factor_natDegree_lt
    hfacK hGkpos hGklt

/-- The common nonvanishing step in the three irreducible-polynomial lifting Hensel routes:
if a polynomial is `X ^ r` times a polynomial with nonzero constant
coefficient, then it is nonzero. -/
theorem irreduciblePolynomial_polynomial_ne_zero_of_eq_X_pow_mul_of_coeff_zero_ne_zero
    {k : Type*} [Field k] {P Q : k[X]} {r : ℕ}
    (hfactor : P = Polynomial.X ^ r * Q)
    (hQ0 : Q.coeff 0 ≠ 0) :
    P ≠ 0 := by
  have hQne : Q ≠ 0 := by
    intro hQzero
    simp_all
  simp_all

/-- scalar normalization preserves irreducibility: multiplying
by the inverse of a nonzero coefficient is multiplication by a unit. -/
theorem irreduciblePolynomial_irreducible_normalized_scale_of_irreducible
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hirr : Irreducible f) :
    Irreducible (Polynomial.C (f.coeff n)⁻¹ * f) := by
  have hmne : m ≠ 0 := ne_of_gt hmpos
  have hn_ne : f.coeff n ≠ 0 := by
    intro hzero
    simp_all
  have hunit :
      IsUnit (Polynomial.C (f.coeff n)⁻¹ : K[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hn_ne))
  exact (irreducible_isUnit_mul hunit).2 hirr
