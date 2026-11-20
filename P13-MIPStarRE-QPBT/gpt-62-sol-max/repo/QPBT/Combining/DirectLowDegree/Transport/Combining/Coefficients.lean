module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.Restriction

/-!
# The coefficients of a polynomial in the combining variables

The recovery step of the combining reduction reads a polynomial `p` in the
`m + k` combined variables as a polynomial in the `k` combining variables whose
coefficients `c_μ` are polynomials in the `m` point variables, and characterises
the two properties it needs in terms of those coefficients: `p` is the combined
polynomial of a tuple exactly when `c_μ` vanishes for every exponent vector `μ`
outside the `k` standard basis vectors, and the restriction `p(u, ·)` is a
linear form exactly when `c_μ(u)` vanishes for every such `μ`.  The
individual degrees of the coefficients are bounded by those of `p`, so each
`c_μ` has total degree at most `m d` and the Schwartz--Zippel lemma applies to
it.

The rereading uses the polynomial algebra equivalence for a sum of variable sets.

## Main definitions

* `combinedPointExp`, `combinedCoefExp` — the two blocks of an exponent vector
  of the combined dimension.
* `combinedCoefEquiv` — the rereading of a polynomial in the combined
  variables as a polynomial in the combining variables with polynomial
  coefficients.
* `combinedCoef` — the coefficient of the combining monomial `μ`.

## Main statements

* `combinedCoefEquiv_monomial` — the rereading of a monomial.
* `eval_combinedCoef` — the value at `u` of `c_μ` is the coefficient of `μ` in
  the restriction `p(u, ·)`.
* `combinePolyTuple_combinedCoef_iff` — `p` is combined exactly when `c_μ`
  vanishes off the standard basis vectors.
* `degreeOf_combinedCoef_le`, `totalDegree_combinedCoef_le` — the degree bounds.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1470`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:575-600`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The two blocks of an exponent vector -/

section

variable {m k : ℕ} (s : Fin (m + k) →₀ ℕ)
include m k s

/-- The point block of an exponent vector of the combined dimension. -/
def combinedPointExp : Fin m →₀ ℕ :=
  Finsupp.comapDomain (combinedPointVar m k) s (combinedPointVar_injective m k).injOn

/-- The combining block of an exponent vector of the combined dimension. -/
def combinedCoefExp : Fin k →₀ ℕ :=
  Finsupp.comapDomain (combinedCoefficientVar m k) s
    (combinedCoefficientVar_injective m k).injOn

@[simp] theorem combinedPointExp_apply (j : Fin m) :
    combinedPointExp s j = s (combinedPointVar m k j) := rfl

end

@[simp] theorem combinedCoefExp_apply {m k : ℕ} (s : Fin (m + k) →₀ ℕ) (r : Fin k) :
    combinedCoefExp s r = s (combinedCoefficientVar m k r) := rfl

/-- A monomial splits into its outer combining exponent and inner point exponent. -/
theorem combinedCoefEquiv_monomial {K : Type*} [CommSemiring K] {m k : ℕ}
    (s : Fin (m + k) →₀ ℕ) (a : K) :
    combinedCoefEquiv K m k (MvPolynomial.monomial s a) =
      MvPolynomial.monomial (combinedCoefExp s)
        (MvPolynomial.monomial (combinedPointExp s) a) := by
  have h : Finsupp.sumFinsuppAddEquivProdFinsupp (s.mapDomain (combinedVariableEquiv m k)) =
      (combinedCoefExp s, combinedPointExp s) := by
    apply Prod.ext <;> apply Finsupp.ext <;> intro j <;>
      simp only [Finsupp.fst_sumFinsuppAddEquivProdFinsupp, Finsupp.snd_sumFinsuppAddEquivProdFinsupp,
        Finsupp.mapDomain_equiv_apply, combinedPointExp_apply, combinedCoefExp_apply] <;> rfl
  simp only [combinedCoefEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_monomial, MvPolynomial.sumAlgEquiv]
  simp only [MvPolynomial.monomial, AddMonoidAlgebra.lsingle_apply,
    AddMonoidAlgebra.domCongr_single, h, AddMonoidAlgebra.curryAlgEquiv_single]

/-! ## The coefficients -/

section

variable {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K)
include K m k p

/-- The coefficient of the combining monomial `μ` in `p`: a polynomial in the
point variables. -/
def combinedCoef (μ : Fin k →₀ ℕ) : MvPolynomial (Fin m) K :=
  (combinedCoefEquiv K m k p).coeff μ

/-- The value at `u` of the coefficient of `μ` is the coefficient of `μ` in the
restriction of `p` at `u`. -/
theorem eval_combinedCoef (u : Fin m → K) (μ : Fin k →₀ ℕ) :
    MvPolynomial.eval u (combinedCoef p μ) =
      (combinedRestrict p u).coeff μ := rfl

end

/-! ## Combined polynomials in terms of the coefficients -/

/-- A polynomial in the combining variables supported on the standard basis
vectors is the sum of its monomials at those vectors. -/
theorem eq_sum_monomial_single {B : Type*} [CommSemiring B] {k : ℕ}
    (q : MvPolynomial (Fin k) B)
    (h : ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) →
      q.coeff μ = 0) :
    q = ∑ r : Fin k, MvPolynomial.monomial (Finsupp.single r 1)
      (q.coeff (Finsupp.single r 1)) := by
  classical
  have hsub : q.support ⊆ Finset.image (fun r : Fin k => Finsupp.single r 1) Finset.univ := by
    intro μ hμ
    by_contra hcon
    refine MvPolynomial.mem_support_iff.mp hμ (h μ fun r hr => hcon ?_)
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr.symm⟩
  conv_lhs => rw [q.as_sum]
  rw [Finset.sum_subset hsub, Finset.sum_image]
  · intro r _ r' _ hrr'
    exact Finsupp.single_left_injective one_ne_zero hrr'
  · simp_all

section

variable {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K)
include K m k g

/-- The rereading of a combined polynomial: its coefficients are the components
of the tuple, at the standard basis vectors. -/
theorem combinedCoefEquiv_combinePolyTuple :
    combinedCoefEquiv K m k (combinePolyTuple g) =
      ∑ r : Fin k, MvPolynomial.monomial (Finsupp.single r 1) (g r) := by
  classical
  have hrename : (combinedCoefEquiv K m k).toAlgHom.comp
      (MvPolynomial.rename (combinedPointVar m k)) =
        IsScalarTower.toAlgHom K (MvPolynomial (Fin m) K) _ := by
    ext j
    simp [MvPolynomial.algebraMap_eq]
  rw [combinePolyTuple, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, combinedCoefEquiv_X_coefficient]
  change MvPolynomial.X r * ((combinedCoefEquiv K m k).toAlgHom.comp
    (MvPolynomial.rename (combinedPointVar m k))) (g r) = _
  rw [hrename, IsScalarTower.toAlgHom_apply, MvPolynomial.algebraMap_eq, mul_comm,
    MvPolynomial.C_mul_X_eq_monomial]

theorem combinedCoef_combinePolyTuple (r : Fin k) :
    combinedCoef (combinePolyTuple g) (Finsupp.single r 1) = g r := by
  classical
  rw [combinedCoef, combinedCoefEquiv_combinePolyTuple, MvPolynomial.coeff_sum,
    Finset.sum_eq_single r]
  · simp
  · intro s _ hs
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun hEq => hs (Finsupp.single_left_injective one_ne_zero hEq)
  · simp_all

theorem combinedCoef_combinePolyTuple_eq_zero {μ : Fin k →₀ ℕ}
    (hμ : ∀ r : Fin k, μ ≠ Finsupp.single r 1) :
    combinedCoef (combinePolyTuple g) μ = 0 := by
  classical
  rw [combinedCoef, combinedCoefEquiv_combinePolyTuple, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [MvPolynomial.coeff_monomial, if_neg]
  exact fun hEq => hμ r hEq.symm

end

/-- A polynomial in the combined variables is combined exactly when its
coefficients vanish outside the `k` standard basis vectors.  This is the
first half of the characterisation used in `lem:ld-combining-exact-linearity`. -/
theorem combinePolyTuple_combinedCoef_iff {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) :
    (∃ g : Fin k → MvPolynomial (Fin m) K, p = combinePolyTuple g) ↔
      ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) → combinedCoef p μ = 0 := by
  classical
  constructor
  · rintro ⟨g, rfl⟩ μ hμ
    exact combinedCoef_combinePolyTuple_eq_zero g hμ
  · intro h
    refine ⟨fun r => combinedCoef p (Finsupp.single r 1), (combinedCoefEquiv K m k).injective ?_⟩
    rw [combinedCoefEquiv_combinePolyTuple]
    exact eq_sum_monomial_single (combinedCoefEquiv K m k p) h

/-! ## The degree bound on the coefficients -/

/-- The coefficient of `μ` as a sum over the support of `p`. -/
theorem combinedCoef_eq_sum {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (μ : Fin k →₀ ℕ) :
    combinedCoef p μ = ∑ s ∈ p.support,
      (if combinedCoefExp s = μ then
        MvPolynomial.monomial (combinedPointExp s) (p.coeff s) else 0) := by
  classical
  rw [combinedCoef]
  conv_lhs => rw [p.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  simp_all [combinedCoefEquiv_monomial, MvPolynomial.coeff_monomial]

section

variable {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K}
include K m k d p

/-- The coefficients inherit the individual-degree bound of `p`: the individual
degree of `c_μ` in the point variable `j` is at most the individual degree of
`p` in the corresponding point coordinate. -/
theorem degreeOf_combinedCoef_le (hp : ∀ i, p.degreeOf i ≤ d)
    (μ : Fin k →₀ ℕ) (j : Fin m) : (combinedCoef p μ).degreeOf j ≤ d := by
  classical
  rw [MvPolynomial.degreeOf_le_iff]
  intro ν hν
  rw [combinedCoef_eq_sum] at hν
  obtain ⟨s, hs, hνs⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hν)
  by_cases hc : combinedCoefExp s = μ
  · rw [if_pos hc] at hνs
    have hνeq : ν = combinedPointExp s := by
      have := MvPolynomial.support_monomial_subset hνs
      simpa using this
    subst hνeq
    exact MvPolynomial.degreeOf_le_iff.mp (hp (combinedPointVar m k j)) s hs
  · rw [if_neg hc] at hνs
    simp at hνs

section

variable (hp : p ∈ polyFunc (m + k) K d)
include hp

/-- The coefficients of a polynomial of individual degree at most `d` lie in the
low individual degree class in the point variables. -/
theorem combinedCoef_mem_polyFunc (μ : Fin k →₀ ℕ) :
    combinedCoef p μ ∈ polyFunc m K d :=
  mem_polyFunc_of_degreeOf_le
    (degreeOf_combinedCoef_le (degreeOf_le_of_mem_polyFunc hp) μ)

/-- The components of a combined polynomial of individual degree at most `d`
have individual degree at most `d`: they are among its coefficients. -/
theorem mem_polyFunc_of_combinePolyTuple
    {g : Fin k → MvPolynomial (Fin m) K} (hg : p = combinePolyTuple g) (r : Fin k) :
    g r ∈ polyFunc m K d := by
  have h := combinedCoef_mem_polyFunc hp (Finsupp.single r 1)
  rwa [hg, combinedCoef_combinePolyTuple] at h

/-- The coefficients of a polynomial of individual degree at most `d` have total
degree at most `m d`, which is the bound the Schwartz--Zippel lemma is applied
to in `lem:ld-combining-exact-linearity`. -/
theorem totalDegree_combinedCoef_le (μ : Fin k →₀ ℕ) :
    (combinedCoef p μ).totalDegree ≤ m * d :=
  totalDegree_le_mul_of_degreeOf_le
    (degreeOf_combinedCoef_le (degreeOf_le_of_mem_polyFunc hp) μ)

end

end

end

end MIPStarRE.QPBT
