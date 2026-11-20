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

The rereading is the algebra homomorphism sending the point variables to
constants and keeping the combining variables; it is injective, its left
inverse being the substitution which renames the point variables back and sends
the combining variables to the combining coordinates.

## Main definitions

* `combinedPointExp`, `combinedCoefExp` — the two blocks of an exponent vector
  of the combined dimension.
* `combinedCoefAlgHom` — the rereading of a polynomial in the combined
  variables as a polynomial in the combining variables with polynomial
  coefficients.
* `combinedCoef` — the coefficient of the combining monomial `μ`.

## Main statements

* `combinedCoefAlgHom_monomial` — the rereading of a monomial.
* `combinedCoefAlgHom_injective` — the rereading is injective.
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

/-- The point block of an exponent vector of the combined dimension. -/
def combinedPointExp : Fin m →₀ ℕ :=
  Finsupp.comapDomain (combinedPointVar m k) s (combinedPointVar_injective m k).injOn

/-- The combining block of an exponent vector of the combined dimension. -/
def combinedCoefExp : Fin k →₀ ℕ :=
  Finsupp.comapDomain (combinedCoefficientVar m k) s
    (combinedCoefficientVar_injective m k).injOn

@[simp] theorem combinedPointExp_apply (j : Fin m) :
    combinedPointExp s j = s (combinedPointVar m k j) := rfl

@[simp] theorem combinedCoefExp_apply (r : Fin k) :
    combinedCoefExp s r = s (combinedCoefficientVar m k r) := rfl

end

/-- A product over the combined dimension splits into the product over the point
coordinates and the product over the combining coordinates. -/
private theorem prod_combinedVar_split {M : Type*} [CommMonoid M] {m k : ℕ}
    (f : Fin (m + k) → M) :
    ∏ i : Fin (m + k), f i =
      (∏ j : Fin m, f (combinedPointVar m k j)) *
        ∏ r : Fin k, f (combinedCoefficientVar m k r) := by
  rw [← Fintype.prod_equiv finSumFinEquiv _ f fun _ => rfl,
    Fintype.prod_sum_type]
  rfl

/-! ## Rereading a polynomial in the combining variables -/

section

variable (K : Type*) [CommSemiring K] (m k : ℕ)

/-- The substitution reading the point variables as constants of the polynomial
ring in the point variables and keeping the combining variables. -/
def combinedCoefSubstitution :
    Fin (m + k) → MvPolynomial (Fin k) (MvPolynomial (Fin m) K) :=
  fun i => Sum.elim
    (fun j : Fin m => MvPolynomial.C (MvPolynomial.X j))
    (fun r : Fin k => MvPolynomial.X r) (finSumFinEquiv.symm i)

@[simp] theorem combinedCoefSubstitution_point
    (j : Fin m) :
    combinedCoefSubstitution K m k (combinedPointVar m k j) =
      MvPolynomial.C (MvPolynomial.X j) := by
  simp [combinedCoefSubstitution, combinedPointVar]

@[simp] theorem combinedCoefSubstitution_coefficient
    (r : Fin k) :
    combinedCoefSubstitution K m k (combinedCoefficientVar m k r) =
      (MvPolynomial.X r : MvPolynomial (Fin k) (MvPolynomial (Fin m) K)) := by
  simp [combinedCoefSubstitution, combinedCoefficientVar]

/-- The rereading of a polynomial in the `m + k` combined variables as a
polynomial in the `k` combining variables with coefficients in the polynomial
ring in the `m` point variables. -/
def combinedCoefAlgHom :
    MvPolynomial (Fin (m + k)) K →ₐ[K]
      MvPolynomial (Fin k) (MvPolynomial (Fin m) K) :=
  MvPolynomial.aeval (combinedCoefSubstitution K m k)

@[simp] theorem combinedCoefAlgHom_X
    (i : Fin (m + k)) :
    combinedCoefAlgHom K m k (MvPolynomial.X i) = combinedCoefSubstitution K m k i :=
  MvPolynomial.aeval_X _ _

theorem combinedCoefAlgHom_C (a : K) :
    combinedCoefAlgHom K m k (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  simp

end

/-- The rereading of a monomial: its exponent vector splits into the combining
block, which becomes the exponent of the outer monomial, and the point block,
which becomes the exponent of the inner monomial. -/
theorem combinedCoefAlgHom_monomial {K : Type*} [CommSemiring K] {m k : ℕ}
    (s : Fin (m + k) →₀ ℕ) (a : K) :
    combinedCoefAlgHom K m k (MvPolynomial.monomial s a) =
      MvPolynomial.monomial (combinedCoefExp s)
        (MvPolynomial.monomial (combinedPointExp s) a) := by
  classical
  set A := MvPolynomial (Fin k) (MvPolynomial (Fin m) K)
  have hL : combinedCoefAlgHom K m k (MvPolynomial.monomial s a) =
      MvPolynomial.C (MvPolynomial.C a) *
        ((∏ j : Fin m, (MvPolynomial.C (MvPolynomial.X j)) ^ s (combinedPointVar m k j)) *
          ∏ r : Fin k, (MvPolynomial.X r) ^ s (combinedCoefficientVar m k r)) := by
    simp [MvPolynomial.monomial_eq, Finsupp.prod_fintype, map_mul, map_prod, combinedCoefAlgHom_C]
    rw [prod_combinedVar_split]
    simp
  have hR : MvPolynomial.monomial (combinedCoefExp s)
        (MvPolynomial.monomial (combinedPointExp s) a) =
      MvPolynomial.C (MvPolynomial.C a) *
        ((∏ j : Fin m, (MvPolynomial.C (MvPolynomial.X j)) ^ s (combinedPointVar m k j)) *
          ∏ r : Fin k, (MvPolynomial.X r) ^ s (combinedCoefficientVar m k r)) := by
    rw [MvPolynomial.monomial_eq,
      Finsupp.prod_fintype _ _ fun _ => pow_zero _,
      MvPolynomial.monomial_eq,
      Finsupp.prod_fintype _ _ fun _ => pow_zero _, map_mul, map_prod]
    simp
    ring
  simp [*]

/-! ## Injectivity of the rereading -/

/-- The substitution inverting the rereading: rename the point variables back to
the point coordinates and send the combining variables to the combining
coordinates. -/
def combinedCoefInv (K : Type*) [CommSemiring K] (m k : ℕ) :
    MvPolynomial (Fin k) (MvPolynomial (Fin m) K) →+* MvPolynomial (Fin (m + k)) K :=
  MvPolynomial.eval₂Hom ((MvPolynomial.rename (combinedPointVar m k)).toRingHom)
    (fun r : Fin k => MvPolynomial.X (combinedCoefficientVar m k r))

section

variable {K : Type*} [CommSemiring K] {m k : ℕ}

theorem combinedCoefInv_combinedCoefAlgHom
    (p : MvPolynomial (Fin (m + k)) K) :
    combinedCoefInv K m k (combinedCoefAlgHom K m k p) = p := by
  have h : (combinedCoefInv K m k).comp
      (combinedCoefAlgHom K m k : MvPolynomial (Fin (m + k)) K →ₐ[K] _) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · simp [combinedCoefInv]
    · intro i
      rcases combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;>
        simp [combinedCoefInv]
  exact RingHom.congr_fun h p

/-- The rereading is injective: a polynomial in the combined variables is
determined by its coefficients in the combining variables. -/
theorem combinedCoefAlgHom_injective :
    Function.Injective (combinedCoefAlgHom K m k) :=
  Function.LeftInverse.injective combinedCoefInv_combinedCoefAlgHom

/-! ## The coefficients -/

/-- The coefficient of the combining monomial `μ` in `p`: a polynomial in the
point variables. -/
def combinedCoef
    (p : MvPolynomial (Fin (m + k)) K) (μ : Fin k →₀ ℕ) : MvPolynomial (Fin m) K :=
  (combinedCoefAlgHom K m k p).coeff μ

/-- The value at `u` of the coefficient of `μ` is the coefficient of `μ` in the
restriction of `p` at `u`. -/
theorem eval_combinedCoef
    (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) (μ : Fin k →₀ ℕ) :
    MvPolynomial.eval u (combinedCoef p μ) =
      (combinedRestrict p u).coeff μ := by
  have h : (MvPolynomial.mapAlgHom (MvPolynomial.aeval u)).comp (combinedCoefAlgHom K m k) =
      MvPolynomial.aeval (combinedRestrictSubstitution k u) := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;> simp
  have hp := AlgHom.congr_fun h p
  simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.mapAlgHom_apply] at hp
  rw [combinedRestrict, ← hp, combinedCoef, MvPolynomial.coeff_map]
  rfl

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
    grind
  conv_lhs => rw [q.as_sum]
  rw [Finset.sum_subset hsub, Finset.sum_image]
  · intro r _ r' _ hrr'
    exact Finsupp.single_left_injective one_ne_zero hrr'
  · intro μ _ hμ
    simp [MvPolynomial.notMem_support_iff.mp hμ]

section

variable {K : Type*} [CommSemiring K] {m k : ℕ}

section

variable (g : Fin k → MvPolynomial (Fin m) K)

/-- The rereading of a combined polynomial: its coefficients are the components
of the tuple, at the standard basis vectors. -/
theorem combinedCoefAlgHom_combinePolyTuple :
    combinedCoefAlgHom K m k (combinePolyTuple g) =
      ∑ r : Fin k, MvPolynomial.monomial (Finsupp.single r 1) (g r) := by
  classical
  have hrename : ∀ h : MvPolynomial (Fin m) K,
      combinedCoefAlgHom K m k (MvPolynomial.rename (combinedPointVar m k) h) =
        MvPolynomial.C h := by
    intro h
    induction h using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp_all
    | mul_X p j hp => simp [hp]
  rw [combinePolyTuple, map_sum]
  congr 1 with r
  rw [map_mul, combinedCoefAlgHom_X, (show combinedCoefSubstitution K m k (combinedCoefficientVar m k r) = (MvPolynomial.X r : MvPolynomial (Fin k) (MvPolynomial (Fin m) K)) by simp [combinedCoefSubstitution, combinedCoefficientVar]), hrename,
    mul_comm, MvPolynomial.C_mul_X_eq_monomial]

theorem combinedCoef_combinePolyTuple (r : Fin k) :
    combinedCoef (combinePolyTuple g) (Finsupp.single r 1) = g r := by
  classical
  rw [combinedCoef, combinedCoefAlgHom_combinePolyTuple, MvPolynomial.coeff_sum,
    Finset.sum_eq_single r]
  · simp
  · intro s _ hs
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun hEq => hs (Finsupp.single_left_injective one_ne_zero hEq)
  · intro h
    simp_all

end

/-- A polynomial in the combined variables is combined exactly when its
coefficients vanish outside the `k` standard basis vectors.  This is the
first half of the characterisation used in `lem:ld-combining-exact-linearity`. -/
theorem combinePolyTuple_combinedCoef_iff
    (p : MvPolynomial (Fin (m + k)) K) :
    (∃ g : Fin k → MvPolynomial (Fin m) K, p = combinePolyTuple g) ↔
      ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) → combinedCoef p μ = 0 := by
  classical
  constructor
  · rintro ⟨g, rfl⟩ μ hμ
    classical
    rw [combinedCoef, combinedCoefAlgHom_combinePolyTuple, MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [MvPolynomial.coeff_monomial, if_neg]
    grind
  · intro h
    refine ⟨fun r => combinedCoef p (Finsupp.single r 1), combinedCoefAlgHom_injective ?_⟩
    rw [combinedCoefAlgHom_combinePolyTuple]
    solve_by_elim [eq_sum_monomial_single]

/-! ## The degree bound on the coefficients -/

/-- The coefficient of `μ` as a sum over the support of `p`. -/
theorem combinedCoef_eq_sum
    (p : MvPolynomial (Fin (m + k)) K) (μ : Fin k →₀ ℕ) :
    combinedCoef p μ = ∑ s ∈ p.support,
      (if combinedCoefExp s = μ then
        MvPolynomial.monomial (combinedPointExp s) (p.coeff s) else 0) := by
  classical
  rw [combinedCoef]
  conv_lhs => rw [p.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  congr 1 with s
  simp [combinedCoefAlgHom_monomial]

end

/-- The coefficients inherit the individual-degree bound of `p`: the individual
degree of `c_μ` in the point variable `j` is at most the individual degree of
`p` in the corresponding point coordinate. -/
theorem degreeOf_combinedCoef_le {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} (hp : ∀ i, p.degreeOf i ≤ d)
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

end

end MIPStarRE.QPBT
