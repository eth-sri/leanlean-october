module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.Coefficients

/-!
# Exact linearity in the combining variables

The recovery step of the combining reduction needs to know that a polynomial in
the combined variables which is not the combined polynomial of any tuple only
rarely restricts to a linear form in the combining variables: writing
`p = ∑_μ c_μ α^μ` with coefficients `c_μ` in the point variables, the
polynomial `p` is combined exactly when `c_μ` vanishes for every exponent vector
`μ` outside the `k` standard basis vectors, and the restriction `p(u, ·)` is a
linear form exactly when `c_μ(u)` vanishes for every such `μ`.  Fixing one such
`μ` with `c_μ ≠ 0`, whose total degree is at most `m d`, the Schwartz--Zippel
lemma bounds the probability of `c_μ(u) = 0` by `m d / q`.

## Main statements

* `exists_eq_combiningLinearForm_iff` — a polynomial in the combining variables
  is a linear form exactly when its coefficients vanish off the standard basis
  vectors.
* `combinedRestrict_combiningLinearForm_avg_le` — `lem:ld-combining-exact-linearity`.
* `directCombinedExactLinearity_avg_le` — the same bound in the parameters of
  the directly indexed low-degree game.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1477`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:575-600`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## Linear forms in terms of their coefficients -/

section

variable {K : Type*}

/-- A linear form is the sum of its monomials at the standard basis vectors. -/
theorem combiningLinearForm_eq_sum_monomial [CommSemiring K] {k : ℕ}
    (c : Fin k → K) :
    combiningLinearForm c =
      ∑ r : Fin k, MvPolynomial.monomial (Finsupp.single r 1) (c r) := Finset.sum_congr rfl fun r x => MvPolynomial.C_mul_X_eq_monomial

/-- A polynomial in the combining variables is a linear form exactly when its
coefficients vanish outside the `k` standard basis vectors. -/
theorem exists_eq_combiningLinearForm_iff [CommSemiring K] {k : ℕ}
    (P : MvPolynomial (Fin k) K) :
    (∃ c : Fin k → K, P = combiningLinearForm c) ↔
      ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) →
        P.coeff μ = 0 := by
  classical
  constructor
  · rintro ⟨c, rfl⟩ μ hμ
    classical
    rw [combiningLinearForm_eq_sum_monomial, MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun hEq => hμ r hEq.symm
  · intro h
    constructor
    rw [combiningLinearForm_eq_sum_monomial]
    exact eq_sum_monomial_single P h

/-- The restriction of `p` at `u` is a linear form exactly when the values at
`u` of the coefficients off the standard basis vectors all vanish. -/
theorem exists_eq_combiningLinearForm_combinedRestrict_iff [CommSemiring K]
    {m k : ℕ} (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) :
    (∃ c : Fin k → K, combinedRestrict p u = combiningLinearForm c) ↔
      ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) →
        MvPolynomial.eval u (combinedCoef p μ) = 0 := by
  rw [exists_eq_combiningLinearForm_iff]
  simp only [eval_combinedCoef]

/-! ## The exact-linearity estimate -/

open scoped Classical in
/-- `lem:ld-combining-exact-linearity`.  A polynomial of individual degree at
most `d` in the combined variables which is not the combined polynomial of any
tuple restricts, at a uniformly sampled point of the original space, to a linear
form in the combining variables with probability at most `m d / q`. -/
theorem combinedRestrict_combiningLinearForm_avg_le [Field K] [Fintype K]
    [DecidableEq K] {m k d : ℕ} {p : MvPolynomial (Fin (m + k)) K}
    (hp : p ∈ polyFunc (m + k) K d)
    (hnc : ∀ g : Fin k → MvPolynomial (Fin m) K, p ≠ combinePolyTuple g) :
    avgOver (uniformDistribution (Fin m → K))
        (fun u => if ∃ c : Fin k → K, combinedRestrict p u = combiningLinearForm c then
          (1 : Error) else 0) ≤
      ((((m * d : ℕ) : ℚ≥0) / Fintype.card K : ℚ≥0) : Error) := by
  classical
  obtain ⟨μ, hμ, hne⟩ : ∃ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) ∧
      combinedCoef p μ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := (combinePolyTuple_combinedCoef_iff p).mpr hcon
    exact hnc g hg
  calc
    _
      ≤ avgOver (uniformDistribution (Fin m → K))
          (fun u => if MvPolynomial.eval u (combinedCoef p μ) =
            MvPolynomial.eval u 0 then 1 else 0) := by
        refine avgOver_mono _ _ _ fun u => ?_
        by_cases hu : ∃ c : Fin k → K, combinedRestrict p u = combiningLinearForm c
        · have h0 : MvPolynomial.eval u (combinedCoef p μ) =
              MvPolynomial.eval u 0 := (exists_eq_combiningLinearForm_combinedRestrict_iff p u).mp hu μ hμ
          simp [*]
        · split_ifs <;> norm_num
    _ = _ :=
        polynomialAgreement_avg_eq_agreementProbability _ _
    _ ≤ _ := by
        exact_mod_cast schwartzZippel_totalDegree hne ((totalDegree_le_mul_of_degreeOf_le
                                                         (degreeOf_combinedCoef_le (degreeOf_le_of_mem_polyFunc hp) μ))) (by simp)

end

open scoped Classical in
/-- `lem:ld-combining-exact-linearity` in the parameters of the directly indexed
low-degree game: an outcome of the combined game which is not combined restricts
to a linear form in the combining variables with probability at most `m d / q`
over a uniformly sampled point of the original space. -/
theorem directCombinedExactLinearity_avg_le (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d) (hnc : ¬ IsDirectCombined D p) :
    avgOver (uniformDistribution (DirectPoint D))
        (fun u => if ∃ c : Fin D.k → DirectScalarQ D,
          combinedRestrict p.1 u = combiningLinearForm c then (1 : Error) else 0) ≤
      ((D.m * D.d : ℕ) : Error) / D.q := by
  classical
  have hbound := combinedRestrict_combiningLinearForm_avg_le (d := D.d) p.2 (by
    intro g hg
    refine hnc ⟨fun r => ⟨g r, by
                                 have h := (mem_polyFunc_of_degreeOf_le
                                             (degreeOf_combinedCoef_le (degreeOf_le_of_mem_polyFunc p.2) (Finsupp.single r 1)))
                                 rwa [hg, combinedCoef_combinePolyTuple] at h⟩, ?_⟩
    exact Subtype.ext hg.symm)
  refine LE.le.trans_eq hbound ?_
  rw [card_directScalarQ]
  push_cast
  ring

/-! ## The collision estimate at a fixed point -/

variable {K : Type*}

/-- A nonzero coefficient of `μ` comes from a monomial of `p` whose combining
block is `μ`. -/
theorem exists_mem_support_of_combinedCoef_ne_zero [CommSemiring K] {m k : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} {μ : Fin k →₀ ℕ} (h : combinedCoef p μ ≠ 0) :
    ∃ s ∈ p.support, combinedCoefExp s = μ := by
  classical
  by_contra hcon
  push Not at hcon
  apply h
  rw [combinedCoef_eq_sum]
  exact Finset.sum_eq_zero fun s hs => if_neg (hcon s hs)

section

variable [CommSemiring K] {m k d : ℕ} {p : MvPolynomial (Fin (m + k)) K}

/-- The restriction of `p` to a point inherits the individual-degree bound of
`p` in the combining variables. -/
theorem degreeOf_combinedRestrict_le (hp : ∀ i, p.degreeOf i ≤ d) (u : Fin m → K)
    (r : Fin k) : (combinedRestrict p u).degreeOf r ≤ d := by
  classical
  rw [MvPolynomial.degreeOf_le_iff]
  intro μ hμ
  obtain ⟨s, hs, rfl⟩ := exists_mem_support_of_combinedCoef_ne_zero (by
    intro h0
    refine MvPolynomial.mem_support_iff.mp hμ ?_
    rw [← eval_combinedCoef, h0, map_zero])
  exact MvPolynomial.degreeOf_le_iff.mp (hp (combinedCoefficientVar m k r)) s hs

end

open scoped Classical in
/-- The collision estimate of the recovery step at a fixed point: if the
restriction of `p` at `u` is not a linear form, then the value of `p` at the
combined point agrees with the combined point answer of a tuple `b` at a
uniformly sampled combining vector with probability at most `k d / q`.  Both
polynomials in the combining variables have total degree at most `k d`, and
they are distinct because one of them is a linear form. -/
theorem combinedRestrict_collision_avg_le [Field K] [Fintype K]
    [DecidableEq K] {m k d : ℕ} {p : MvPolynomial (Fin (m + k)) K}
    (hp : p ∈ polyFunc (m + k) K d) (hkd : 1 ≤ k * d) (u : Fin m → K) (b : Fin k → K)
    (hu : ∀ c : Fin k → K, combinedRestrict p u ≠ combiningLinearForm c) :
    avgOver (uniformDistribution (Fin k → K))
        (fun α => if MvPolynomial.eval (combinedPoint u α) p =
          ∑ r : Fin k, b r * α r then (1 : Error) else 0) ≤
      ((((k * d : ℕ) : ℚ≥0) / Fintype.card K : ℚ≥0) : Error) := by
  classical
  calc
    _
      = _ := by
        apply avgOver_congr
        intro α
        simp [eval_combinedRestrict]
    _ = (polynomialAgreementProbability k K (combinedRestrict p u)
          (combiningLinearForm b) : Error) :=
        polynomialAgreement_avg_eq_agreementProbability _ _
    _ ≤ _ := by
        exact_mod_cast schwartzZippel_totalDegree (hu b) ((totalDegree_le_mul_of_degreeOf_le
                                                            (degreeOf_combinedRestrict_le (degreeOf_le_of_mem_polyFunc hp) u))) (le_trans (combiningLinearForm_totalDegree_le_one b) hkd)

end

end MIPStarRE.QPBT
