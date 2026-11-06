module
public import GafniTao.HeathBrownSourceAverage
public import GafniTao.FordLemma51Fibers

@[expose] public section

/-!
# Polynomial phases in Heath-Brown Lemma 1

This file fixes the literal Taylor polynomial used in the source and proves
that its constant term and integral coefficient changes have no effect on the
norm of the associated exponential sum.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem heathBrownPhase_eq_fordAdditiveCharacter (x : ℝ) :
    heathBrownPhase x = fordAdditiveCharacter x := by
  unfold heathBrownPhase fordAdditiveCharacter
  congr 1
  push_cast
  ring

theorem heathBrownPhase_add (x y : ℝ) :
    heathBrownPhase (x + y) = heathBrownPhase x * heathBrownPhase y := by
  simp only [heathBrownPhase_eq_fordAdditiveCharacter,
    fordAdditiveCharacter_add]

/-- Heath-Brown's Taylor polynomial
`f_n(x)=sum_{j=0}^{k-1} f^(j)(n)x^j/j!`. -/
noncomputable def heathBrownTaylorPolynomial
    (k : ℕ) (f : ℝ → ℝ) (n x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k,
    iteratedDeriv j f n * x ^ j / (j.factorial : ℝ)

/-- The same Taylor phase after removing its constant term. -/
noncomputable def heathBrownReducedTaylorPolynomial
    (k : ℕ) (f : ℝ → ℝ) (n x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 k,
    iteratedDeriv j f n * x ^ j / (j.factorial : ℝ)

theorem heathBrownTaylorPolynomial_eq_constant_add_reduced
    {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ) (n x : ℝ) :
    heathBrownTaylorPolynomial k f n x =
      f n + heathBrownReducedTaylorPolynomial k f n x := by
  unfold heathBrownTaylorPolynomial heathBrownReducedTaylorPolynomial
  have hrange : Finset.range k = insert 0 (Finset.Ico 1 k) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hrange, Finset.sum_insert (by simp)]
  simp

noncomputable def heathBrownTaylorPolynomialSum
    (k Q : ℕ) (f : ℝ → ℝ) (n : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 Q,
    heathBrownPhase (heathBrownTaylorPolynomial k f n h)

noncomputable def heathBrownReducedTaylorPolynomialSum
    (k Q : ℕ) (f : ℝ → ℝ) (n : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 Q,
    heathBrownPhase (heathBrownReducedTaylorPolynomial k f n h)

theorem heathBrownTaylorPolynomialSum_eq_phase_mul_reduced
    {k : ℕ} (hk : 1 ≤ k) (Q : ℕ) (f : ℝ → ℝ) (n : ℝ) :
    heathBrownTaylorPolynomialSum k Q f n =
      heathBrownPhase (f n) *
        heathBrownReducedTaylorPolynomialSum k Q f n := by
  unfold heathBrownTaylorPolynomialSum heathBrownReducedTaylorPolynomialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← heathBrownPhase_add,
    ← heathBrownTaylorPolynomial_eq_constant_add_reduced hk]

/-- Removing the constant Taylor coefficient preserves the exact norm. -/
theorem norm_heathBrownTaylorPolynomialSum_eq_reduced
    {k : ℕ} (hk : 1 ≤ k) (Q : ℕ) (f : ℝ → ℝ) (n : ℝ) :
    ‖heathBrownTaylorPolynomialSum k Q f n‖ =
      ‖heathBrownReducedTaylorPolynomialSum k Q f n‖ := by
  rw [heathBrownTaylorPolynomialSum_eq_phase_mul_reduced hk, norm_mul,
    norm_heathBrownPhase, one_mul]


