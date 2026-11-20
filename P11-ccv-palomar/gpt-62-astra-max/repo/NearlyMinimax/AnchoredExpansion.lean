module

public import NearlyMinimax.AnchoredFeatures

@[expose] public section

/-! Finite global-coordinate expansions for actual anchor-dependent raw features. -/

noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace NearlyMinimax

section
variable {d ℓ : ℕ} (j : ℕ) (x z : Covariate d) (γ : AnchoredIndex d ℓ)

/-- The exact centered scaled feature as a polynomial in the observation covariates. -/
def dyadicFeaturePolynomial : MvPolynomial (Fin d) ℝ :=
  ∏ i, (C (2 ^ j) * (X i - C (x i))) ^ (γ.val i).val

theorem dyadicFeaturePolynomial_eval :
    eval z (dyadicFeaturePolynomial j x γ) = dyadicAnchoredFeature j x z γ := by
  simp [dyadicFeaturePolynomial, dyadicAnchoredFeature, anchoredMonomial]

theorem dyadicFeaturePolynomial_degree : (dyadicFeaturePolynomial j x γ).totalDegree ≤ ℓ := by
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  apply (Finset.sum_le_sum _).trans γ.property.2
  intro i hi
  have hlinear : (C (2 ^ j) * (X i - C (x i))).totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, zero_add]
    exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left _ hlinear)

end

section
variable {X σ ι : Type*} [TopologicalSpace X]

/-- Coefficientwise continuity of a polynomial family; this does not require
choosing an auxiliary topology on the infinite polynomial ring. -/
def PolynomialCoefficientContinuous
    (P : X → MvPolynomial σ ℝ) : Prop := ∀ e, Continuous (fun x => (P x).coeff e)

theorem polynomialCoefficientContinuous_const
    (P : MvPolynomial σ ℝ) : PolynomialCoefficientContinuous (fun _ : X => P) :=
  fun _ => continuous_const

theorem polynomialCoefficientContinuous_C
    [DecidableEq σ] {g : X → ℝ} (hg : Continuous g) :
    PolynomialCoefficientContinuous (fun x => C (g x) : X → MvPolynomial σ ℝ) := by
  intro e
  simp
  by_cases he : 0 = e
  · simp_all
  · simp [he]
    exact continuous_const

theorem polynomialCoefficientContinuous_mul
    [DecidableEq σ] {P Q : X → MvPolynomial σ ℝ}
    (hP : PolynomialCoefficientContinuous P) (hQ : PolynomialCoefficientContinuous Q) :
    PolynomialCoefficientContinuous (fun x => P x * Q x) := by
  intro e
  simp [coeff_mul]
  apply continuous_finset_sum
  intro v hv
  exact (hP v.1).mul (hQ v.2)

theorem polynomialCoefficientContinuous_sub
    (P Q : X → MvPolynomial σ ℝ)
    (hP : PolynomialCoefficientContinuous P) (hQ : PolynomialCoefficientContinuous Q) :
    PolynomialCoefficientContinuous (fun x => P x - Q x) := fun e => (hP e).sub (hQ e)

theorem polynomialCoefficientContinuous_pow
    [DecidableEq σ] (P : X → MvPolynomial σ ℝ)
    (hP : PolynomialCoefficientContinuous P) (n : ℕ) :
    PolynomialCoefficientContinuous (fun x => P x ^ n) := by
  induction n with
  | zero => exact polynomialCoefficientContinuous_const 1
  | succ n hn =>
    exact polynomialCoefficientContinuous_mul hn hP

theorem polynomialCoefficientContinuous_prod
    [DecidableEq σ] {s : Finset ι} {P : ι → X → MvPolynomial σ ℝ}
    (hP : ∀ i ∈ s, PolynomialCoefficientContinuous (P i)) :
    PolynomialCoefficientContinuous (fun x => ∏ i ∈ s, P i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polynomialCoefficientContinuous_const 1
  | @insert i s hi hs =>
    simp_rw [Finset.prod_insert hi]
    exact polynomialCoefficientContinuous_mul (hP i (Finset.mem_insert_self i s))
      (hs (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

end

variable {d ℓ : ℕ} (j : ℕ) (γ δ : AnchoredIndex d ℓ) (e : Fin d →₀ ℕ)

/-- All actual anchor-dependent coefficients used in a factorial lift are Borel. -/
theorem dyadicFeaturePolynomial_coeff_continuous :
    Continuous (fun x => (dyadicFeaturePolynomial j x γ).coeff e) := by
  apply polynomialCoefficientContinuous_prod ?_ e
  intro i hi
  apply polynomialCoefficientContinuous_pow
  apply polynomialCoefficientContinuous_mul
  · exact polynomialCoefficientContinuous_const _
  · apply polynomialCoefficientContinuous_sub
    · exact polynomialCoefficientContinuous_const _
    · exact polynomialCoefficientContinuous_C (continuous_apply i)

theorem dyadicFeatureProduct_coeff_continuous :
    Continuous (fun x =>
      (dyadicFeaturePolynomial j x γ * dyadicFeaturePolynomial j x δ).coeff e) :=
  polynomialCoefficientContinuous_mul (dyadicFeaturePolynomial_coeff_continuous j γ)
    (dyadicFeaturePolynomial_coeff_continuous j δ) e

end NearlyMinimax
