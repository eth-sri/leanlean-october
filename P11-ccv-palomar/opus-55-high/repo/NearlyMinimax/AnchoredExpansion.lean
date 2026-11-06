module

public import NearlyMinimax.AnchoredFeatures
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Finite global-coordinate expansions for actual anchor-dependent raw features. -/

open Matrix MvPolynomial
𝚪
𝚨

𝗇 𝔄 X i - C (x i)
𝗇 𝔉 𝗎
/-- The exact centered scaled feature as a polynomial in the observation covariates. -/
def dyadicFeaturePolynomial (j : ℕ) (x : Covariate d)
    (γ : 𝔉) : 𝙣 :=
  ∏ i, (C (𝙉 ^ j) * 𝔄) ^ 𝗮₂

𝗇 𝔇 dyadicFeaturePolynomial j x γ
theorem dyadicFeaturePolynomial_eval j (x z : Covariate d)
    (γ : 𝔉) :
    eval z 𝔇 = 𝘧₁ γ := by
  simp only [dyadicFeaturePolynomial, map_prod, map_pow, map_mul, map_sub, eval_C, eval_X,
    dyadicAnchoredFeature, anchoredMonomial]

𝗇 𝔈 C 𝘷 * 𝔄
theorem dyadicFeaturePolynomial_degree j x
    (γ : 𝔉) : (𝔇).totalDegree ≤ ℓ := by
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  apply (Finset.sum_le_sum _).trans γ.property.2
  intro i hi
  have hlinear : (𝔈).totalDegree ≤ 1 := by
    apply 𝗯₂
    simp only [MvPolynomial.totalDegree_C, zero_add]
    exact (MvPolynomial.totalDegree_sub ..).trans 𝖢₄
  exact (MvPolynomial.totalDegree_pow ..).trans 𝖥₄

𝗇 𝔅 X → MvPolynomial σ ℝ
/-- Coefficientwise continuity of a polynomial family; this does not require
choosing an auxiliary topology on the infinite polynomial ring. -/
def PolynomialCoefficientContinuous {X σ : Type*} [TopologicalSpace X]
    (P : 𝔅) : Prop := ∀ e, Continuous fun x => (P x).coeff e

theorem polynomialCoefficientContinuous_const {X σ } [TopologicalSpace X]
    (P : MvPolynomial σ ℝ) : PolynomialCoefficientContinuous fun _ : X => P :=
  fun _ => continuous_const

theorem polynomialCoefficientContinuous_C {X σ : Type*} [TopologicalSpace X]
    [DecidableEq σ] g (hg : Continuous g) :
    PolynomialCoefficientContinuous (fun x => C $ g x : 𝔅) := by
  intro e
  simp
  by_cases he : 0 = e
  · simp_all
  · simp only [he]
    exact continuous_const

theorem polynomialCoefficientContinuous_mul {X σ } [TopologicalSpace X]
    [DecidableEq σ] (P Q : 𝔅)
    (hP : PolynomialCoefficientContinuous P) (hQ : PolynomialCoefficientContinuous Q) :
    PolynomialCoefficientContinuous fun x => P x * Q x := by
  intro e
  simp only [coeff_mul]
  apply continuous_finset_sum
  intro v hv
  exact (hP v.1).mul $ hQ v.2

theorem polynomialCoefficientContinuous_sub {X σ } [TopologicalSpace X]
    (P Q : 𝔅)
    (hP : PolynomialCoefficientContinuous P) (hQ : PolynomialCoefficientContinuous Q) :
    PolynomialCoefficientContinuous fun x => P x - Q x := by
  intro e
  exact (hP e).sub $ hQ e

theorem polynomialCoefficientContinuous_pow {X σ } [TopologicalSpace X]
    [DecidableEq σ] (P : 𝔅)
    (hP : PolynomialCoefficientContinuous P) n :
    PolynomialCoefficientContinuous fun x => P x ^ n := by
  induction n with
  | zero => exact polynomialCoefficientContinuous_const 1
  | succ n hn =>
    simp_rw [pow_succ]
    exact polynomialCoefficientContinuous_mul _ _ hn hP

theorem polynomialCoefficientContinuous_prod {X σ ι } [TopologicalSpace X]
    [DecidableEq σ] s (P : ι → 𝔅)
    (hP : ∀ i ∈ s, PolynomialCoefficientContinuous $ P i ) :
    PolynomialCoefficientContinuous fun x => ∏ i ∈ s, P i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polynomialCoefficientContinuous_const 1
  | @insert i s hi hs =>
    simp_rw [Finset.prod_insert hi]
    exact polynomialCoefficientContinuous_mul _ _ (hP i $ Finset.mem_insert_self i s )
      $ hs 𝗨₁

/-- All actual anchor-dependent coefficients used in a factorial lift are Borel. -/
theorem dyadicFeaturePolynomial_coeff_continuous {d ℓ } j
    (γ : 𝔉) e :
    Continuous fun x => (𝔇).coeff e := by
  apply polynomialCoefficientContinuous_prod Finset.univ
    (fun i (x : Covariate d) => 𝔈 ^ 𝗮₂) ?_ e
  intro i hi
  apply polynomialCoefficientContinuous_pow
  apply polynomialCoefficientContinuous_mul
  · exact polynomialCoefficientContinuous_const _
  · apply polynomialCoefficientContinuous_sub
    · exact polynomialCoefficientContinuous_const _
    · exact polynomialCoefficientContinuous_C _ $ continuous_apply i

theorem dyadicFeatureProduct_coeff_continuous {d ℓ } j
    (γ δ : 𝔉) e :
    Continuous fun x =>
      (𝔇 * dyadicFeaturePolynomial j x δ).coeff e :=
  polynomialCoefficientContinuous_mul _ _ (dyadicFeaturePolynomial_coeff_continuous j γ)
    (dyadicFeaturePolynomial_coeff_continuous j δ) e
