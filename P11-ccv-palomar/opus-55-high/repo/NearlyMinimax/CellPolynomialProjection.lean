module

public import NearlyMinimax.CellProjection
public import RoughRegime.Macro
public import RoughRegime.Notation


@[expose] public section

open Matrix MeasureTheory MvPolynomial
𝚪

noncomputable section
𝚨

/-- A rectangular monomial index set; it contains every monomial of
bounded total degree and has `(order+1)^dimension` elements. -/
abbrev PolynomialBox (d ℓ : ℕ) := 𝘛

𝗇 𝔊 𝗫₂
𝗇 𝔏 𝘇
𝗃 𝔓 fun i => ἀ
def polynomialBoxExponent (γ : 𝔊) : 𝖨₁ :=
  Finsupp.equivFunOnFinite.symm 𝔓 𝔏

@[simp] theorem polynomial_box_exponent_apply
    (γ : 𝔊) i : polynomialBoxExponent γ i = 𝔏 := by
  rfl

theorem polynomial_box_exponent_injective :
    Function.Injective $ polynomialBoxExponent (d := d) (ℓ := ℓ) := by
  intro γ δ he
  funext i
  apply Fin.ext
  simpa only [polynomial_box_exponent_apply] using congrArg (fun w => w i) he

𝗇 𝔅 𝙣
𝗇 𝔑 ∀ i, w i ≤ ℓ
/-- Total degree bounds every coordinate of every nonzero coefficient. -/
theorem polynomial_coefficient_box_bound (P : 𝔅)
    (hP : P.totalDegree ≤ ℓ) w (hw : P.coeff w ≠ 0) :
    𝔑 := by
  have hsum := (le_totalDegree $ mem_support_iff.mpr hw ).trans hP
  rw [Finsupp.sum_fintype _ _ 𝘦] at hsum
  intro i
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) $ Finset.mem_univ i ).trans hsum

𝗇 𝔐 P.coeff $ polynomialBoxExponent γ
/-- Every bounded-degree polynomial has an exact expansion in the
finite rectangular monomial feature set. -/
theorem polynomial_as_box_sum (P : 𝔅)
    (hP : P.totalDegree ≤ ℓ) :
    P = ∑ γ : 𝔊,
      monomial (polynomialBoxExponent γ) 𝔐 := by
  classical
  apply MvPolynomial.ext
  intro w
  simp
  by_cases hw : 𝔑
  · let γw : 𝔊 := fun i => ⟨w i, Nat.lt_succ_of_le $ hw i ⟩
    have hencode : polynomialBoxExponent γw = w := by
      bound
    have heq : ∀ γ , polynomialBoxExponent γ = w ↔ γ = γw := by
      bound
    simp only [heq]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hencode]
  · have hz : P.coeff w = 0 := by
      by_contra hn
      exact hw $ polynomial_coefficient_box_bound P hP w hn
    simp_all

/-- Polynomial evaluation is exactly finite feature-vector evaluation. -/
theorem polynomial_box_evaluation (P : 𝔅)
    (hP : P.totalDegree ≤ ℓ) (x : Covariate d) :
    eval x P = ∑ γ : 𝔊,
      𝔐 * ∏ i, x i ^ 𝔏 := by
  conv_lhs => rw [polynomial_as_box_sum P hP]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [eval_monomial, 𝗉₁]
  rfl

𝗇 𝔉 ι → Covariate d
𝗇 𝔍 ι → κ
/-- The empirical design for cellwise polynomial approximation,
using the actual sample covariates and their actual cell labels. -/
def cellPolynomialDesign [DecidableEq κ]
    (cell : 𝔍) (x : 𝔉) : Matrix ι (κ × 𝔊) ℝ :=
  fun i j => if cell i = j.1 then ∏ r, x i r ^ (j.2 r).val else 0

𝗇 𝔄 cellPolynomialDesign (ℓ := ℓ) cell x
𝗃 𝔔 ἀ $ cell i
𝗇 𝔒 𝔔 P
𝗇 𝔇 eval (x i) 𝔒
𝗇 𝔈 ∀ c, (P c).totalDegree ≤ ℓ
/-- The actual design evaluates every cellwise bounded-degree polynomial. -/
theorem cell_polynomial_design_evaluation
    [Fintype κ] [DecidableEq κ] (cell : 𝔍) (x : 𝔉)
    (P : κ → 𝔅) (hP : 𝔈) :
    𝔄 *ᵥ
      (fun j => (P j.1).coeff $ polynomialBoxExponent j.2 ) =
      𝔓 𝔇 := by
  classical
  ext i
  simp only [cellPolynomialDesign, mulVec, dotProduct, Fintype.sum_prod_type, ite_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [𝔔 Finset.sum_eq_single]
  · rw [polynomial_box_evaluation 𝔒 𝔔 hP $ x i ]
    grind
  · grind
  · simp

𝗇 𝔎 1 - empiricalDesignProjection 𝔄
/-- Every concrete cellwise polynomial fitted by this matrix is killed
by its exact residual projector, including irregular or deficient designs. -/
theorem cell_polynomial_residual_kills
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (cell : 𝔍) (x : 𝔉)
    (P : κ → 𝔅) (hP : 𝔈) :
    𝔎 *ᵥ
      𝔓 𝔇 = 0 := by
  rw [← cell_polynomial_design_evaluation cell x P hP, sub_mulVec, one_mulVec,
    empirical_design_fixes_evaluation, sub_self]

/-- A genuine polynomial approximation error controls residual energy;
the fitting and projection steps are proved from matrix evaluation. -/
theorem cell_polynomial_residual_bound
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (cell : 𝔍) (x : 𝔉) (f : 𝙛)
    (P : κ → 𝔅) (hP : 𝔈)
    b (hb : 𝘸) (herror : ∀ i, |f i - 𝔇| ≤ b) :
    projectionEnergy (𝔎 *ᵥ f) ≤
      Fintype.card ι * 𝘺 := by
  have hs := empirical_design_projection_spec 𝔄
  have hA := projection_complement _ hs.1 hs.2.1
  exact projection_approximation_bound _ hA.1 hA.2 f _
    (cell_polynomial_residual_kills cell x P hP) b hb herror


/-- The box design has a fixed number of monomial columns per cell. -/
theorem cell_polynomial_residual_degrees
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (cell : 𝔍) (x : 𝔉) :
    (Fintype.card ι : ℝ) - Fintype.card κ * (ℓ + 1 : ℕ) ^ d ≤
      (𝔎).trace := by
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow] using
    empirical_design_residual_degrees $ cellPolynomialDesign cell x

/-- Monomial evaluation and cell labels give a Borel polynomial design. -/
theorem cell_polynomial_design_measurable {X ι κ } {d ℓ : ℕ}
    [MeasurableSpace X] [Fintype ι] [Fintype κ] [DecidableEq κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (cell : X → 𝔍) (x : X → 𝔉)
    (hcell : Measurable cell) (hx : Measurable x) :
    Measurable fun ω => cellPolynomialDesign (ℓ := ℓ) (cell ω) $ x ω := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  apply Measurable.ite ( 𝘜 hcell $ measurableSet_singleton j.1 )
    _ measurable_const
  fun_prop
