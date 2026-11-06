module

public import NearlyMinimax.CellProjection


@[expose] public section

open Matrix MeasureTheory MvPolynomial
open scoped BigOperators

noncomputable section
namespace NearlyMinimax


variable {ι κ : Type*} {d ℓ : ℕ}
/-- A rectangular monomial index set; it contains every monomial of
bounded total degree and has `(order+1)^dimension` elements. -/
abbrev PolynomialBox (d ℓ : ℕ) := Fin d → Fin (ℓ + 1)

def polynomialBoxExponent  (γ : PolynomialBox d ℓ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (γ i).val)

@[simp] theorem polynomial_box_exponent_apply 
    (γ : PolynomialBox d ℓ) (i : Fin d) : polynomialBoxExponent γ i = (γ i).val := by
  change Finsupp.equivFunOnFinite (Finsupp.equivFunOnFinite.symm (fun i => (γ i).val)) i = _
  simp

theorem polynomial_box_exponent_injective  :
    Function.Injective (polynomialBoxExponent (d := d) (ℓ := ℓ)) := by
  intro γ δ he
  funext i
  apply Fin.ext
  simpa only [polynomial_box_exponent_apply] using congrArg (fun w : Fin d →₀ ℕ => w i) he

/-- Every bounded-degree polynomial has an exact expansion in the
finite rectangular monomial feature set. -/
theorem polynomial_as_box_sum  (P : MvPolynomial (Fin d) ℝ)
    (hP : P.totalDegree ≤ ℓ) :
    P = ∑ γ : PolynomialBox d ℓ,
      monomial (polynomialBoxExponent γ) (P.coeff (polynomialBoxExponent γ)) := by
  apply MvPolynomial.ext
  intro w
  simp only [coeff_sum, coeff_monomial]
  by_cases hw : ∀ i, w i ≤ ℓ
  · let γw : PolynomialBox d ℓ := fun i => ⟨w i, Nat.lt_succ_of_le (hw i)⟩
    have hencode : polynomialBoxExponent γw = w := by
      ext i
      simp only [polynomial_box_exponent_apply, γw]
    have heq : ∀ γ : PolynomialBox d ℓ, polynomialBoxExponent γ = w ↔ γ = γw := by
      intro γ
      rw [← hencode]
      exact ⟨fun h => polynomial_box_exponent_injective h, fun h => congrArg polynomialBoxExponent h⟩
    simp only [heq]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hencode]
  · have hz : P.coeff w = 0 := by
      by_contra hn
      exact hw (by have hsupport  := mem_support_iff.mpr hn; have hsum := (le_totalDegree hsupport).trans hP; rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hsum; intro i; exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hsum)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro γ hγ
    have hne : polynomialBoxExponent γ ≠ w := by
      intro he
      apply hw
      intro i
      rw [← he, polynomial_box_exponent_apply]
      exact Nat.le_of_lt_succ (γ i).isLt
    simp only [hne, ite_false]

/-- Polynomial evaluation is exactly finite feature-vector evaluation. -/
theorem polynomial_box_evaluation  (P : MvPolynomial (Fin d) ℝ)
    (hP : P.totalDegree ≤ ℓ) (x : Covariate d) :
    eval x P = ∑ γ : PolynomialBox d ℓ,
      (P.coeff (polynomialBoxExponent γ)) * ∏ i, (x i) ^ (γ i).val := by
  conv_lhs => rw [polynomial_as_box_sum P hP]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [polynomial_box_exponent_apply]

/-- The empirical design for cellwise polynomial approximation,
using the actual sample covariates and their actual cell labels. -/
def cellPolynomialDesign   [DecidableEq κ]
    (cell : ι → κ) (x : ι → Covariate d) : Matrix ι (κ × PolynomialBox d ℓ) ℝ :=
  fun i j => if cell i = j.1 then ∏ r, (x i r) ^ (j.2 r).val else 0

/-- A genuine polynomial approximation error controls residual energy;
the fitting and projection steps are proved from matrix evaluation. -/
theorem cell_polynomial_residual_bound  
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (cell x) (f : ι → ℝ)
    (P : κ → MvPolynomial (Fin d) ℝ) (hP : ∀ c, (P c).totalDegree ≤ ℓ)
    (b : ℝ) (hb : 0 ≤ b) (herror : ∀ i, |f i - eval (x i) (P (cell i))| ≤ b) :
    projectionEnergy ((1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := ℓ) cell x)) *ᵥ f) ≤
      Fintype.card ι * b ^ 2 := by
  have hs := empirical_design_projection_spec (cellPolynomialDesign (ℓ := ℓ) cell x)
  have hA := projection_complement _ hs.1 hs.2.1
  have h_cell_polynomial_residual_kills : (1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := ℓ) cell x)) *ᵥ
      (fun i => eval (x i) (P (cell i))) = 0 := by
    have h_cell_polynomial_design_evaluation : cellPolynomialDesign (ℓ := ℓ) cell x *ᵥ
        (fun j => (P j.1).coeff (polynomialBoxExponent j.2)) =
        fun i => eval (x i) (P (cell i)) := by
      ext i
      simp only [cellPolynomialDesign, mulVec, dotProduct, Fintype.sum_prod_type, ite_mul, zero_mul]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
      rw [Finset.sum_eq_single (cell i)]
      · simp only [ite_true]
        rw [polynomial_box_evaluation (P (cell i)) (hP (cell i)) (x i)]
        apply Finset.sum_congr rfl
        intro γ hγ
        exact mul_comm _ _
      · intro c hc hne
        simp only [Ne.symm hne, ite_false]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    rw [← h_cell_polynomial_design_evaluation, sub_mulVec, one_mulVec,
      empirical_design_fixes_evaluation, sub_self]
  exact projection_approximation_bound _ hA.1 hA.2 f _
    h_cell_polynomial_residual_kills b hb herror


end NearlyMinimax
