module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite moment rules

The finite signed rules below are represented by their finite weighted-sum action.
This retains coincident atoms (so the sum of absolute weights is an upper bound on
measure total variation). Polynomial degree bounds count the number of distinct
nodes, and no interpolation property is assumed as a hypothesis.
-/

noncomputable section

namespace NearlyMinimax

open Polynomial Finset

section Cardinal

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

variable {s : Finset ι} {v : ι → F} (hv : Set.InjOn v s) {P : F[X]} (hP : P.degree < s.card) (a : ℕ)

include hv hP in
/-- Applying cardinal evaluation weights is evaluation at the chosen point. -/
theorem cardinal_evaluation_exact (x : F) :
    (∑ i ∈ s, (Lagrange.basis s v i).eval x * P.eval (v i)) = P.eval x := by
  have h := congrArg (fun p => p.eval x) (Lagrange.eq_interpolate hv hP)
  simpa only [Lagrange.interpolate_apply, eval_finset_sum, eval_mul, eval_C,
    mul_comm] using h.symm

include hv hP in
/-- Coefficients of cardinal polynomials extract that coefficient exactly. -/
theorem cardinal_coefficient_exact :
    (∑ i ∈ s, (Lagrange.basis s v i).coeff a * P.eval (v i)) = P.coeff a := by
  have h := congrArg (fun p => p.coeff a) (Lagrange.eq_interpolate hv hP)
  simp at h
  simpa only [mul_comm] using h.symm

include hv in
/-- Differentiating cardinal interpolation gives the finite derivative rule. -/
theorem cardinal_derivative_exact (P : F[X]) (hP : P.degree < s.card) (x : F) :
    (∑ i ∈ s, (Lagrange.basis s v i).derivative.eval x * P.eval (v i)) =
      P.derivative.eval x := by
  have h := congrArg (fun p => p.derivative.eval x)
    (Lagrange.eq_interpolate hv hP)
  simp [Lagrange.interpolate_apply, derivative_sum, derivative_C_mul,
    eval_finset_sum, eval_mul, eval_C] at h
  simpa only [mul_comm] using h.symm

/-- The exterior cardinal weight has the product formula in Lemma 3(a). -/
theorem cardinal_weight_at_zero (s : Finset ι) (v : ι → F) (i : ι) :
    (Lagrange.basis s v i).eval 0 = ∏ j ∈ s.erase i, v j / (v j - v i) := by
  simp only [Lagrange.basis, eval_prod, Lagrange.basisDivisor, eval_mul,
    eval_C, eval_sub, eval_X, zero_sub]
  apply Finset.prod_congr rfl
  intro j hj
  grind

include hv in
/-- The explicit exterior product rule reproduces every polynomial in its degree range. -/
theorem exterior_product_rule_exact (P : F[X]) (hP : P.degree < s.card) :
    (∑ i ∈ s, (∏ j ∈ s.erase i, v j / (v j - v i)) * P.eval (v i)) = P.eval 0 := by
  simpa only [cardinal_weight_at_zero] using cardinal_evaluation_exact hv hP 0

include hv in
/-- The coefficient rule has Kronecker monomial moments. -/
theorem cardinal_coefficient_monomial (b : ℕ) (hb : b < s.card) :
    (∑ i ∈ s, (Lagrange.basis s v i).coeff a * (v i) ^ b) =
      if b = a then 1 else 0 := by
  have hd : (X ^ b : F[X]).degree < s.card := by
    simpa using (WithBot.coe_lt_coe.mpr hb)
  simpa [coeff_X_pow, eq_comm] using cardinal_coefficient_exact hv hd a

end Cardinal

section
variable {q : ℕ} (b : Bool)

/-- The fixed scalar-response nodes from Lemma 3(c). -/
def responseNode (j : Fin (2 * q + 2)) : ℝ :=
  j.val / (2 * q + 1 : ℕ)

theorem responseNode_injective (q : ℕ) : Function.Injective (responseNode (q := q)) := by
  intro i j hij
  have hn : (2 * q + 1 : ℝ) ≠ 0 := by positivity
  have h : (i.val : ℝ) = j.val := by
    apply (div_left_inj' hn).mp
    simpa [responseNode] using hij
  exact Fin.ext (by exact_mod_cast h)

/-- The scalar-response extraction weights. -/
def responseWeight (j : Fin (2 * q + 2)) : ℝ :=
  (Lagrange.basis Finset.univ responseNode j).coeff 2

/-- Total absolute weight of the fixed second-coefficient extraction rule. -/
abbrev responseVariation (q : ℕ) : ℝ := ∑ j : Fin (2*q+2), |responseWeight j|

theorem responseVariation_bound {f : Fin (2*q+2) → ℝ} {B : ℝ} (hf : ∀ j, |f j| ≤ B) :
    |∑ j, responseWeight j * f j| ≤ responseVariation q * B := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [responseVariation, Finset.sum_mul]
  simp
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)

/-- The paper's fixed rule extracts the quadratic coefficient, including zero mass and mean. -/
theorem response_rule_moments (q a : ℕ) (ha : a ≤ 2 * q + 1) :
    (∑ j : Fin (2 * q + 2), responseWeight j * (responseNode j) ^ a) =
      if a = 2 then 1 else 0 := cardinal_coefficient_monomial
    (responseNode_injective q).injOn 2 a (by simpa using (show a < 2 * q + 2 by omega))

/-- Exactness of the fixed quadratic-extraction rule on every polynomial of the stated degree. -/
theorem response_rule_exact {P : ℝ[X]} (hP : P.degree < 2 * q + 2) :
    (∑ j : Fin (2 * q + 2), responseWeight j * P.eval (responseNode j)) =
      P.coeff 2 := cardinal_coefficient_exact
    (responseNode_injective q).injOn (by simpa using hP) 2

/-- The fixed response rule has zero total mass. -/
theorem response_zero_mass (q : ℕ) :
    (∑ j : Fin (2 * q + 2), responseWeight j) = 0 := by
  simpa using response_rule_moments q 0 (by omega)

/-- The fixed response rule has zero first moment. -/
theorem response_zero_mean (q : ℕ) :
    (∑ j : Fin (2 * q + 2), responseWeight j * responseNode j) = 0 := by
  simpa using response_rule_moments q 1 (by omega)

/-- A fair sign, represented on the two-point Boolean space. -/
def fairSign : ℝ := if b then 1 else -1

@[simp] theorem fairSign_abs : |fairSign b| = 1 := by cases b <;> norm_num [fairSign]

end

private theorem finite_sum_abs_bound {κ : Type*} [Fintype κ] (g b : κ → ℝ)
    (h : ∀ k, |g k| ≤ b k) : |∑ k, g k| ≤ ∑ k, b k := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (by bound)

section Covariance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section
variable {κ : Type*} (S : Finset κ) (C a : ℝ) (A : ι → ι → ℝ) (f g : (ι → ℝ) → ℝ)

/-- Fixed atoms of the covariance rule. They do not depend on the matrix. -/
def covarianceAtom (i j : ι) (s t : Bool) : ι → ℝ :=
  fun k => (fairSign s * (if i = k then 1 else 0) +
    fairSign t * (if j = k then 1 else 0)) / (2 * C)

/-- The factor `1/4` from fair sign averaging is included in the weight. -/
def covarianceWeight (i j : ι) (s t : Bool) : ℝ :=
  C ^ 2 / 2 * A i j * fairSign s * fairSign t

/-- The finite signed covariance kernel evaluated against a function. -/
def covarianceAction : ℝ :=
  ∑ i, ∑ j, ∑ s, ∑ t,
    covarianceWeight C A i j s t * f (covarianceAtom C i j s t)

private theorem sign_mass :
    (∑ s, ∑ t, C ^ 2 / 2 * a * fairSign s * fairSign t) = 0 := by
  simp [fairSign]

private theorem sign_mean (x y : ℝ) :
    (∑ s, ∑ t,
      (C ^ 2 / 2 * a * fairSign s * fairSign t) *
        ((fairSign s * x + fairSign t * y) / (2 * C))) = 0 := by
  simp [fairSign]
  ring

private theorem sign_second (x y u v : ℝ) (hC : C ≠ 0) :
    (∑ s, ∑ t,
      (C ^ 2 / 2 * a * fairSign s * fairSign t) *
        (((fairSign s * x + fairSign t * y) / (2 * C)) *
          ((fairSign s * u + fairSign t * v) / (2 * C)))) =
      a / 2 * (x * v + y * u) := by
  simp [fairSign]
  field_simp
  ring

/-- The action is additive in the test function. -/
theorem covarianceAction_add :
    covarianceAction C A (fun x => f x + g x) =
      covarianceAction C A f + covarianceAction C A g := by
  simp only [covarianceAction, mul_add, Finset.sum_add_distrib]

/-- The action is homogeneous in the test function. -/
theorem covarianceAction_mul :
    covarianceAction C A (fun x => a * f x) = a * covarianceAction C A f := by
  simp only [covarianceAction, mul_left_comm, Finset.mul_sum]

/-- The action commutes with a finite sum of test functions. -/
theorem covarianceAction_sum (f : κ → (ι → ℝ) → ℝ) :
    covarianceAction C A (fun x => ∑ i ∈ S, f i x) =
      ∑ i ∈ S, covarianceAction C A (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [covarianceAction]
  | @insert k S hk ih =>
      simp [Finset.sum_insert hk]
      rw [covarianceAction_add, ih]

/-- The covariance rule annihilates constants. -/
theorem covariance_zero_mass :
    covarianceAction C A (fun _ => 1) = 0 := by
  simp only [covarianceAction, covarianceWeight, mul_one]
  simp_rw [sign_mass]
  simp

/-- The covariance rule annihilates each coordinate. -/
theorem covariance_zero_mean (k : ι) :
    covarianceAction C A (fun x => x k) = 0 := by
  simp only [covarianceAction, covarianceWeight, covarianceAtom]
  simp_rw [sign_mean]
  simp

end

section
variable {C : ℝ}

/-- Without a symmetry assumption the second moment is the matrix's symmetric part. -/
theorem covariance_second_moment (A : ι → ι → ℝ) (hC : C ≠ 0) (k l : ι) :
    covarianceAction C A (fun x => x k * x l) = (A k l + A l k) / 2 := by
  simp only [covarianceAction, covarianceWeight, covarianceAtom]
  simp_rw [sign_second C _ _ _ _ _ hC]
  simp [mul_add, Finset.sum_add_distrib, mul_ite]
  ring

/-- For symmetric matrices the covariance rule has precisely the prescribed second moment. -/
theorem covariance_second_moment_symmetric {A : ι → ι → ℝ}
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) (k l : ι) :
    covarianceAction C A (fun x => x k * x l) = A k l := by
  rw [covariance_second_moment A hC, hA l k]
  ring

/-- Each atom lies in the coefficient ball of radius `1/C`. -/
theorem covarianceAtom_mem_ball (hC : 0 < C) (i j : ι) (s t : Bool) :
    (∑ k, |covarianceAtom C i j s t k|) ≤ C⁻¹ := by
  have hden : 0 < 2 * C := by positivity
  calc
    _ ≤
        ∑ k, (|(fairSign s * (if i = k then 1 else 0))| +
          |(fairSign t * (if j = k then 1 else 0))|) / (2 * C) := by
      apply Finset.sum_le_sum
      intro k hk
      dsimp [covarianceAtom]
      rw [abs_div, abs_of_pos hden]
      exact div_le_div_of_nonneg_right (abs_add_le _ _) (le_of_lt hden)
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      simp [apply_ite abs]
      field_simp
      ring

end

variable (C B : ℝ) (A : ι → ι → ℝ)

/-- The sum of absolute atom weights is the variation bound in the paper. -/
theorem covariance_weight_variation :
    (∑ i, ∑ j, ∑ s, ∑ t, |covarianceWeight C A i j s t|) =
      2 * C ^ 2 * ∑ i, ∑ j, |A i j| := by
  have hw (i j : ι) (s t : Bool) : |covarianceWeight C A i j s t| = C ^ 2 / 2 * |A i j| := by
    dsimp [covarianceWeight]
    rw [abs_mul, abs_mul, abs_mul, abs_div]
    simp
  simp_rw [hw]
  simp
  calc
    _ =
      ∑ i, ∑ j, 2 * C ^ 2 * |A i j| := by
        ring
    _ = _ := by simp [Finset.mul_sum]

/-- The signed-rule action is bounded by the atom variation times a uniform bound. -/
theorem covarianceAction_abs_le
    (f : (ι → ℝ) → ℝ)
    (hf : ∀ i j s t, |f (covarianceAtom C i j s t)| ≤ B) :
    |covarianceAction C A f| ≤ (2 * C ^ 2 * ∑ i, ∑ j, |A i j|) * B := by
  have ht (i j : ι) (s t : Bool) :
      |covarianceWeight C A i j s t * f (covarianceAtom C i j s t)| ≤
        |covarianceWeight C A i j s t| * B := by
    rw [abs_mul]
    bound
  have h := finite_sum_abs_bound
    (fun i => ∑ (j), ∑ s, ∑ t,
      covarianceWeight C A i j s t * f (covarianceAtom C i j s t))
    (fun i => ∑ (j), ∑ s, ∑ t, |covarianceWeight C A i j s t| * B)
    (fun i => finite_sum_abs_bound _ _ (fun j =>
      finite_sum_abs_bound _ _ (fun s => finite_sum_abs_bound _ _ (ht i j s))))
  simpa only [covarianceAction, ← Finset.sum_mul, covariance_weight_variation] using h

end Covariance

end NearlyMinimax
