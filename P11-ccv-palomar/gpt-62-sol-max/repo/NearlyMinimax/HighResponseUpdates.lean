module

public import NearlyMinimax.AtomicRules
public import NearlyMinimax.LowSmoothnessVariance

@[expose] public section

/-! Actual finite scalar extraction and signed covariance resets of the
high-smoothness local response operator. -/
noncomputable section
open MeasureTheory Set Polynomial
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A ternary response on an affine regression line, as an actual polynomial. -/
def ternaryLinePolynomial (a f V δ : ℝ) (y : Fin 3) : ℝ[X] :=
  C (ternaryMass a f V y) + monomial 1 (δ * ternaryMeanDerivative a f y) +
    monomial 2 (δ ^ 2 * ternaryVarianceDerivative a y)

theorem ternary_line_polynomial_eval (a f V δ z : ℝ) (y : Fin 3) :
    (ternaryLinePolynomial a f V δ y).eval z = ternaryMass a (f + z * δ) V y := by
  fin_cases y <;> simp [ternaryLinePolynomial, ternaryMass, ternaryMeanDerivative,
    ternaryVarianceDerivative, div_eq_mul_inv] <;> ring

theorem ternary_line_polynomial_natDegree (a f V δ : ℝ) (y : Fin 3) :
    (ternaryLinePolynomial a f V δ y).natDegree ≤ 2 := by
  apply (natDegree_add_le _ _).trans (max_le ?_ (natDegree_monomial_le _))
  exact (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_monomial_le _).trans (by omega)))

/-- Complete finite product likelihood on the same line. -/
def responseLinePolynomial (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) : ℝ[X] := ∏ i, ternaryLinePolynomial a (f i) V (δ i) (y i)

section
variable (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3)

theorem response_line_polynomial_eval (z : ℝ) :
    (responseLinePolynomial n a V f δ y).eval z =
      ∏ i, ternaryMass a (f i + z * δ i) V (y i) := by
  simp only [responseLinePolynomial, eval_prod, ternary_line_polynomial_eval]

theorem response_line_polynomial_natDegree : (responseLinePolynomial n a V f δ y).natDegree ≤ 2 * n := by
  simpa [responseLinePolynomial, mul_comm] using
    (natDegree_prod_le Finset.univ (fun i => ternaryLinePolynomial a (f i) V (δ i) (y i))).trans
      (Finset.sum_le_sum (fun i _ => ternary_line_polynomial_natDegree a (f i) V (δ i) (y i)))

end

/-- Exact cardinal quadratic extraction of the genuine likelihood through
count q, including arbitrary offsets and incoming regression fields. -/
theorem response_line_rule_exact (q n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) (hn : n ≤ q) :
    (∑ j : Fin (2 * q + 2), responseWeight q j *
      ∏ i, ternaryMass a (f i + responseNode q j * δ i) V (y i)) =
      (responseLinePolynomial n a V f δ y).coeff 2 := by
  simpa only [response_line_polynomial_eval] using response_rule_exact q
    (responseLinePolynomial n a V f δ y)
    ((degree_le_of_natDegree_le ((response_line_polynomial_natDegree n a V f δ y).trans
      (show 2 * n ≤ 2 * q + 1 by omega))).trans_lt (by norm_cast; omega))

/-- Formal quadratic coefficient equals half the genuine second directional
product derivative, so its heat contraction can be evaluated explicitly. -/
theorem response_line_quadratic_coefficient (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) :
    2 * (responseLinePolynomial n a V f δ y).coeff 2 =
      finiteProductSecond Finset.univ
        (fun i z => ternaryMass a (f i + z * δ i) V (y i))
        (fun i z => δ i * ternaryMeanDerivative a (f i + z * δ i) (y i))
        (fun i _ => (δ i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0 := by
  let Q := responseLinePolynomial n a V f δ y
  have hd : (fun z => Q.derivative.eval z) = ternaryProductFirst a V f δ y := by
    funext z
    exact (Q.hasDerivAt z).unique (by
      simpa only [Q, response_line_polynomial_eval, ternaryLineMass] using
        ternary_product_hasDerivAt a V f δ y z)
  have hsecond := ternary_product_first_hasDerivAt a V f δ y 0
  rw [← hd] at hsecond
  have he := (Q.derivative.hasDerivAt 0).unique hsecond
  change Q.derivative.derivative.eval 0 = ternaryProductSecond a V f δ y 0 at he
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_derivative] at he
  norm_num only [Nat.cast_ofNat, Nat.cast_one, mul_one, Nat.zero_add] at he
  exact (mul_comm _ _).trans he

/-- The real scalar cardinal action has the all-count quadratic derivative
bound; its affine part cancels exactly by the proved moments. -/
theorem response_scalar_action_abs_bound (q : ℕ) (H D E : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivAt H (D z) z)
    (hD : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivAt D (E z) z)
    (hE : ∀ z ∈ Icc (0 : ℝ) 1, |E z| ≤ B)
    (hnodes : ∀ j : Fin (2 * q + 2), responseNode q j ∈ Icc (0 : ℝ) 1) :
    |∑ j : Fin (2 * q + 2), responseWeight q j * H (responseNode q j)| ≤
      (∑ j : Fin (2 * q + 2), |responseWeight q j|) * B := by
  have he : (∑ j : Fin (2 * q + 2), responseWeight q j * H (responseNode q j)) =
      ∑ j : Fin (2 * q + 2), responseWeight q j *
        (H (responseNode q j) - H 0 - responseNode q j * D 0) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
    simp [← Finset.sum_mul, response_zero_mass, response_zero_mean]
  rw [he]
  exact abs_weighted_sum_le fun j _ => affine_remainder_abs_bound (convex_Icc 0 1) (by norm_num)
    (fun _ hz => (abs_of_nonneg hz.1).trans_le hz.2) H D E B hB hH hD hE _ (hnodes j)

section Covariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Incoming coefficients are reset by the actual scalar mark and covariance atom. -/
def coefficientReset (c v : ι → ℝ) (z : ℝ) : ι → ℝ :=
  fun i => (1 - z) * c i + z * v i

/-- The paper's B_A as a genuine finite signed action. -/
def responseMatrixAction (q : ℕ) (C : ℝ) (A : ι → ι → ℝ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  covarianceAction C A (fun v => ∑ j : Fin (2 * q + 2),
    responseWeight q j * Φ (coefficientReset c v (responseNode q j)))

theorem responseMatrixAction_zero_mass (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) :
    responseMatrixAction q C A c (fun _ => 1) = 0 := by
  simp [responseMatrixAction, response_zero_mass, covarianceAction]

theorem covariance_displacement_second (C : ℝ) (A : ι → ι → ℝ)
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) (c : ι → ℝ) (k l : ι) :
    covarianceAction C A (fun v => (v k - c k) * (v l - c l)) = A k l := by
  have hf : (fun v : ι → ℝ => (v k - c k) * (v l - c l)) =
      (fun v => v k * v l + (-c l) * v k + (-c k) * v l + c k * c l * 1) := by
    funext v
    ring
  rw [hf, covarianceAction_add, covarianceAction_add, covarianceAction_add,
    covarianceAction_mul, covarianceAction_mul, covarianceAction_mul,
    covariance_second_moment_symmetric C A hC hA, covariance_zero_mean,
    covariance_zero_mean, covariance_zero_mass]
  ring

theorem responseNode_mem_unit (q : ℕ) (j : Fin (2 * q + 2)) :
    responseNode q j ∈ Icc (0 : ℝ) 1 := by
  have hden : (0 : ℝ) < (2 * q + 1 : ℕ) := by positivity
  constructor
  · apply div_nonneg <;> positivity
  · apply (div_le_one hden).mpr
    exact_mod_cast (show j.val ≤ 2 * q + 1 by omega)

omit [DecidableEq ι] in
theorem coefficientReset_mem_ball (C : ℝ) (c v : ι → ℝ) (z : ℝ)
    (hz : z ∈ Icc (0 : ℝ) 1)
    (hc : ∑ i, |c i| ≤ C⁻¹) (hv : ∑ i, |v i| ≤ C⁻¹) :
    (∑ i, |coefficientReset c v z i|) ≤ C⁻¹ := by
  calc
    _ ≤ ∑ i, ((1 - z) * |c i| + z * |v i|) := by
      apply Finset.sum_le_sum
      intro i _
      apply (abs_add_le _ _).trans_eq
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hz.2] : 0 ≤ 1 - z), abs_of_nonneg hz.1]
    _ = (1 - z) * (∑ i, |c i|) + z * (∑ i, |v i|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (1 - z) * C⁻¹ + z * C⁻¹ := add_le_add
      (mul_le_mul_of_nonneg_left hc (by linarith [hz.2])) (mul_le_mul_of_nonneg_left hv hz.1)
    _ = _ := by ring

/-- The finite spatial polynomial frame is evaluated without any abstract
smoothness or response assumptions. -/
def spatialFrameCovariance (A : ι → ι → ℝ) {n : ℕ} (φ : Fin n → ι → ℝ)
    (i l : Fin n) : ℝ := ∑ k, ∑ m, φ i k * φ l m * A k m

def coefficientRegression {n : ℕ} (η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) : Fin n → ℝ :=
  fun i => g i + η * w i * ∑ k, φ i k * c k

def coefficientDirection {n : ℕ} (η : ℝ) (w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c v : ι → ℝ) : Fin n → ℝ :=
  fun i => η * w i * ∑ k, φ i k * (v k - c k)

omit [DecidableEq ι] in
theorem coefficientRegression_reset {n : ℕ} (η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c v : ι → ℝ) (z : ℝ) :
    coefficientRegression η g w φ (coefficientReset c v z) =
      fun i => coefficientRegression η g w φ c i + z * coefficientDirection η w φ c v i := by
  funext i
  have hs : (∑ k, φ i k * coefficientReset c v z k) =
      (∑ k, φ i k * c k) + z * ((∑ k, φ i k * v k) - ∑ k, φ i k * c k) := by
    calc
      _ = ∑ k, (φ i k * c k + z * (φ i k * v k - φ i k * c k)) := by
        apply Finset.sum_congr rfl
        intro k _
        dsimp [coefficientReset]
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [coefficientRegression, coefficientDirection, hs, mul_sub, Finset.sum_sub_distrib]
  ring

theorem covariance_direction_product {n : ℕ} (C η : ℝ) (A : ι → ι → ℝ)
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) (w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (i l : Fin n) :
    covarianceAction C A (fun v => coefficientDirection η w φ c v i *
      coefficientDirection η w φ c v l) = η ^ 2 * w i * w l * spatialFrameCovariance A φ i l := by
  have he : (fun v : ι → ℝ => coefficientDirection η w φ c v i * coefficientDirection η w φ c v l) =
      (fun v => η ^ 2 * w i * w l *
        ∑ k, ∑ m, (φ i k * φ l m) * ((v k - c k) * (v m - c m))) := by
    funext v
    simp only [coefficientDirection, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl <;> grind
  rw [he, covarianceAction_mul, covarianceAction_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [covarianceAction_sum]
  simp [covarianceAction_mul, covariance_displacement_second C A hC hA]

/-- Real response likelihood of a single local coefficient state. -/
def highResponseProduct {n : ℕ} (a V η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  ∏ i, ternaryMass a (coefficientRegression η g w φ c i) V (y i)

/-- The variance derivative before substituting a common variance. -/
def highResponseVarianceTerm {n : ℕ} (a V η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) * ∏ l ∈ (Finset.univ : Finset (Fin n)).erase i,
    ternaryMass a (coefficientRegression η g w φ c l) V (y l)

/-- The mixed response derivative, with two distinct response coordinates differentiated. -/
def highResponseMixedTerm {n : ℕ} (a V η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) (i l : Fin n) : ℝ :=
  ternaryMeanDerivative a (coefficientRegression η g w φ c l) (y l) *
    ternaryMeanDerivative a (coefficientRegression η g w φ c i) (y i) *
    ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase l,
      ternaryMass a (coefficientRegression η g w φ c k) V (y k)

section
variable {n : ℕ} (q : ℕ) (hn : n ≤ q)
    (C a V η : ℝ) (A : ι → ι → ℝ) (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3)
include hn hC hA

/-- The cardinal rule contracts the full likelihood Hessian against the spatial covariance. -/
theorem high_response_matrix_expansion :
    responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) =
      η ^ 2 * ∑ i, ((w i) ^ 2 * spatialFrameCovariance A φ i i * highResponseVarianceTerm a V η g w φ c y i +
        (1 / 2 : ℝ) * ∑ l ∈ Finset.univ.erase i,
          w l * w i * spatialFrameCovariance A φ l i * highResponseMixedTerm a V η g w φ c y i l) := by
  let f := coefficientRegression η g w φ c
  let δ := coefficientDirection η w φ c
  let e := highResponseVarianceTerm a V η g w φ c y
  let M := highResponseMixedTerm a V η g w φ c y
  have hs (v : ι → ℝ) : (∑ j, responseWeight q j *
        highResponseProduct a V η g w φ (coefficientReset c v (responseNode q j)) y) =
      (1 / 2 : ℝ) * ∑ i, ((2 * e i) * (δ v i * δ v i) +
        ∑ l ∈ Finset.univ.erase i, M i l * (δ v l * δ v i)) := by
    simp only [highResponseProduct, coefficientRegression_reset]
    rw [response_line_rule_exact q n a V f (δ v) y hn]
    have h := response_line_quadratic_coefficient n a V f (δ v) y
    rw [← mul_right_inj' (by norm_num : (2 : ℝ) ≠ 0), h, ← mul_assoc]
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
    simp only [finiteProductSecond, finiteProductFirst, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul, ternary_heat_identity, add_comm]
    congr 1
    · dsimp [e, highResponseVarianceTerm]; ring
    · apply Finset.sum_congr rfl
      intro l _
      dsimp [M, highResponseMixedTerm, f]; ring
  simp only [responseMatrixAction, hs, δ, covarianceAction_mul, covarianceAction_sum, covarianceAction_add,
    covariance_direction_product C η A hC hA w φ c, Finset.mul_sum, mul_add]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  · dsimp [e]; ring
  · apply Finset.sum_congr rfl
    intros
    dsimp [M]; ring

/-- Spatial cardinal covariance cancels every off-diagonal product derivative.
This is the actual heat identity of the realized finite signed update. -/
theorem high_response_matrix_heat
    (d : Fin n → ℝ)
    (hdiag : ∀ i l, spatialFrameCovariance A φ i l = if i = l then d i else 0) :
    responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) =
      η ^ 2 * ∑ i, (w i) ^ 2 * d i * highResponseVarianceTerm a V η g w φ c y i := by
  simp_all [high_response_matrix_expansion]

end

/-- All-count cardinal action bound propagated through the genuine product
likelihood. The assumptions are individual legality and displacement bounds. -/
theorem response_scalar_product_action_abs_bound (q n : ℕ) (hn : 1 ≤ n)
    (a V η ρ : ℝ) (f δ : Fin n → ℝ) (y : Fin n → Fin 3)
    (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hf : ∀ z ∈ Icc (0 : ℝ) 1, ∀ i, |f i + z * δ i| ≤ ρ)
    (hp : ∀ z ∈ Icc (0 : ℝ) 1, ∀ i u, 0 ≤ ternaryMass a (f i + z * δ i) V u)
    (hδ : ∀ i, |δ i| ≤ 2 * η) :
    |∑ j : Fin (2 * q + 2), responseWeight q j *
      ∏ i, ternaryMass a (f i + responseNode q j * δ i) V (y i)| ≤
      (∑ j : Fin (2 * q + 2), |responseWeight q j|) *
        (4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2) * n ^ 2 * η ^ 2) := by
  let A := (2 * ρ + a) / a ^ 2
  let S := 2 / a ^ 2
  have Hb : 0 ≤ S := by positivity
  apply response_scalar_action_abs_bound q _ (ternaryProductFirst a V f δ y)
    (ternaryProductSecond a V f δ y) _ (by positivity)
    (fun z _ => ternary_product_hasDerivAt a V f δ y z)
    (fun z _ => ternary_product_first_hasDerivAt a V f δ y z) _ (responseNode_mem_unit q)
  intro z hz
  refine (ternary_product_second_abs_bound a V f δ y z (2*η) A S (by positivity)
    (by positivity) Hb hδ ?_ (fun i => ternary_mean_derivative_abs_bound a _ ρ ha hρ (hf z hz i) (y i))
    (fun i => ternary_mean_second_derivative_abs_bound a ha (y i))).trans ?_
  · intro i
    rw [ternaryLineMass, abs_of_nonneg (hp z hz i (y i))]
    exact ternary_mass_le_one a _ V ha.ne' (hp z hz i) (y i)
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnn : 0 ≤ (n : ℝ) ^ 2 - n := by nlinarith
    linarith [mul_nonneg hnn (mul_nonneg (sq_nonneg η) Hb)]

/-- A legal local regression chart for the finite response rule. The same
bounds control the incoming field and every convex reset of its coefficients. -/
structure ResponseGuards {n : ℕ} (C a V η ρ : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) : Prop where
  frame_pos : 0 < C
  scale_pos : 0 < a
  amplitude_nonneg : 0 ≤ η
  amplitude_half : η ≤ ρ / 2
  baseline : ∀ i, |g i| ≤ ρ / 2
  weight : ∀ i, |w i| ≤ 1
  profile : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1
  mass : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u

section Guards
variable {n : ℕ} {C a V η ρ : ℝ} {g w : Fin n → ℝ} {φ : Fin n → ι → ℝ}
  (H : ResponseGuards C a V η ρ g w φ)
include H

omit [DecidableEq ι] in
theorem ResponseGuards.radius_nonneg : 0 ≤ ρ := by
  linarith [H.amplitude_nonneg, H.amplitude_half]

omit [DecidableEq ι] in
private theorem ResponseGuards.weighted_amplitude (i : Fin n) : |η * w i| ≤ η := by
  rw [abs_mul, abs_of_nonneg H.amplitude_nonneg]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (H.weight i) H.amplitude_nonneg

omit [DecidableEq ι] in
theorem ResponseGuards.regression_bound {c : ι → ℝ} (hc : ∑ k, |c k| ≤ C⁻¹) (i : Fin n) :
    |coefficientRegression η g w φ c i| ≤ ρ := by
  have ht : |η * w i * (∑ k, φ i k * c k)| ≤ η := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul (H.weighted_amplitude i) (H.profile c hc i)
      (abs_nonneg _) H.amplitude_nonneg
  exact (abs_add_le _ _).trans (by linarith [H.baseline i, H.amplitude_half])

omit [DecidableEq ι] in
theorem ResponseGuards.mass_nonneg {c : ι → ℝ} (hc : ∑ k, |c k| ≤ C⁻¹) (i : Fin n) (u : Fin 3) :
    0 ≤ ternaryMass a (coefficientRegression η g w φ c i) V u :=
  H.mass _ (H.regression_bound hc i) u

omit [DecidableEq ι] in
theorem ResponseGuards.product_abs_le {c : ι → ℝ} (hc : ∑ k, |c k| ≤ C⁻¹) (y : Fin n → Fin 3) :
    |highResponseProduct a V η g w φ c y| ≤ 1 := by
  rw [highResponseProduct, Finset.abs_prod]
  apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
  intro i _
  rw [abs_of_nonneg (H.mass_nonneg hc i (y i))]
  exact ternary_mass_le_one a _ V H.scale_pos.ne' (H.mass_nonneg hc i) (y i)

omit [DecidableEq ι] in
theorem ResponseGuards.reset_bound {c v : ι → ℝ} {z : ℝ}
    (hc : ∑ k, |c k| ≤ C⁻¹) (hv : ∑ k, |v k| ≤ C⁻¹) (hz : z ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    |coefficientRegression η g w φ c i + z * coefficientDirection η w φ c v i| ≤ ρ := by
  rw [← congrFun (coefficientRegression_reset η g w φ c v z) i]
  exact H.regression_bound (coefficientReset_mem_ball C c v z hz hc hv) i

omit [DecidableEq ι] in
theorem ResponseGuards.direction_bound {c v : ι → ℝ}
    (hc : ∑ k, |c k| ≤ C⁻¹) (hv : ∑ k, |v k| ≤ C⁻¹) (i : Fin n) :
    |coefficientDirection η w φ c v i| ≤ 2 * η := by
  have hprof : |∑ k, φ i k * (v k - c k)| ≤ 2 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact (abs_sub _ _).trans (by linarith [H.profile v hv i, H.profile c hc i])
  unfold coefficientDirection
  rw [abs_mul]
  exact (mul_le_mul (H.weighted_amplitude i) hprof (abs_nonneg _) H.amplitude_nonneg).trans_eq (mul_comm _ _)

end Guards

def highLocalDerivativeConstant (q : ℕ) (a ρ : ℝ) : ℝ :=
  (∑ j : Fin (2 * q + 2), |responseWeight q j|) *
    (4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2))

/-- Matrix-response bound at every count, derived from legal frame resets
and the actual ternary product derivatives. -/
theorem high_response_matrix_all_count_bound {n : ℕ} (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (A : ι → ι → ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3)
    (H : ResponseGuards C a V η ρ g w φ) (hc : ∑ k, |c k| ≤ C⁻¹) :
    |responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y)| ≤
      (2 * C ^ 2 * ∑ k, ∑ l, |A k l|) *
        (highLocalDerivativeConstant q a ρ * (n : ℝ)^2 * η^2) := by
  unfold responseMatrixAction
  apply covarianceAction_abs_le
  intro k l s t
  have hv := covarianceAtom_mem_ball C H.frame_pos k l s t
  have hf (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) := H.reset_bound hc hv hz
  simp only [highResponseProduct, coefficientRegression_reset]
  exact (response_scalar_product_action_abs_bound q n hn a V η ρ _ _ y H.scale_pos
    H.amplitude_nonneg H.radius_nonneg hf (fun z hz i u => H.mass _ (hf z hz i) u)
    (H.direction_bound hc hv)).trans_eq (by unfold highLocalDerivativeConstant; ring)

end Covariance

end NearlyMinimax
