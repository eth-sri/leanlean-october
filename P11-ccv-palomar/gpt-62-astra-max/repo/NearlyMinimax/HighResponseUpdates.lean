module

public import NearlyMinimax.AtomicVariation
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

section
variable (a f V δ z : ℝ) (y : Fin 3)

/-- A ternary response on an affine regression line, as an actual polynomial. -/
def ternaryLinePolynomial : ℝ[X] :=
  C (ternaryMass a f V y) + monomial 1 (δ * ternaryMeanDerivative a f y) +
    monomial 2 (δ ^ 2 * ternaryVarianceDerivative a y)

theorem ternary_line_polynomial_eval :
    (ternaryLinePolynomial a f V δ y).eval z = ternaryMass a (f + z * δ) V y := by
  fin_cases y <;> simp [ternaryLinePolynomial, ternaryMass, ternaryMeanDerivative,
    ternaryVarianceDerivative, div_eq_mul_inv] <;> ring

theorem ternary_line_polynomial_natDegree :
    (ternaryLinePolynomial a f V δ y).natDegree ≤ 2 := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    exact max_le (by simp) ((natDegree_monomial_le _).trans (by norm_num))
  · exact natDegree_monomial_le _

end

section
variable {q n : ℕ} (a V : ℝ) (f δ : Fin n → ℝ) (y : TernaryVector n)

/-- Complete finite product likelihood on the same line. -/
def responseLinePolynomial : ℝ[X] := ∏ i, ternaryLinePolynomial a (f i) V (δ i) (y i)

theorem response_line_polynomial_eval (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : TernaryVector n) (z : ℝ) :
    (responseLinePolynomial a V f δ y).eval z =
      ∏ i, ternaryMass a (f i + z * δ i) V (y i) := by
  simp only [responseLinePolynomial, eval_prod]
  simp [ternary_line_polynomial_eval]

theorem response_line_polynomial_natDegree : (responseLinePolynomial a V f δ y).natDegree ≤ 2 * n := by
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ _ := Finset.sum_le_sum (fun i _ => ternary_line_polynomial_natDegree ..)
    _ = _ := by simp [mul_comm]

/-- Exact cardinal quadratic extraction of the genuine likelihood through
count q, including arbitrary offsets and incoming regression fields. -/
theorem response_line_rule_exact (hn : n ≤ q) :
    (∑ j : Fin (2 * q + 2), responseWeight j *
      ∏ i, ternaryMass a (f i + responseNode j * δ i) V (y i)) =
      (responseLinePolynomial a V f δ y).coeff 2 := by
  simpa only [response_line_polynomial_eval] using response_rule_exact
    (P := (responseLinePolynomial a V f δ y))
    (degree_le_natDegree.trans_lt (by
      exact_mod_cast (show (responseLinePolynomial a V f δ y).natDegree < 2 * q + 2 from
        (response_line_polynomial_natDegree a V f δ y).trans_lt (by omega))))

private theorem ternary_line_derivatives (a f V δ : ℝ) (y : Fin 3) (z : ℝ) :
    HasDerivAt (fun t => ternaryMass a (f + t*δ) V y) (δ*ternaryMeanDerivative a (f+z*δ) y) z ∧
    HasDerivAt (fun t => δ*ternaryMeanDerivative a (f+t*δ) y) (δ^2*ternaryMeanSecondDerivative a y) z := by
  have hz := ((hasDerivAt_id z).mul_const δ).const_add f
  exact ⟨((ternary_hasDerivAt_mean a _ V y).comp z hz).congr_deriv (by simp; ring),
    ((((ternary_hasDerivAt_mean_derivative a _ y).comp z hz).const_mul δ)).congr_deriv (by simp; ring)⟩

/-- Formal quadratic coefficient equals half the genuine second directional
product derivative, so its heat contraction can be evaluated explicitly. -/
theorem response_line_quadratic_coefficient :
    2 * (responseLinePolynomial a V f δ y).coeff 2 =
      finiteProductSecond Finset.univ
        (fun i z => ternaryMass a (f i + z * δ i) V (y i))
        (fun i z => δ i * ternaryMeanDerivative a (f i + z * δ i) (y i))
        (fun i _ => (δ i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0 := by
  let Q := responseLinePolynomial a V f δ y
  let H  := fun i z => ternaryMass a (f i + z * δ i) V (y i)
  let D  := fun i z => δ i * ternaryMeanDerivative a (f i + z * δ i) (y i)
  let E : Fin n → ℝ → ℝ := fun i _ => (δ i) ^ 2 * ternaryMeanSecondDerivative a (y i)
  have hdif (i : Fin n) (z : ℝ) := ternary_line_derivatives a (f i) V (δ i) (y i) z
  have hQ (z : ℝ) : HasDerivAt (fun z => Q.eval z) (finiteProductFirst Finset.univ H D z) z := by
    simpa only [Q, response_line_polynomial_eval] using
      finite_product_hasDerivAt Finset.univ H D z (fun i _ => (hdif i z).1)
  have hd : (fun z => Q.derivative.eval z) = finiteProductFirst Finset.univ H D := by
    funext z
    exact (Q.hasDerivAt z).unique (hQ z)
  have hsecond := finite_product_first_hasDerivAt Finset.univ H D E 0
    (fun i _ => (hdif i 0).1) (fun i _ => (hdif i 0).2)
  rw [← hd] at hsecond
  have he := (Q.derivative.hasDerivAt 0).unique hsecond
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_derivative] at he
  grind

/-- A uniform second-derivative estimate yields an affine Taylor remainder
bound at every scalar response mark; no score bound is assumed. -/
theorem affine_line_remainder_abs_bound {H D E : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ z ∈ Icc 0 1, HasDerivAt H (D z) z)
    (hD : ∀ z ∈ Icc 0 1, HasDerivAt D (E z) z)
    (hE : ∀ z ∈ Icc 0 1, |E z| ≤ B)
    {z : ℝ} (hz : z ∈ Icc 0 1) : |H z - H 0 - z * D 0| ≤ B := by
  have hzero : 0 ∈ Icc (0 : ℝ) 1 := by norm_num
  have hDdiff (u : ℝ) (hu : u ∈ Icc 0 1) : |D u - D 0| ≤ B := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hD x hx).hasDerivWithinAt)
      (fun x hx => by bound)
      (convex_Icc 0 1) hzero hu
    simp at h
    have huabs  := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    exact h.trans (by bound)
  let G := fun u => H u - H 0 - u * D 0
  have hG (u : ℝ) (hu : u ∈ Icc 0 1) : HasDerivAt G (D u - D 0) u :=
    (((hH u hu).sub_const (H 0)).sub ((hasDerivAt_id u).mul_const (D 0))).congr_deriv (by ring)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hG x hx).hasDerivWithinAt)
    (fun x hx => by bound)
    (convex_Icc 0 1) hzero hz
  have hzabs  := abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
  simp [G, sub_zero, zero_mul, sub_self, Real.norm_eq_abs] at h
  exact h.trans (by bound)

/-- The real scalar cardinal action has the all-count quadratic derivative
bound; its affine part cancels exactly by the proved moments. -/
theorem response_scalar_action_abs_bound (H D E : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ z ∈ Icc 0 1, HasDerivAt H (D z) z)
    (hD : ∀ z ∈ Icc 0 1, HasDerivAt D (E z) z)
    (hE : ∀ z ∈ Icc 0 1, |E z| ≤ B)
    (hnodes : ∀ j : Fin (2 * q + 2), responseNode j ∈ Icc 0 1) :
    |∑ j : Fin (2 * q + 2), responseWeight j * H (responseNode j)| ≤
      responseVariation q * B := by
  have he : (∑ j : Fin (2 * q + 2), responseWeight j * H (responseNode j)) =
      ∑ j : Fin (2 * q + 2), responseWeight j *
        (H (responseNode j) - H 0 - responseNode j * D 0) := by
    simp [mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
    rw [← Finset.sum_mul, ← Finset.sum_mul, response_zero_mass, response_zero_mean]
    simp
  rw [he]
  exact responseVariation_bound (fun j => affine_line_remainder_abs_bound hB hH hD hE (hnodes j))

end

section Covariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section
variable (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ)

/-- Incoming coefficients are reset by the actual scalar mark and covariance atom. -/
def coefficientReset (v : ι → ℝ) (z : ℝ) : ι → ℝ :=
  fun i => (1 - z) * c i + z * v i

/-- The paper's B_A as a genuine finite signed action. -/
def responseMatrixAction (Φ : (ι → ℝ) → ℝ) : ℝ :=
  covarianceAction C A (fun v => ∑ j : Fin (2 * q + 2),
    responseWeight j * Φ (coefficientReset c v (responseNode j)))

theorem responseMatrixAction_zero_mass :
    responseMatrixAction q C A c (fun _ => 1) = 0 := by
  simp [responseMatrixAction, response_zero_mass, covarianceAction]

theorem covariance_displacement_second {C : ℝ} {A : ι → ι → ℝ}
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) (c : ι → ℝ) (k l : ι) :
    covarianceAction C A (fun v => (v k - c k) * (v l - c l)) = A k l := by
  have hf : (fun v : ι → ℝ => (v k - c k) * (v l - c l)) =
      (fun v => v k * v l + (-c l) * v k + (-c k) * v l + c k * c l * 1) := by
    funext v
    ring
  rw [hf, covarianceAction_add, covarianceAction_add, covarianceAction_add,
    covarianceAction_mul, covarianceAction_mul, covarianceAction_mul,
    covariance_second_moment_symmetric hC hA, covariance_zero_mean,
    covariance_zero_mean, covariance_zero_mass]
  ring

theorem responseNode_mem_unit (j : Fin (2 * q + 2)) :
    responseNode j ∈ Icc 0 1 := by
  have hden : (0 : ℝ) < (2 * q + 1 : ℕ) := by positivity
  constructor
  · exact div_nonneg (by positivity) hden.le
  · apply (div_le_one hden).mpr
    exact_mod_cast (show j.val ≤ 2 * q + 1 by omega)

end

omit [DecidableEq ι] in
theorem coefficientReset_mem_ball (C : ℝ) (c v : ι → ℝ) (z : ℝ)
    (hz : z ∈ Icc 0 1)
    (hc : ∑ i, |c i| ≤ C⁻¹) (hv : ∑ i, |v i| ≤ C⁻¹) :
    (∑ i, |coefficientReset c v z i|) ≤ C⁻¹ := by
  calc
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply (abs_add_le _ _).trans_eq
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hz.2]), abs_of_nonneg hz.1]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hc (by linarith [hz.2])) (mul_le_mul_of_nonneg_left hv hz.1)
    _ = _ := by ring

section
variable (A : ι → ι → ℝ) {n : ℕ} (η : ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c v : ι → ℝ)

/-- The finite spatial polynomial frame is evaluated without any abstract
smoothness or response assumptions. -/
def spatialFrameCovariance
    (i l : Fin n) : ℝ := ∑ k, ∑ m, φ i k * φ l m * A k m

def coefficientRegression : Fin n → ℝ :=
  fun i => g i + η * w i * ∑ k, φ i k * c k

def coefficientDirection : Fin n → ℝ :=
  fun i => η * w i * ∑ k, φ i k * (v k - c k)

end

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

section
variable {n q : ℕ} (hn : n ≤ q) (C a V η : ℝ) {A : ι → ι → ℝ} (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : TernaryVector n)

include hC hA in
theorem covariance_direction_product (i l : Fin n) :
    covarianceAction C A (fun v => coefficientDirection η w φ c v i *
      coefficientDirection η w φ c v l) = η ^ 2 * w i * w l * spatialFrameCovariance A φ i l := by
  have he : (fun v => coefficientDirection η w φ c v i * coefficientDirection η w φ c v l) =
      (fun v => η ^ 2 * w i * w l *
        ∑ k, ∑ m, (φ i k * φ l m) * ((v k - c k) * (v m - c m))) := by
    funext v
    simp only [coefficientDirection, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, covarianceAction_mul, covarianceAction_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [covarianceAction_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [covarianceAction_mul, covariance_displacement_second hC hA]

/-- Real response likelihood of a single local coefficient state. -/
def highResponseProduct : ℝ :=
  ∏ i, ternaryMass a (coefficientRegression η g w φ c i) V (y i)

omit [DecidableEq ι] in
/-- Displacement on a bounded chart is at most η, so adding it to the
baseline keeps the entire regression in the legal response interval. -/
theorem coefficientRegression_abs_le {n : ℕ} {η ρ : ℝ} {g w : Fin n → ℝ}
    {φ : Fin n → ι → ℝ} {v : ι → ℝ} {i : Fin n} (hη : 0 ≤ η) (hηρ : η ≤ ρ/2)
    (hg : |g i| ≤ ρ/2) (hw : |w i| ≤ 1) (hφ : |∑ k, φ i k * v k| ≤ 1) :
    |coefficientRegression η g w φ v i| ≤ ρ := by
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hη]
  calc
    _ ≤ ρ/2 + η * 1 * 1 := by gcongr
    _ ≤ _ := by linarith

omit [DecidableEq ι] in
theorem coefficient_direction_abs_le {n : ℕ} (C η : ℝ) (hη : 0 ≤ η)
    (w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c v : ι → ℝ)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hv : ∑ k, |v k| ≤ C⁻¹)
    (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (i : Fin n) : |coefficientDirection η w φ c v i| ≤ 2 * η := by
  have hprof : |∑ k, φ i k * (v k - c k)| ≤ 2 := by
    simp [mul_sub, Finset.sum_sub_distrib]
    exact (abs_sub _ _).trans (by linarith [hφ v hv i, hφ c hc i])
  have hm : |η * w i| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]
    bound
  change |η * w i * (∑ k, φ i k * (v k - c k))| ≤ _
  rw [abs_mul]
  exact (mul_le_mul hm hprof (abs_nonneg _) hη).trans_eq (by ring)

omit [DecidableEq ι] in
theorem coefficient_regression_reset_abs_le {n : ℕ} (C η ρ : ℝ)
    (hη : 0 ≤ η) (hηρ : η ≤ ρ / 2) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c v : ι → ℝ) (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hv : ∑ k, |v k| ≤ C⁻¹)
    (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (i : Fin n) :
    |coefficientRegression η g w φ c i + z * coefficientDirection η w φ c v i| ≤ ρ := by
  rw [← congrFun (coefficientRegression_reset η g w φ c v z) i]
  exact coefficientRegression_abs_le hη hηρ (hg i) (hw i) (hφ _ (coefficientReset_mem_ball C c v z hz hc hv) i)

include hn in
/-- The exact finite signed response operator is its directional Hessian
contraction through count q. This comes from actual cardinal evaluation. -/
theorem high_response_matrix_second (A : ι → ι → ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : TernaryVector n) :
    let direction := coefficientDirection η w φ c
    responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) =
      (1 / 2) * covarianceAction C A (fun v =>
        finiteProductSecond Finset.univ
          (fun i z => ternaryMass a (coefficientRegression η g w φ c i +
            z * direction v i) V (y i))
          (fun i z => direction v i * ternaryMeanDerivative a
            (coefficientRegression η g w φ c i + z * direction v i) (y i))
          (fun i _ => (direction v i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0) := by
  intro direction
  rw [← covarianceAction_mul]
  apply congrArg (covarianceAction C A)
  funext v
  simp only [highResponseProduct, coefficientRegression_reset]
  rw [response_line_rule_exact a V _ _ y hn]
  have h := response_line_quadratic_coefficient a V
    (coefficientRegression η g w φ c) (direction v) y
  linarith

/-- The variance derivative before substituting a common variance. -/
def highResponseVarianceTerm (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) * ∏ l ∈ Finset.univ.erase i,
    ternaryMass a (coefficientRegression η g w φ c l) V (y l)

include hn hC hA in
/-- Spatial cardinal covariance cancels every off-diagonal product derivative.
This is the actual heat identity of the realized finite signed update. -/
theorem high_response_matrix_heat
    (d : Fin n → ℝ)
    (hdiag : ∀ i l, spatialFrameCovariance A φ i l = if i = l then d i else 0) :
    responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) =
      η ^ 2 * ∑ i, (w i) ^ 2 * d i * highResponseVarianceTerm a V η g w φ c y i := by
  let f := coefficientRegression η g w φ c
  let δ := coefficientDirection η w φ c
  let p := fun i => ternaryMass a (f i) V (y i)
  let m := fun i => ternaryMeanDerivative a (f i) (y i)
  let e := fun i => ternaryMeanSecondDerivative a (y i)
  let S  := fun v => ∑ i,
    ((∑ l ∈ Finset.univ.erase i,
      (∏ k ∈ (Finset.univ.erase i).erase l, p k) *
        m l * m i * (δ v l * δ v i)) +
      (∏ l ∈ Finset.univ.erase i, p l) * e i * (δ v i * δ v i))
  have hS (v : ι → ℝ) :
      finiteProductSecond Finset.univ
        (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
        (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
        (fun i _ => (δ v i) ^ 2 * e i) 0 = S v := by
    simp only [finiteProductSecond, zero_mul, add_zero, S]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    · ring
  rw [high_response_matrix_second hn C a V η A g w φ c y]
  change (1 / 2) * covarianceAction C A
    (fun v => finiteProductSecond Finset.univ
      (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
      (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
      (fun i _ => (δ v i) ^ 2 * e i) 0) = _
  simp_rw [hS]
  rw [covarianceAction_sum]
  have he (i : Fin n) : covarianceAction C A
      (fun v => (∑ l ∈ Finset.univ.erase i,
        (∏ k ∈ (Finset.univ.erase i).erase l, p k) *
          m l * m i * (δ v l * δ v i)) +
        (∏ l ∈ Finset.univ.erase i, p l) * e i * (δ v i * δ v i)) =
      2 * η ^ 2 * (w i) ^ 2 * d i * highResponseVarianceTerm a V η g w φ c y i := by
    rw [covarianceAction_add, covarianceAction_sum]
    have hcross (l : Fin n) (hl : l ∈ Finset.univ.erase i) :
        covarianceAction C A (fun v =>
          (∏ k ∈ (Finset.univ.erase i).erase l, p k) * m l * m i *
            (δ v l * δ v i)) = 0 := by
      rw [covarianceAction_mul, covariance_direction_product C η hC hA w φ c l i,
        hdiag l i, ite_eq_right (Finset.ne_of_mem_erase hl), mul_zero, mul_zero]
    rw [Finset.sum_eq_zero (fun l hl => hcross l hl), zero_add, covarianceAction_mul,
      covariance_direction_product C η hC hA w φ c i i, hdiag i i, ite_eq_left rfl]
    dsimp [e, highResponseVarianceTerm]
    rw [ternary_heat_identity]
    ring
  simp_rw [he]
  rw [Finset.mul_sum, Finset.mul_sum]
  ring

end

/-- All-count cardinal action bound propagated through the genuine product
likelihood. The assumptions are individual legality and displacement bounds. -/
theorem response_scalar_product_action_abs_bound (q n : ℕ) (hn : 1 ≤ n)
    (a V η ρ : ℝ) {f δ : Fin n → ℝ} (y : TernaryVector n)
    (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hf : ∀ z ∈ Icc 0 1, ∀ i, |f i + z * δ i| ≤ ρ)
    (hp : ∀ z ∈ Icc 0 1, ∀ i u, 0 ≤ ternaryMass a (f i + z * δ i) V u)
    (hδ : ∀ i, |δ i| ≤ 2 * η) :
    |∑ j : Fin (2 * q + 2), responseWeight j *
      ∏ i, ternaryMass a (f i + responseNode j * δ i) V (y i)| ≤
      responseVariation q *
        (4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2) * n ^ 2 * η ^ 2) := by
  let H  := fun i z => ternaryMass a (f i + z * δ i) V (y i)
  let D  := fun i z => δ i * ternaryMeanDerivative a (f i + z * δ i) (y i)
  let E : Fin n → ℝ → ℝ := fun i _ => (δ i) ^ 2 * ternaryMeanSecondDerivative a (y i)
  let A := (2 * ρ + a) / a ^ 2
  let S := 2 / a ^ 2
  have hS : 0 ≤ S := by positivity
  have hdif (i : Fin n) (z : ℝ) := ternary_line_derivatives a (f i) V (δ i) (y i) z
  have hHbound (z : ℝ) (hz : z ∈ Icc 0 1) (i : Fin n) : |H i z| ≤ 1 := by
    rw [abs_of_nonneg (hp z hz i (y i))]
    exact ternary_mass_le_one _ V ha.ne' (hp z hz i) (y i)
  have hDbound (z : ℝ) (hz : z ∈ Icc 0 1) (i : Fin n) : |D i z| ≤ 2 * η * A := by
    rw [abs_mul]
    exact mul_le_mul (hδ i) (ternary_mean_derivative_abs_bound ha hρ (hf z hz i) (y i))
      (abs_nonneg _) (by positivity)
  have hEbound (z : ℝ) (i : Fin n) : |E i z| ≤ 4 * η ^ 2 * S := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hs : (δ i) ^ 2 ≤ (2 * η) ^ 2 := by
      simpa using pow_le_pow_left₀ (abs_nonneg _) (hδ i) 2
    have h := mul_le_mul hs (ternary_mean_second_derivative_abs_bound ha (y i))
      (abs_nonneg _) (by positivity)
    linarith
  apply response_scalar_action_abs_bound _ (finiteProductFirst Finset.univ H D)
    (finiteProductSecond Finset.univ H D E) _ (by positivity)
    (fun z hz => finite_product_hasDerivAt Finset.univ H D z (fun i _ => (hdif i z).1))
    (fun z hz => finite_product_first_hasDerivAt Finset.univ H D E z
      (fun i _ => (hdif i z).1) (fun i _ => (hdif i z).2)) _ (responseNode_mem_unit q)
  intro z hz
  have h := finite_product_second_abs_bound Finset.univ H D E z (2 * η * A) (4 * η ^ 2 * S)
    (by positivity) (by positivity) (fun i _ => hHbound z hz i)
    (fun i _ => hDbound z hz i) (fun i _ => hEbound z i)
  simp at h
  apply h.trans
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn : 0 ≤ (n : ℝ) ^ 2 - n := by nlinarith
  have hmore := mul_nonneg hnn (mul_nonneg (sq_nonneg η) hS)
  linarith

/-- Matrix-response bound at every count, derived from legal frame resets
and the actual ternary product derivatives. -/
theorem high_response_matrix_all_count_bound {n : ℕ} (q : ℕ) (hn : 1 ≤ n)
    {C a V η ρ : ℝ} (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ / 2) (A : ι → ι → ℝ) {g w : Fin n → ℝ}
    {φ : Fin n → ι → ℝ} {c : ι → ℝ} (y : TernaryVector n)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2)
    (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    |responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y)| ≤
      (2 * C ^ 2 * ∑ k, ∑ l, |A k l|) *
        (responseVariation q *
          (4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2) * n ^ 2 * η ^ 2)) := by
  apply covarianceAction_abs_le
  intro k l s t
  let v := covarianceAtom C k l s t
  have hv  := covarianceAtom_mem_ball hC k l s t
  let f := coefficientRegression η g w φ c
  let δ := coefficientDirection η w φ c v
  have hr (z : ℝ) : coefficientRegression η g w φ (coefficientReset c v z) =
      fun i => f i + z * δ i := coefficientRegression_reset η g w φ c v z
  have hδ := coefficient_direction_abs_le C η hη w φ c v hc hv hw hφ
  have hf (z) (hz : z ∈ Icc 0 1) := coefficient_regression_reset_abs_le C η ρ hη hηρ g w φ c v z hz hc hv hg hw hφ
  have he : (∑ j : Fin (2 * q + 2), responseWeight j *
      highResponseProduct a V η g w φ (coefficientReset c v (responseNode j)) y) =
      ∑ j : Fin (2 * q + 2), responseWeight j *
        ∏ i, ternaryMass a (f i + responseNode j * δ i) V (y i) := by
    simp [highResponseProduct, hr]
  rw [he]
  exact response_scalar_product_action_abs_bound q n hn a V η ρ y ha hη hρ hf
    (fun z hz i u => hp _ (hf z hz i) u) hδ

end Covariance

end NearlyMinimax
