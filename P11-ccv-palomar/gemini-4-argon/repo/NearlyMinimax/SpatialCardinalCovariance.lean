module
public import NearlyMinimax.HighResponseUpdates
public import NearlyMinimax.CellPolynomialProjection
@[expose] public section
noncomputable section
set_option maxHeartbeats 1500000
section
open MeasureTheory Set Polynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
theorem polynomial_product_iterate_derivative_abs_bound  [DecidableEq ι]
    (s : Finset ι) (P : ι → ℝ[X]) (b z : ℝ) (hb : 0 ≤ b)
    (hP : ∀ i ∈ s, ∀ r : ℕ, |(derivative^[r] (P i)).eval z| ≤ b ^ r) :
    ∀ r : ℕ, |(derivative^[r] (∏ i ∈ s, P i)).eval z| ≤ (↑s.card * b) ^ r := by
  induction s using Finset.induction_on with
  | empty =>
    intro r
    by_cases hr : r = 0
    · simp [hr]
    · rw [Finset.prod_empty, iterate_derivative_one (Nat.pos_of_ne_zero hr)]
      simp only [eval_zero, abs_zero, Finset.card_empty, Nat.cast_zero, zero_mul]
      positivity
  | @insert i s hi ih =>
    intro r
    rw [Finset.prod_insert hi, iterate_derivative_mul, eval_finsetSum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ k ∈ Finset.range (r + 1), (r.choose k ) *
          (b ^ (r - k) * (s.card * b) ^ k) := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [nsmul_eq_mul, eval_mul, eval_natCast, abs_mul, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ r.choose k)]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact mul_le_mul (hP i (Finset.mem_insert_self _ _) (r - k))
          (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)) k)
          (abs_nonneg _) (pow_nonneg hb _)
      _ = ((s.card * b) + b) ^ r := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = (((insert i s : Finset ι).card : ℝ) * b) ^ r := by
        rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
        congr 1
        ring
def polynomialResponseTaylor (q : ℕ) (P : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (2 * q + 2), monomial k (P.coeff k)
theorem polynomial_response_extraction_remainder (q ) (hq : 1 ≤ q)
    (P : ℝ[X]) (B ) (hB : 0 ≤ B)
    (hderiv : ∀ z ∈ Icc (0 : ℝ) 1,
      |(derivative^[2 * q + 2] P).eval z| ≤ B) :
    |(∑ j : Fin (2 * q + 2), responseWeight q j * P.eval (responseNode q j)) -
      P.coeff 2| ≤ (∑ j : Fin (2 * q + 2), |responseWeight q j|) * B := by
  have h_polynomial_iteratedDerivWithin_eval (r) (z) (hz : z ∈ Icc (0 : ℝ) 1) : iteratedDerivWithin r (fun z => P.eval z) (Icc 0 1) z =
      (derivative^[r] P).eval z := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))]
    have h_polynomial_iteratedDeriv_eval : iteratedDeriv r (fun z => P.eval z) = fun z => (derivative^[r] P).eval z := by
      induction r with
      | zero => simp
      | succ r ih =>
        rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
        funext z
        exact ((derivative^[r] P).hasDerivAt z).deriv
    · exact congrFun h_polynomial_iteratedDeriv_eval z
    · simpa only [coe_aeval_eq_eval] using
        (P.contDiff_aeval (𝕜 := ℝ) r).contDiffAt
    · exact hz
  have h_polynomial_response_taylor_exact : (∑ j : Fin (2 * q + 2), responseWeight q j *
      (polynomialResponseTaylor q P).eval (responseNode q j)) = P.coeff 2 := by
    have hdeg : (polynomialResponseTaylor q P).natDegree ≤ 2 * q + 1 := by
      apply natDegree_sum_le_of_forall_le
      intro k hk
      exact (natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hk; omega)
    have hdegree : (polynomialResponseTaylor q P).degree < 2 * q + 2 :=
      degree_le_natDegree.trans_lt (by exact_mod_cast
        (show (polynomialResponseTaylor q P).natDegree < 2 * q + 2 from hdeg.trans_lt (by omega)))
    rw [response_rule_exact q _ hdegree]
    simp only [polynomialResponseTaylor, finsetSum_coeff, coeff_monomial]
    simp [Finset.mem_range, show 2 < 2 * q + 2 by omega]
  rw [← h_polynomial_response_taylor_exact, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j : Fin (2 * q + 2), |responseWeight q j| * B := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_sub, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have h_polynomial_response_taylor_eval z : (polynomialResponseTaylor q P).eval z =
      taylorWithinEval (fun z => P.eval z) (2 * q + 1) (Icc 0 1) 0 z := by
        rw [taylor_within_apply]
        simp only [polynomialResponseTaylor, eval_finsetSum, eval_monomial]
        apply Finset.sum_congr rfl
        intro k hk
        rw [h_polynomial_iteratedDerivWithin_eval k 0 (by norm_num), ← coeff_zero_eq_eval_zero,
          coeff_iterate_derivative]
        simp only [Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul, sub_zero, smul_eq_mul]
        field_simp
      rw [h_polynomial_response_taylor_eval]
      have hsmooth : ContDiff ℝ (2 * q + 1 + 1) (fun z => P.eval z) := by
        simpa only [coe_aeval_eq_eval] using P.contDiff_aeval (𝕜 := ℝ) (2 * q + 1 + 1)
      have h := taylor_mean_remainder_bound (f := fun z => P.eval z) (n := 2 * q + 1)
        (by norm_num : (0 : ℝ) ≤ 1) hsmooth.contDiffOn (responseNode_mem_unit q j)
        (fun z hz => by
          rw [h_polynomial_iteratedDerivWithin_eval (2 * q + 1 + 1) z hz]
          simpa only [Real.norm_eq_abs, show 2 * q + 1 + 1 = 2 * q + 2 by omega] using hderiv z hz)
      rw [Real.norm_eq_abs, sub_zero] at h
      apply h.trans
      have hz := responseNode_mem_unit q j
      apply (div_le_self (mul_nonneg hB (pow_nonneg hz.1 _)) (by exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (2 * q + 1))))).trans
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hz.1 hz.2) hB).trans_eq (mul_one B)
    _ = _ := by rw [Finset.sum_mul]
theorem ternary_line_derivative_eval (a f V δ z y) :
    (ternaryLinePolynomial a f V δ y).derivative.eval z =
      δ * ternaryMeanDerivative a (f + z * δ) y := by
  have h := (ternary_hasDerivAt_mean a (f + z * δ) V y).comp z
    (((hasDerivAt_id z).mul_const δ).const_add f)
  have he := (ternaryLinePolynomial a f V δ y).hasDerivAt z
  simp only [ternary_line_polynomial_eval] at he
  exact he.unique (h.congr_deriv (by ring))
theorem ternary_line_iterate_derivative_abs_bound (a f V δ η ρ B z y) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hB : 1 ≤ B) (hMean : (2 * ρ + a) / a ^ 2 ≤ B)
    (hSecond : 2 / a ^ 2 ≤ B) (hf : |f + z * δ| ≤ ρ)
    (hp : ∀ u, 0 ≤ ternaryMass a (f + z * δ) V u) (hδ : |δ| ≤ 2 * η) :
    ∀ r, |(derivative^[r] (ternaryLinePolynomial a f V δ y)).eval z| ≤
      (2 * η * B) ^ r := by
  intro r
  rcases r with _ | _ | _ | r
  · rw [Function.iterate_zero_apply, ternary_line_polynomial_eval, pow_zero,
      abs_of_nonneg (hp y)]
    exact ternary_mass_le_one a _ V ha.ne' hp y
  · rw [Function.iterate_one, ternary_line_derivative_eval, pow_one, abs_mul]
    apply (mul_le_mul hδ ((ternary_mean_derivative_abs_bound a _ ρ ha hρ hf y).trans hMean)
      (abs_nonneg _) (by positivity)).trans_eq
    ring
  · change |(derivative^[2] (ternaryLinePolynomial a f V δ y)).eval z| ≤ (2 * η * B) ^ 2
    have h_ternary_line_second_derivative_eval : (ternaryLinePolynomial a f V δ y).derivative.derivative.eval z =
      δ ^ 2 * ternaryMeanSecondDerivative a y := by
      have h := ((ternary_hasDerivAt_mean_derivative a (f + z * δ) y).comp z
        (((hasDerivAt_id z).mul_const δ).const_add f)).const_mul δ
      have he := (ternaryLinePolynomial a f V δ y).derivative.hasDerivAt z
      simp only [ternary_line_derivative_eval] at he
      exact he.unique (h.congr_deriv (by ring))
    rw [show 2 = 1 + 1 by rfl, Function.iterate_succ_apply', Function.iterate_one,
      h_ternary_line_second_derivative_eval, abs_mul, abs_of_nonneg (sq_nonneg δ)]
    have hSB : 2 / a ^ 2 ≤ B ^ 2 := hSecond.trans (by nlinarith)
    exact (mul_le_mul (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hδ 2) ((ternary_mean_second_derivative_abs_bound a ha y).trans hSB)
      (abs_nonneg _) (by positivity : 0 ≤ (2 * η) ^ 2)).trans_eq (by ring)
  · rw [iterate_derivative_eq_zero ((ternary_line_polynomial_natDegree a f V δ y).trans_lt
      (by omega)), eval_zero, abs_zero]
    positivity
theorem response_scalar_high_order_remainder (q ) (hq : 1 ≤ q) (n a V η ρ B f δ y)
    (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hB : 1 ≤ B)
    (hMean : (2 * ρ + a) / a ^ 2 ≤ B) (hSecond : 2 / a ^ 2 ≤ B)
    (hf : ∀ z ∈ Icc (0 : ℝ) 1, ∀ i, |f i + z * δ i| ≤ ρ)
    (hp : ∀ z ∈ Icc (0 : ℝ) 1, ∀ i u, 0 ≤ ternaryMass a (f i + z * δ i) V u)
    (hδ : ∀ i, |δ i| ≤ 2 * η) :
    |(∑ j : Fin (2 * q + 2), responseWeight q j *
      ∏ i, ternaryMass a (f i + responseNode q j * δ i) V (y i)) -
      (responseLinePolynomial n a V f δ y).coeff 2| ≤
      (∑ j : Fin (2 * q + 2), |responseWeight q j|) *
        (n * (2 * η * B)) ^ (2 * q + 2) := by
  simp only [← response_line_polynomial_eval]
  apply polynomial_response_extraction_remainder q hq _ _ (by positivity)
  intro z hz
  simpa only [responseLinePolynomial, Finset.card_univ, Fintype.card_fin] using
    polynomial_product_iterate_derivative_abs_bound Finset.univ
      (fun i : Fin n => ternaryLinePolynomial a (f i) V (δ i) (y i))
      (2 * η * B) z (by positivity)
      (fun i _ => ternary_line_iterate_derivative_abs_bound a (f i) V (δ i) η ρ B z
        (y i) ha hη hρ hB hMean hSecond (hf z hz i) (hp z hz i) (hδ i)) (2 * q + 2)
section SpatialRemainder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def highResponseQuadraticAction  (C a V η : ℝ) (A : ι → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (y : Fin n → Fin 3) : ℝ :=
  covarianceAction C A (fun v =>
    (responseLinePolynomial n a V (coefficientRegression η g w φ c)
      (coefficientDirection η w φ c v) y).coeff 2)
theorem coefficient_direction_abs_le  (C η ) (hη : 0 ≤ η)
    (w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c v : ι → ℝ)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hv : ∑ k, |v k| ≤ C⁻¹)
    (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (i : Fin n) : |coefficientDirection η w φ c v i| ≤ 2 * η := by
  have hprof : |∑ k, φ i k * (v k - c k)| ≤ 2 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact (abs_sub _ _).trans (by linarith [hφ v hv i, hφ c hc i])
  have hm : |η * w i| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]
    exact (mul_le_mul_of_nonneg_left (hw i) hη).trans_eq (mul_one η)
  change |η * w i * (∑ k, φ i k * (v k - c k))| ≤ 2 * η
  rw [abs_mul]
  exact (mul_le_mul hm hprof (abs_nonneg _) hη).trans_eq (by ring)
theorem high_response_matrix_high_order_remainder  (q ) (hq : 1 ≤ q)
    (C a V η ρ B ) (hC : 0 < C) (ha : 0 < a)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2)
    (hB : 1 ≤ B) (hMean : (2 * ρ + a) / a ^ 2 ≤ B) (hSecond : 2 / a ^ 2 ≤ B)
    (A : ι → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (y : Fin n → Fin 3)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    |responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) -
      highResponseQuadraticAction C a V η A g w φ c y| ≤
      (2 * C ^ 2 * ∑ k, ∑ l, |A k l|) *
        ((∑ j : Fin (2 * q + 2), |responseWeight q j|) *
          (↑n * (2 * η * B)) ^ (2 * q + 2)) := by
  have h_coefficient_regression_reset_abs_le (v : ι → ℝ) (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (hc : ∑ k, |c k| ≤ C⁻¹) (hv : ∑ k, |v k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1) (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1) (i : Fin n) : |coefficientRegression η g w φ c i + z * coefficientDirection η w φ c v i| ≤ ρ := by
    rw [← (congrFun (coefficientRegression_reset η g w φ c v z) i)]
    have hpterm : |η * w i * (∑ k, φ i k * coefficientReset c v z k)| ≤ η := by
      rw [abs_mul]
      exact (mul_le_mul (by rw [abs_mul, abs_of_nonneg hη]; exact (mul_le_mul_of_nonneg_left (hw i) hη).trans_eq (mul_one η)) (hφ _ (coefficientReset_mem_ball C c v z hz hc hv) i) (abs_nonneg _) hη).trans_eq (mul_one η)
    exact (abs_add_le _ _).trans (by linarith [hg i, hpterm])
  unfold responseMatrixAction highResponseQuadraticAction
  rw [show covarianceAction C A
      (fun v => ∑ j : Fin (2 * q + 2), responseWeight q j *
        highResponseProduct a V η g w φ (coefficientReset c v (responseNode q j)) y) -
      covarianceAction C A
        (fun v => (responseLinePolynomial n a V (coefficientRegression η g w φ c)
          (coefficientDirection η w φ c v) y).coeff 2) =
      covarianceAction C A (fun v =>
        (∑ j : Fin (2 * q + 2), responseWeight q j *
          highResponseProduct a V η g w φ (coefficientReset c v (responseNode q j)) y) -
        (responseLinePolynomial n a V (coefficientRegression η g w φ c)
          (coefficientDirection η w φ c v) y).coeff 2) by
    simp only [covarianceAction, mul_sub, Finset.sum_sub_distrib]]
  apply covarianceAction_abs_le
  intro k l s t
  let v := covarianceAtom C k l s t
  have hv  := covarianceAtom_mem_ball C hC k l s t
  simp only [highResponseProduct, coefficientRegression_reset]
  apply response_scalar_high_order_remainder q hq n a V η ρ B _ _ y
    ha hη hρ hB hMean hSecond
  · exact fun z hz i => h_coefficient_regression_reset_abs_le v z hz
      hc hv hg hw hφ i
  · exact fun z hz i u => hp _
      (h_coefficient_regression_reset_abs_le v z hz hc hv hg hw hφ i) u
  · exact fun i => coefficient_direction_abs_le C η hη w φ c v hc hv hw hφ i
def highResponseDerivativeBudget (a ρ : ℝ) : ℝ :=
  max 1 (max ((2 * ρ + a) / a ^ 2) (2 / a ^ 2))
theorem highResponseDerivativeBudget_guards (a ρ ) :
    1 ≤ highResponseDerivativeBudget a ρ ∧
    (2 * ρ + a) / a ^ 2 ≤ highResponseDerivativeBudget a ρ ∧
    2 / a ^ 2 ≤ highResponseDerivativeBudget a ρ := by
  exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩
def highResponseDefect  (q : ℕ) (C a V η : ℝ) (A : ι → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (y : Fin n → Fin 3) : ℝ :=
  responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) -
    highResponseQuadraticAction C a V η A g w φ c y
theorem high_response_matrix_heat_with_defect  (q C a V η A) (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i)
    (g w φ) (c : ι → ℝ)
    (y : Fin n → Fin 3) (d : Fin n → ℝ)
    (hdiag : ∀ i l, spatialFrameCovariance A φ i l = if i = l then d i else 0) :
    responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) =
      η ^ 2 * ∑ i, (w i) ^ 2 * d i * highResponseVarianceTerm a V η g w φ c y i +
        highResponseDefect q C a V η A g w φ c y := by
  unfold highResponseDefect
  have h_high_response_quadratic_heat : highResponseQuadraticAction C a V η A g w φ c y =
      η ^ 2 * ∑ i, (w i) ^ 2 * d i * highResponseVarianceTerm a V η g w φ c y i := by
    have h_high_response_quadratic_eq_exact_rule : highResponseQuadraticAction C a V η A g w φ c y =
        responseMatrixAction n C A c (fun c => highResponseProduct a V η g w φ c y) := by
      unfold highResponseQuadraticAction responseMatrixAction
      apply congrArg (covarianceAction C A)
      funext v
      simp only [highResponseProduct, coefficientRegression_reset]
      exact (response_line_rule_exact n n a V _ _ y le_rfl).symm
    rw [h_high_response_quadratic_eq_exact_rule]
    exact high_response_matrix_heat n le_rfl C a V η A hC hA g w φ c y d hdiag
  rw [h_high_response_quadratic_heat]
  ring
def highResponseRemainderConstant (q : ℕ) (C a ρ : ℝ) : ℝ :=
  2 * C ^ 2 * (∑ j : Fin (2 * q + 2), |responseWeight q j|) *
    (2 * highResponseDerivativeBudget a ρ) ^ (2 * q + 2)
theorem high_response_defect_abs_bound  (q ) (hq : 1 ≤ q)
    (C a V η ρ ) (hC : 0 < C) (ha : 0 < a)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2)
    (A : ι → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (y : Fin n → Fin 3)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    |highResponseDefect q C a V η A g w φ c y| ≤
      highResponseRemainderConstant q C a ρ * (∑ k, ∑ l, |A k l|) *
        ↑n ^ (2 * q + 2) * η ^ (2 * q + 2) := by
  obtain ⟨hB, hMean, hSecond⟩ := highResponseDerivativeBudget_guards a ρ
  have h := high_response_matrix_high_order_remainder q hq C a V η ρ
    (highResponseDerivativeBudget a ρ) hC ha hη hρ hηρ hB hMean hSecond
    A g w φ c y hc hg hw hφ hp
  apply h.trans_eq
  unfold highResponseRemainderConstant
  rw [show ↑n * (2 * η * highResponseDerivativeBudget a ρ) =
    (2 * highResponseDerivativeBudget a ρ) * ↑n * η by ring, mul_pow, mul_pow]
  ring
end SpatialRemainder
end NearlyMinimax
end
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
variable {d n : ℕ}
abbrev HighFrameIndex (d D : ℕ) :=
  {γ : PolynomialBox d (D - 1) // (∑ r, (γ r).val) ≤ D - 1}
def highFrameFeature  (x : Covariate d) (γ : HighFrameIndex d D) : ℝ :=
  ∏ r, (x r / 8) ^ (γ.val r).val
def highFrameCoefficients  (P : MvPolynomial (Fin d) ℝ)
    (γ : HighFrameIndex d D) : ℝ := P.coeff (polynomialBoxExponent γ.val)
theorem high_frame_polynomial_evaluation  (P : MvPolynomial (Fin d) ℝ)
    (hP : P.totalDegree ≤ D - 1) (x : Covariate d) :
    eval (fun r => x r / 8) P =
      ∑ γ : HighFrameIndex d D, highFrameFeature x γ * highFrameCoefficients P γ := by
  rw [polynomial_box_evaluation P hP]
  have hzero (γ : PolynomialBox d (D - 1))
      (hγ : ¬ (∑ r, (γ r).val) ≤ D - 1) : P.coeff (polynomialBoxExponent γ) = 0 := by
    by_contra hne
    have ht := (le_totalDegree (mem_support_iff.mpr hne)).trans hP
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at ht
    simpa only [polynomial_box_exponent_apply] using hγ ht
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun γ : PolynomialBox d (D - 1) => (∑ r, (γ r).val) ≤ D - 1)
    (fun γ => P.coeff (polynomialBoxExponent γ) * ∏ r, (x r / 8) ^ (γ r).val)
  have hc : (∑ γ : {γ : PolynomialBox d (D - 1) // ¬ (∑ r, (γ r).val) ≤ D - 1},
      P.coeff (polynomialBoxExponent γ.val) * ∏ r, (x r / 8) ^ (γ.val r).val) = 0 := by
    apply Finset.sum_eq_zero
    intro γ _
    rw [hzero γ.val γ.property, zero_mul]
  rw [hc, add_zero] at hsplit
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro γ _
  exact mul_comm _ _
def spatialSquaredDistance  (x y : Covariate d) : ℝ := ∑ r, (y r - x r) ^ 2
def spatialCardinalAffine  (x y : Covariate d) : MvPolynomial (Fin d) ℝ :=
  ∑ r, (C ((y r - x r) * y r) - C (8 * (y r - x r)) * X r)
theorem spatial_cardinal_affine_eval  (x y u : Covariate d) :
    eval (fun r => u r / 8) (spatialCardinalAffine x y) =
      ∑ r, (y r - x r) * (y r - u r) := by
  simp only [spatialCardinalAffine, map_sum, map_sub, map_mul, eval_C, eval_X]
  apply Finset.sum_congr rfl
  intro r _
  ring
theorem spatial_cardinal_affine_eval_center  (x y : Covariate d) :
    eval (fun r => x r / 8) (spatialCardinalAffine x y) = spatialSquaredDistance x y := by
  rw [spatial_cardinal_affine_eval]
  simp only [spatialSquaredDistance, pow_two]
theorem spatial_cardinal_affine_degree  (x y : Covariate d) :
    (spatialCardinalAffine x y).totalDegree ≤ 1 := by
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro r _
  apply (totalDegree_sub _ _).trans
  apply max_le
  · simp only [totalDegree_C]; omega
  · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
def spatialCardinalPolynomial  (U : Fin n → Covariate d) (i : Fin n) :
    MvPolynomial (Fin d) ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, spatialCardinalAffine (U i) (U j)
theorem spatial_cardinal_polynomial_degree  (U : Fin n → Covariate d) (i : Fin n) :
    (spatialCardinalPolynomial U i).totalDegree ≤ n - 1 := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin n)).erase i, 1 :=
      Finset.sum_le_sum (fun j _ => spatial_cardinal_affine_degree (U i) (U j))
    _ = _ := by simp
theorem spatial_cardinal_polynomial_eval_neighbor 
    (U : Fin n → Covariate d) (i j : Fin n) (hji : j ≠ i) :
    eval (fun r => U j r / 8) (spatialCardinalPolynomial U i) = 0 := by
  rw [spatialCardinalPolynomial, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    (by rw [spatial_cardinal_affine_eval]; simp)
def spatialUnaryWeight  (lam t : ℝ) (x y : Covariate d) : ℝ :=
  t * (lam * spatialSquaredDistance x y) ^ 2 *
    Real.exp (-t * lam * spatialSquaredDistance x y)
def spatialCardinalScale  (lam : ℝ) (t : Fin n → ℝ)
    (U : Fin n → Covariate d) (i : Fin n) : ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
    t j * lam ^ 2 * Real.exp (-t j * lam * spatialSquaredDistance (U i) (U j))
def spatialCardinalWeight  (lam : ℝ) (t : Fin n → ℝ)
    (U : Fin n → Covariate d) (i : Fin n) : ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, spatialUnaryWeight lam (t j) (U i) (U j)
theorem spatial_frame_covariance_rank_one  [Fintype κ] [DecidableEq κ]
     (v : κ → ℝ) (S : ℝ) (φ : Fin n → κ → ℝ) (i l : Fin n) :
    spatialFrameCovariance (fun β β' => S * v β * v β') φ i l =
      S * (∑ β, φ i β * v β) * (∑ β, φ l β * v β) := by
  simp only [spatialFrameCovariance, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro β' _
  ring
theorem spatial_frame_covariance_add  [Fintype κ] [DecidableEq κ]
     (A B ) (φ : Fin n → κ → ℝ) (i l : Fin n) :
    spatialFrameCovariance (fun β β' => A β β' + B β β') φ i l =
      spatialFrameCovariance A φ i l + spatialFrameCovariance B φ i l := by
  simp only [spatialFrameCovariance, mul_add, Finset.sum_add_distrib]
theorem spatial_frame_covariance_sum {κ J : Type*} [Fintype κ] [DecidableEq κ]
     (s : Finset J) (A : J → κ → κ → ℝ) (φ : Fin n → κ → ℝ) (i l : Fin n) :
    spatialFrameCovariance (fun β β' => ∑ j ∈ s, A j β β') φ i l =
      ∑ j ∈ s, spatialFrameCovariance (A j) φ i l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [spatialFrameCovariance]
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    rw [spatial_frame_covariance_add, ih]
end NearlyMinimax
