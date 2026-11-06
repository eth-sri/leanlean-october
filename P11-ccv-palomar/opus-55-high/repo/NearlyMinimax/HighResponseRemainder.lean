module

public import NearlyMinimax.HighResponseUpdates
public import RoughRegime.Macro

𝗌

/-! High-order remainder of the actual finite response reset. The
derivative budget below is derived from the ternary factors. -/
open MeasureTheory Set Polynomial
𝚨

𝗇 𝔗 derivative^[r]
𝗇 𝔤 s.card * b
𝗇 𝔫 ℝ[X]
𝗇 𝕬 r - k
𝗃 𝕳 (ἀ ..).trans
/-- Leibniz and the binomial theorem give a count-power derivative bound
for a genuine finite product, without an exponential in the count. -/
theorem polynomial_product_iterate_derivative_abs_bound [DecidableEq ι]
    s (P : ι → 𝔫) b z (hb : 0 ≤ b)
    (hP : ∀ i ∈ s, ∀ r , |(𝔗 $ P i ).eval z| ≤ b ^ r) :
    ∀ r , |(𝔗 $ ∏ i ∈ s, P i ).eval z| ≤ 𝔤 ^ r := by
  induction s using Finset.induction_on with
  | empty =>
    intro r
    by_cases hr : r = 0
    · simp_all
    · rw [Finset.prod_empty, iterate_derivative_one $ Nat.pos_of_ne_zero hr ]
      simp
  | @insert i s hi ih =>
    intro r
    rw [Finset.prod_insert hi, iterate_derivative_mul, eval_finsetSum]
    apply 𝕳 Finset.abs_sum_le_sum_abs
    calc
      _ ≤ ∑ k ∈ Finset.range $ r + 1 , r.choose k *
          (b ^ 𝕬 * 𝔤 ^ k ) := by
        apply Finset.sum_le_sum
        intro k hk
        simp
        apply mul_le_mul_of_nonneg_left _ $ Nat.cast_nonneg _
        exact mul_le_mul (hP i (Finset.mem_insert_self ..) 𝕬)
          (ih (fun j hj => hP j $ Finset.mem_insert_of_mem hj ) k)
          (abs_nonneg _) $ pow_nonneg hb _
      _ = (𝔤 + b) ^ r := by
        rw [add_pow]
        grind
      _ = ( (insert i s).card * b) ^ r := by
        rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
        ring

/-- Analytic iterated derivatives coincide with formal polynomial ones. -/
theorem polynomial_iteratedDeriv_eval (P : 𝔫) r :
    iteratedDeriv r P.eval = (𝔗 P).eval := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext z
    exact ((𝔗 P).hasDerivAt z).deriv

𝗇 𝔙 Icc 0 1
𝗇 𝔳 Icc (0 : ℝ) 1
theorem polynomial_iteratedDerivWithin_eval P r z
    (hz : z ∈ 𝔙) :
    iteratedDerivWithin r P.eval 𝔳 z =
      (𝔗 P).eval z := by
  rw [iteratedDerivWithin_eq_iteratedDeriv $ uniqueDiffOn_Icc $ by norm_num ]
  · exact congrFun (polynomial_iteratedDeriv_eval P r) z
  · simpa only [coe_aeval_eq_eval] using
      (P.contDiff_aeval (𝕜 := ℝ) r).contDiffAt
  · exact hz

𝗃 𝕸 2 * ἀ
𝗇 𝔄 𝕸 q + 2
/-- Coefficient truncation is exactly the analytic Taylor polynomial at
zero, including its one-sided endpoint derivatives. -/
def polynomialResponseTaylor (q : ℕ) (P : 𝔫) : 𝔫 :=
  ∑ k ∈ Finset.range 𝔄, monomial k (P.coeff k)

𝗇 𝔊 𝕸 q + 1
𝗇 𝕮 polynomialResponseTaylor q P
theorem polynomial_response_taylor_eval q P z :
    (𝕮).eval z =
      taylorWithinEval P.eval 𝔊 𝔙 0 z := by
  rw [taylor_within_apply]
  simp only [polynomialResponseTaylor, eval_finsetSum, eval_monomial]
  apply Finset.sum_congr rfl
  intro k hk
  rw [polynomial_iteratedDerivWithin_eval P k 0 $ by norm_num , ← coeff_zero_eq_eval_zero,
    coeff_iterate_derivative]
  simp only [Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul, sub_zero, smul_eq_mul]
  field_simp

𝗃 𝕴 ἀ q j
𝗇 𝔟 𝕴 responseWeight
𝗇 𝔡 𝕴 responseNode
𝗇 𝔴 1 ≤ q
theorem polynomial_response_taylor_exact q (hq : 𝔴) P :
     ∑ j : Fin 𝔄, 𝔟 *
      (𝕮).eval 𝔡 = P.coeff 2 := by
  have hdeg : (𝕮).natDegree ≤ 𝔊 := by
    apply natDegree_sum_le_of_forall_le
    intro k hk
    exact (natDegree_monomial_le _).trans $ by grind
  have hdegree : (𝕮).degree < 𝔄 :=
    degree_le_natDegree.trans_lt $ by exact_mod_cast
      ( hdeg.trans_lt $ by omega )
  rw [response_rule_exact q _ hdegree]
  simp only [polynomialResponseTaylor, finsetSum_coeff, coeff_monomial]
  aesop

𝗇 𝔭 𝔊 + 1
/-- The fixed extraction defect follows from an actual derivative bound
and Taylor's theorem, with exact extraction of every lower-order term. -/
theorem polynomial_response_extraction_remainder q (hq : 𝔴)
    P B (hB : 0 ≤ B)
    (hderiv : ∀ z ∈ 𝔙,
      |(derivative^[𝔄] P).eval z| ≤ B) :
    |(∑ j : Fin 𝔄, 𝔟 * P.eval 𝔡) -
      P.coeff 2| ≤ (∑ j : Fin 𝔄, |𝔟|) * B := by
  rw [← polynomial_response_taylor_exact q hq P, ← Finset.sum_sub_distrib]
  apply 𝕳 Finset.abs_sum_le_sum_abs
  calc
    _ ≤ ∑ j : Fin 𝔄, |𝔟| * B := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_sub, abs_mul]
      apply mul_le_mul_of_nonneg_left _ $ abs_nonneg _
      rw [polynomial_response_taylor_eval]
      have hsmooth : ContDiff ℝ 𝔭 P.eval := by
        simpa only [coe_aeval_eq_eval] using P.contDiff_aeval (𝕜 := ℝ) 𝔭
      have h := taylor_mean_remainder_bound
        (by norm_num) hsmooth.contDiffOn 𝕴 responseNode_mem_unit
         fun z hz => by
          rw [polynomial_iteratedDerivWithin_eval P 𝔭 z hz]
          bound
      rw [Real.norm_eq_abs, sub_zero] at h
      apply h.trans
      have hz := 𝕴 responseNode_mem_unit
      have hpow : 𝔡 ^ 𝔭 ≤ 1 :=
        pow_le_one₀ hz.1 hz.2
      have hfac : (1 : ℝ) ≤ (𝔊).factorial := by
        exact_mod_cast Nat.succ_le_of_lt $ Nat.factorial_pos 𝔊
      apply (div_le_self (mul_nonneg hB $ pow_nonneg hz.1 _ ) hfac).trans
      bound
    _ = _ := by rw [Finset.sum_mul]

𝗇 𝔎 ternaryLinePolynomial a f V δ y
𝗇 𝔑 f + z * δ
𝗇 𝔠 ((hasDerivAt_id z).mul_const δ).const_add f
/-- First and second formal line derivatives are the actual ternary
derivatives; all subsequent ones vanish. -/
theorem ternary_line_derivative_eval a f V δ z y :
    (𝔎).derivative.eval z =
      δ * ternaryMeanDerivative a 𝔑 y := by
  have h := (ternary_hasDerivAt_mean a 𝔑 V y).comp z
    𝔠
  have he := (𝔎).hasDerivAt z
  simp only [ternary_line_polynomial_eval] at he
  exact he.unique $ h.congr_deriv $ by ring

𝗃 𝕵 ἀ ^ 2
theorem ternary_line_second_derivative_eval a f V δ z y :
    (𝔎).derivative.derivative.eval z =
      𝕵 δ * ternaryMeanSecondDerivative a y := by
  have h := ((ternary_hasDerivAt_mean_derivative a 𝔑 y).comp z
    𝔠).const_mul δ
  have he := (𝔎).derivative.hasDerivAt z
  simp only [ternary_line_derivative_eval] at he
  exact he.unique $ h.congr_deriv $ by ring

𝗇 𝔇 (𝕸 ρ + a) / 𝕵 a
𝗇 𝔏 𝕸 η * B
𝗇 𝔔 2 / 𝕵 a
𝗇 𝔥 0 ≤ η
𝗇 𝔦 𝕸 η
𝗇 𝕯 0 < a
𝗇 𝕰 0 ≤ ρ
𝗃 𝕱 0 ≤ ternaryMass a ἀ V u
theorem ternary_line_iterate_derivative_abs_bound a f V δ η ρ B z
    y (ha : 𝕯) (hη : 𝔥) (hρ : 𝕰)
    (hB : 1 ≤ B) (hMean : 𝔇 ≤ B)
    (hSecond : 𝔔 ≤ B) (hf : |𝔑| ≤ ρ)
    (hp : ∀ u, 𝕱 𝔑) (hδ : |δ| ≤ 𝔦) :
    ∀ r , |(𝔗 𝔎).eval z| ≤
      𝔏 ^ r := by
  intro r
  rcases r with _ | _ | _ | r
  · rw [Function.iterate_zero_apply, ternary_line_polynomial_eval, pow_zero,
      abs_of_nonneg $ hp y ]
    exact ternary_mass_le_one a _ V ha.ne' hp y
  · rw [Function.iterate_one, ternary_line_derivative_eval, pow_one, abs_mul]
    apply (mul_le_mul hδ ((ternary_mean_derivative_abs_bound a _ ρ ha hρ hf y).trans hMean)
      (abs_nonneg _) $ by positivity ).trans_eq
    ring
  · change |(derivative^[2] 𝔎).eval z| ≤ 𝕵 𝔏
    rw [show 2 = 1 + 1 by rfl, Function.iterate_succ_apply', Function.iterate_one,
      ternary_line_second_derivative_eval, abs_mul, abs_of_nonneg $ sq_nonneg δ ]
    have hδsq : 𝕵 δ ≤ 𝕵 𝔦 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hδ 2
    have hSB : 𝔔 ≤ 𝕵 B := hSecond.trans $ by nlinarith
    exact (mul_le_mul hδsq ((ternary_mean_second_derivative_abs_bound a ha y).trans hSB)
      (abs_nonneg _) $ by positivity ).trans_eq $ by ring
  · rw [iterate_derivative_eq_zero $ (ternary_line_polynomial_natDegree a f V δ y).trans_lt
      $ by omega , eval_zero, abs_zero]
    positivity

𝗃 𝕹 f i + ἀ * δ i
𝗇 𝔵 𝕹 z
𝗃 𝕶 ἀ a (f i) V $ δ i
/-- The scalar response error at every count has the true fixed high
power of the signal amplitude, with a count-polynomial prefactor. -/
theorem response_scalar_high_order_remainder q (hq : 𝔴) n
    a V η ρ B f δ y
    (ha : 𝕯) (hη : 𝔥) (hρ : 𝕰) (hB : 1 ≤ B)
    (hMean : 𝔇 ≤ B) (hSecond : 𝔔 ≤ B)
    (hf : ∀ z ∈ 𝔙, ∀ i, |𝔵| ≤ ρ)
    (hp : ∀ z ∈ 𝔙, ∀ i u, 𝕱 𝔵)
    (hδ : ∀ i, |δ i| ≤ 𝔦) :
    |(∑ j : Fin 𝔄, 𝔟 *
      ∏ i, ternaryMass a 𝕹 𝔡 V (y i)) -
      (responseLinePolynomial n a V f δ y).coeff 2| ≤
      (∑ j : Fin 𝔄, |𝔟|) *
        (n * 𝔏) ^ 𝔄 := by
  simp only [← response_line_polynomial_eval]
  apply polynomial_response_extraction_remainder q hq _ _ $ by positivity
  intro z hz
  simpa only [responseLinePolynomial, Finset.card_univ, Fintype.card_fin] using
    polynomial_product_iterate_derivative_abs_bound Finset.univ
      (fun i => 𝕶 ternaryLinePolynomial $ y i )
      𝔏 z (by positivity)
      (fun i _ => 𝕶 ternary_line_iterate_derivative_abs_bound η ρ B z
        (y i) ha hη hρ hB hMean hSecond (hf z hz i) (hp z hz i) $ hδ i ) 𝔄

section SpatialRemainder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

𝗇 𝔱 coefficientDirection η w φ c v
𝗇 𝕭 coefficientRegression η g w φ c
𝗇 𝔅 (responseLinePolynomial n a V 𝕭 𝔱 y).coeff 2
𝗇 𝔉 ι → ℝ
𝗇 𝔒 Fin n → ℝ
𝗇 𝔮 covarianceAction C A
𝗇 𝔰 Fin n → 𝔉
𝗇 𝔷 fun v => 𝔅
/-- The genuine Hessian contraction, represented by its polynomial
quadratic coefficient. -/
def highResponseQuadraticAction (C a V η : ℝ) (A : ι → 𝔉)
    (g w : 𝔒) (φ : 𝔰) (c : 𝔉)
    (y : Fin n → Fin 3) : ℝ :=
  𝔮 𝔷

𝗇 𝕲 highResponseProduct a V η g w φ
𝗇 𝔈 fun c => 𝕲 c y
𝗇 𝔍 highResponseQuadraticAction C a V η A g w φ c y
theorem high_response_quadratic_eq_exact_rule C a V η
    A (g w : 𝔒) φ
    (c : 𝔉) y :
    𝔍 =
      responseMatrixAction n C A c 𝔈 := by
  apply congrArg 𝔮
  funext v
  simp only [highResponseProduct, coefficientRegression_reset]
  exact (response_line_rule_exact n n a V _ _ y le_rfl).symm

𝗇 𝔐 𝕵 η * ∑ i, w i ^ 2 * d i * highResponseVarianceTerm a V η g w φ c y i
𝗇 𝔚 ∀ i l, spatialFrameCovariance A φ i l = if i = l then d i else 0
𝗇 𝔧 ∀ i j, A i j = A j i
theorem high_response_quadratic_heat C a V η
    A (hC : C ≠ 0) (hA : 𝔧)
    g w φ (c : 𝔉)
    y (d : 𝔒)
    (hdiag : 𝔚) :
    𝔍 =
      𝔐 := by
  rw [high_response_quadratic_eq_exact_rule]
  exact high_response_matrix_heat n le_rfl C a V η A hC hA g w φ c y d hdiag

𝗇 𝔓 ∑ k, φ i k * v k
𝗇 𝔛 C⁻¹
𝗇 𝔞 ∑ k, φ i k * (v k - c k)
𝗇 𝔢 (mul_le_mul_of_nonneg_left (hw i) hη).trans_eq $ mul_one η
𝗇 𝔨 (mul_le_mul hm hprof (abs_nonneg _) hη).trans_eq
𝗇 𝔲 η * w i
omit [DecidableEq ι] in
theorem coefficient_direction_abs_le (C η : ℝ) (hη : 𝔥)
    (w : 𝔒) (φ : 𝔰) (c v : 𝔉)
    (hc : ∑ k, |c k| ≤ 𝔛) (hv : ∑ k, |v k| ≤ 𝔛)
    (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : 𝔉, ∑ k, |v k| ≤ 𝔛 → ∀ i, |𝔓| ≤ 1)
    (i : Fin n) : |𝔱 i| ≤ 𝔦 := by
  have hprof : |𝔞| ≤ 2 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact (abs_sub _ _).trans $ by linarith [hφ v hv i, hφ c hc i]
  have hm : |𝔲| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]
    exact 𝔢
  change |𝔲 * 𝔞| ≤ 𝔦
  rw [abs_mul]
  exact 𝔨 $ by ring

𝗇 𝔜 𝔲 * ∑ k, φ i k * coefficientReset c v z k
𝗇 𝔩 ρ / 2
omit [DecidableEq ι] in
theorem coefficient_regression_reset_abs_le (C η ρ : ℝ)
    (hη : 𝔥) (hηρ : η ≤ 𝔩) (g w : 𝔒)
    (φ : 𝔰) (c v : 𝔉) (z : ℝ) (hz : z ∈ 𝔳)
    (hc : ∑ k, |c k| ≤ 𝔛) (hv : ∑ k, |v k| ≤ 𝔛)
    (hg : ∀ i, |g i| ≤ 𝔩) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : 𝔉, ∑ k, |v k| ≤ 𝔛 → ∀ i, |𝔓| ≤ 1)
    (i : Fin n) :
    |𝕭 i + z * 𝔱 i| ≤ ρ := by
  have hi := congrFun (coefficientRegression_reset η g w φ c v z) i
  rw [← hi]
  have hball := coefficientReset_mem_ball C c v z hz hc hv
  have hprof := hφ _ hball i
  change |g i + 𝔜| ≤ ρ
  have hm : |𝔲| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]
    exact 𝔢
  have hpterm : |𝔜| ≤ η := by
    rw [abs_mul]
    exact 𝔨 $ mul_one η
  exact (abs_add_le _ _).trans $ by linarith [hg i, hpterm]

𝗇 𝔖 𝕴 responseWeight * 𝕲 (coefficientReset c v 𝕴 responseNode) y
𝗇 𝔘 coefficient_regression_reset_abs_le C η ρ hη hηρ g w φ c v z hz hc hv hg hw hφ i
𝗇 𝔬 ∀ u, 𝕱 f
𝗇 𝔯 responseMatrixAction q C A c 𝔈
𝗇 𝔶 ∑ j : Fin 𝔄, 𝔖
/-- The actual finite signed matrix reset differs from its Hessian by
the paper's high-order response remainder, for every local count. -/
theorem high_response_matrix_high_order_remainder (q : ℕ) (hq : 𝔴)
    (C a V η ρ B : ℝ) (hC : 0 < C) (ha : 𝕯)
    (hη : 𝔥) (hρ : 𝕰) (hηρ : η ≤ 𝔩)
    (hB : 1 ≤ B) (hMean : 𝔇 ≤ B) (hSecond : 𝔔 ≤ B)
    A (g w : 𝔒) φ
    (c : 𝔉) y
    (hc : ∑ k, |c k| ≤ 𝔛) (hg : ∀ i, |g i| ≤ 𝔩) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : 𝔉, ∑ k, |v k| ≤ 𝔛 → ∀ i, |𝔓| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → 𝔬) :
    |𝔯 -
      𝔍| ≤
      (2 * 𝕵 C * ∑ k, ∑ l, |A k l|) *
        ((∑ j : Fin 𝔄, |𝔟|) *
          ((n : ℝ) * 𝔏) ^ 𝔄) := by
  unfold responseMatrixAction highResponseQuadraticAction
  rw [show 𝔮
      (fun v => 𝔶) -
      𝔮
        𝔷 =
      𝔮 fun v =>
        𝔶 -
        𝔅 by
    simp only [covarianceAction, mul_sub, Finset.sum_sub_distrib]]
  apply covarianceAction_abs_le
  intro k l s t
  let v := covarianceAtom C k l s t
  have hv := covarianceAtom_mem_ball C hC k l s t
  simp only [highResponseProduct, coefficientRegression_reset]
  apply response_scalar_high_order_remainder q hq n a V η ρ B _ _ y
    ha hη hρ hB hMean hSecond
  · exact fun z hz i => 𝔘
  · exact fun z hz i u => hp _
      𝔘 u
  · exact fun i => coefficient_direction_abs_le C η hη w φ c v hc hv hw hφ i

/-- A fixed budget determined only by the ternary neighborhood. -/
def highResponseDerivativeBudget (a ρ : ℝ) : ℝ :=
  max 1 $ max 𝔇 𝔔

𝗇 𝔪 highResponseDerivativeBudget a ρ
theorem highResponseDerivativeBudget_guards a ρ :
    1 ≤ 𝔪 ∧
    𝔇 ≤ 𝔪 ∧
    𝔔 ≤ 𝔪 := ⟨le_max_left .., 𝕳 le_max_left $ le_max_right .. ,
    𝕳 le_max_right $ le_max_right .. ⟩

/-- The actual response Taylor defect. -/
def highResponseDefect (q : ℕ) (C a V η : ℝ) (A : ι → 𝔉)
    (g w : 𝔒) (φ : 𝔰) (c : 𝔉)
    (y : Fin n → Fin 3) : ℝ :=
  𝔯 -
    𝔍

𝗇 𝔣 highResponseDefect q C a V η A g w φ c y
/-- Actual cardinal heat identity with the full response remainder at
every count, rather than a truncated count hypothesis. -/
theorem high_response_matrix_heat_with_defect q
    C a V η A (hC : C ≠ 0) (hA : 𝔧)
    g w φ (c : 𝔉)
    y (d : 𝔒)
    (hdiag : 𝔚) :
    𝔯 =
      𝔐 +
        𝔣 := by
  unfold highResponseDefect
  rw [high_response_quadratic_heat C a V η A hC hA g w φ c y d hdiag]
  ring

/-- The remainder constant is explicit and independent of count and
frame dimension. -/
def highResponseRemainderConstant (q : ℕ) (C a ρ : ℝ) : ℝ :=
  2 * 𝕵 C * (∑ j : Fin 𝔄, |𝔟|) *
    𝕸 𝔪 ^ 𝔄

theorem high_response_defect_abs_bound q (hq : 𝔴)
    C a V η ρ (hC : 0 < C) (ha : 𝕯)
    (hη : 𝔥) (hρ : 𝕰) (hηρ : η ≤ 𝔩)
    A (g w : 𝔒) φ
    c y
    (hc : ∑ k, |c k| ≤ 𝔛) (hg : ∀ i, |g i| ≤ 𝔩) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : 𝔉, ∑ k, |v k| ≤ 𝔛 → ∀ i, |𝔓| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → 𝔬) :
    |𝔣| ≤
      highResponseRemainderConstant q C a ρ * (∑ k, ∑ l, |A k l|) *
        n ^ 𝔄 * η ^ 𝔄 := by
  obtain ⟨hB, hMean, hSecond⟩ := highResponseDerivativeBudget_guards a ρ
  have h := high_response_matrix_high_order_remainder q hq C a V η ρ
    𝔪 hC ha hη hρ hηρ hB hMean hSecond
    A g w φ c y hc hg hw hφ hp
  apply h.trans_eq
  unfold highResponseRemainderConstant
  ring
