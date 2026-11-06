module

public import NearlyMinimax.AtomicVariation
public import NearlyMinimax.LowSmoothnessVariance
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual finite scalar extraction and signed covariance resets of the
high-smoothness local response operator. -/
open MeasureTheory Set Polynomial
𝚨

𝗃 𝖍 ἀ ^ 2
𝗃 𝖑 ternaryMass a ἀ V
/-- A ternary response on an affine regression line, as an actual polynomial. -/
def ternaryLinePolynomial (a f V δ : ℝ) (y : Fin 3) : ℝ[X] :=
  C (𝖑 f y) + monomial 1 (δ * ternaryMeanDerivative a f y) +
    monomial 2 (𝖍 δ * ternaryVarianceDerivative a y)

theorem ternary_line_polynomial_eval a f V δ z y :
    (ternaryLinePolynomial a f V δ y).eval z = ternaryMass a (f + z * δ) V y := by
  fin_cases y <;> simp [ternaryLinePolynomial, ternaryMass, ternaryMeanDerivative,
    ternaryVarianceDerivative] <;> ring

theorem ternary_line_polynomial_natDegree a f V δ y :
    (ternaryLinePolynomial a f V δ y).natDegree ≤ 2 := by
  apply (natDegree_add_le ..).trans
  aesop

𝗇 𝔓 𝙔
𝗇 𝔠 𝙈
𝗃 𝖒 ἀ a $ f i
/-- Complete finite product likelihood on the same line. -/
def responseLinePolynomial (n : ℕ) (a V : ℝ) (f δ : 𝔓)
    (y : 𝔠) : ℝ[X] := ∏ i, 𝖒 ternaryLinePolynomial V (δ i) (y i)

𝗇 𝔄 f i + z * δ i
𝗇 𝔔 responseLinePolynomial n a V f δ y
𝗃 𝕴 𝖑 ἀ $ y i
theorem response_line_polynomial_eval n a V f δ
    y z :
    (𝔔).eval z =
      ∏ i, 𝕴 𝔄 := by
  simp only [responseLinePolynomial, eval_prod]
  simp only [ternary_line_polynomial_eval]

𝗇 𝕽 𝘿
theorem response_line_polynomial_natDegree n a V f δ
    y : (𝔔).natDegree ≤ 𝘕₁ := by
  apply (natDegree_prod_le ..).trans
  calc
    _ ≤ ∑ _i : Fin n, 2 := Finset.sum_le_sum fun i _ => ternary_line_polynomial_natDegree ..
    𝕽 := by simp [mul_comm]

𝗇 𝔅 Fin 𝖵
𝗇 𝔍 responseWeight q j * ∏ i, ternaryMass a (f i + responseNode q j * δ i) V (y i)
𝗇 𝔳 ∑ j : 𝔅, 𝔍
/-- Exact cardinal quadratic extraction of the genuine likelihood through
count q, including arbitrary offsets and incoming regression fields. -/
theorem response_line_rule_exact q n a V f δ
    y (hn : n ≤ q) :
    𝔳 =
      (𝔔).coeff 2 := by
  simpa only [response_line_polynomial_eval] using response_rule_exact q
    𝔔
    $ degree_le_natDegree.trans_lt $ by
      exact_mod_cast (response_line_polynomial_natDegree n a V f δ y).trans_lt 𝖡₃

𝗇 𝔉 ((hasDerivAt_id z).mul_const $ δ i ).const_add $ f i
𝗇 𝕲 ternaryMeanSecondDerivative a $ y i
𝗃 𝖋 ἀ i ^ 2
𝗇 𝔒 fun i _ => 𝖋 δ * 𝕲
𝗃 𝖎 ἀ i z
𝗇 𝔜 fun i _ => 𝖎 hH
𝗇 𝔤 HasDerivAt (H i) 𝖎 D z
𝗇 𝔥 HasDerivAt (D i) 𝖎 E z
𝗃 𝖏 ternaryMeanDerivative a ἀ $ y i
𝗇 𝔪 fun i z => δ i * 𝖏 𝔄
𝗇 𝔫 fun i z => 𝕴 𝔄
𝗇 𝔭 ((ternary_hasDerivAt_mean_derivative a 𝔄 $ y i ).comp z 𝔉).const_mul $ δ i
𝗇 𝔴 (ternary_hasDerivAt_mean a 𝔄 V $ y i ).comp z 𝔉
𝗃 𝕵 ἀ Finset.univ H D
𝗇 𝕾 𝘓
𝗃 𝖐 fun i _ => ἀ i 0
/-- Formal quadratic coefficient equals half the genuine second directional
product derivative, so its heat contraction can be evaluated explicitly. -/
theorem response_line_quadratic_coefficient n a V f δ
    y :
    2 * (𝔔).coeff 2 =
      finiteProductSecond Finset.univ
        𝔫
        𝔪
        𝔒 0 := by
  let Q := 𝔔
  let H := 𝔫
  let D := 𝔪
  let E : Fin n → 𝕾 := 𝔒
  have hH i z : 𝔤 := by
    have h := 𝔴
    exact h.congr_deriv 𝖢₃
  have hD i z : 𝔥 := by
    have h := 𝔭
    grind
  have hQ z : HasDerivAt Q.eval (𝕵 finiteProductFirst z) z := by
    simpa only [Q, response_line_polynomial_eval] using
      𝕵 finite_product_hasDerivAt z 𝔜
  have hd : Q.derivative.eval = 𝕵 finiteProductFirst := by
    funext z
    exact (Q.hasDerivAt z).unique $ hQ z
  have hsecond := 𝕵 finite_product_first_hasDerivAt E 0
    𝖐 hH 𝖐 hD
  rw [← hd] at hsecond
  have he := (Q.derivative.hasDerivAt 0).unique hsecond
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_derivative] at he
  grind

𝗇 𝔎 𝗃
𝗇 𝔷 ∀ z ∈ 𝔎, HasDerivAt H (D z) z
𝗇 𝕬 ∀ z ∈ 𝔎, HasDerivAt D (E z) z
𝗇 𝕷 𝙋
𝗇 𝕿 D u - D 0
𝗇 𝖀 convex_Icc 0 1
𝗃 𝖌 fun x hx => (ἀ x hx).hasDerivWithinAt
/-- A uniform second-derivative estimate yields an affine Taylor remainder
bound at every scalar response mark; no score bound is assumed. -/
theorem affine_line_remainder_abs_bound (H D E : 𝕾) B (hB : 𝙐)
    (hH : 𝔷)
    (hD : 𝕬)
    (hE : ∀ z ∈ 𝔎, |E z| ≤ B)
    z (hz : z ∈ 𝔎) : |H z - H 0 - z * D 0| ≤ B := by
  have hzero : 0 ∈ Icc 𝕷 1 := 𝖠₄
  have hDdiff u (hu : u ∈ Icc 0 1) : |𝕿| ≤ B := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      𝖌 hD
       fun x hx => by bound
      𝖀 hzero hu
    simp at h
    have huabs := abs_le.mpr ⟨𝖤₃, hu.2⟩
    nlinarith
  let G := fun u => H u - H 0 - u * D 0
  have hG u hu : HasDerivAt G 𝕿 u :=
    (((hH u hu).sub_const $ H 0 ).sub $ (hasDerivAt_id u).mul_const $ D 0 ).congr_deriv 𝖢₃
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    𝖌 hG
     fun x hx => by bound
    𝖀 hzero hz
  have hzabs := abs_le.mpr ⟨𝖤₃, hz.2⟩
  simp only [G, sub_zero, zero_mul, sub_self, Real.norm_eq_abs] at h
  nlinarith

𝗇 𝔗 responseNode q j
𝗇 𝔛 responseWeight q j
𝗇 𝔲 𝔛 * (H 𝔗 - H 0 - 𝔗 * D 0)
𝗇 𝕭 ∑ j : 𝔅, 𝔛 * H 𝔗
/-- The real scalar cardinal action has the all-count quadratic derivative
bound; its affine part cancels exactly by the proved moments. -/
theorem response_scalar_action_abs_bound q (H D E : 𝕾) B (hB : 𝙐)
    (hH : 𝔷)
    (hD : 𝕬)
    (hE : ∀ z ∈ 𝔎, |E z| ≤ B)
    (hnodes : ∀ j , 𝔗 ∈ 𝔎) :
    |𝕭| ≤
      (∑ j : 𝔅, |𝔛|) * B := by
  have he : 𝕭 =
      ∑ j : 𝔅, 𝔲 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
    rw [← Finset.sum_mul, ← Finset.sum_mul, response_zero_mass, response_zero_mean]
    simp
  rw [he]
  calc
    _ ≤ ∑ j : 𝔅, |𝔲| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ j : 𝔅, |𝔛| * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (affine_line_remainder_abs_bound H D E B hB
        hH hD hE _ $ hnodes j ) $ abs_nonneg _
    𝕽 := by rw [Finset.sum_mul]

section Covariance
𝛑

𝗇 𝔊 𝙛
𝗇 𝔟 1 - z
/-- Incoming coefficients are reset by the actual scalar mark and covariance atom. -/
def coefficientReset (c v : 𝔊) (z : ℝ) : 𝔊 :=
  fun i => 𝔟 * c i + z * v i

𝗇 𝔯 covarianceAction C A
𝗇 𝕼 coefficientReset c v 𝔗
/-- The paper's B_A as a genuine finite signed action. -/
def responseMatrixAction (q : ℕ) (C : ℝ) (A : ι → 𝔊)
    (c : 𝔊) (Φ : 𝔊 → ℝ) : ℝ :=
  𝔯 fun v => ∑ j : 𝔅,
    𝔛 * Φ 𝕼

theorem responseMatrixAction_zero_mass q C A (c : 𝔊) :
    𝗔 A c 𝙃 = 0 := by
  simp [responseMatrixAction, response_zero_mass, covarianceAction]

𝗇 𝔖 v k - c k
𝗇 𝔙 ∀ i j, 𝘩 = A j i
𝗇 𝕸 𝔖 * (v l - c l)
𝗃 𝖊 𝔯 fun v => ἀ
theorem covariance_displacement_second C A
    (hC : 𝚆) (hA : 𝔙) (c : 𝔊) k l :
    𝖊 𝕸 = A k l := by
  have hf : (fun v : 𝔊 => 𝕸) =
       fun v => v k * v l + -c l * v k + -c k * v l + c k * c l * 1 := by
    funext v
    ring
  rw [hf, covarianceAction_add, covarianceAction_add, covarianceAction_add,
    covarianceAction_mul, covarianceAction_mul, covarianceAction_mul,
    covariance_second_moment_symmetric C A hC hA, covariance_zero_mean,
    covariance_zero_mean, covariance_zero_mass]
  ring

theorem responseNode_mem_unit q j :
    𝔗 ∈ 𝔎 := by
  have hden : 𝕷 < (2 * q + 1 : ℕ) := 𝖠₃
  constructor
  · exact div_nonneg  𝖠₃  hden.le
  · apply (div_le_one hden).mpr
    exact_mod_cast 𝖡₃

𝗇 𝔡 𝗳
𝗇 𝖆 coefficientReset c v z
omit [DecidableEq ι] in
theorem coefficientReset_mem_ball (C : ℝ) (c v : 𝔊) (z : ℝ)
    (hz : z ∈ Icc 𝕷 1)
    (hc : ∑ i, |c i| ≤ 𝔡) (hv : ∑ i, |v i| ≤ 𝔡) :
     ∑ i, |𝖆 i| ≤ 𝔡 := by
  calc
    _ ≤ ∑ i, (𝔟 * |c i| + z * |v i|) := by
      apply Finset.sum_le_sum
      intro i _
      apply (abs_add_le _ _).trans_eq
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hz.2] : 0 ≤ 𝔟), abs_of_nonneg hz.1]
    _ = 𝔟 * ∑ i, |c i| + z * ∑ i, |v i| := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 𝔟 * 𝔡 + z * 𝔡 := add_le_add
      (mul_le_mul_of_nonneg_left hc $ by linarith [hz.2] ) $ mul_le_mul_of_nonneg_left hv hz.1
    𝕽 := 𝖢₃

𝗇 𝔘 φ i k
𝗇 𝔰 Fin n → 𝔊
𝗇 𝖁 𝔘 * φ l m
/-- The finite spatial polynomial frame is evaluated without any abstract
smoothness or response assumptions. -/
def spatialFrameCovariance (A : ι → 𝔊) (φ : 𝔰)
    (i l : Fin n) : ℝ := ∑ k, ∑ m, 𝖁 * A k m

𝗇 𝔞 𝗌₂
𝗇 𝖈 𝔘 * c k
𝗇 𝔱 ∑ k, 𝖈
def coefficientRegression (η : ℝ) (g w : 𝔓)
    (φ : 𝔰) (c : 𝔊) : 𝔓 :=
  fun i => g i + 𝔞 * 𝔱

𝗇 𝔵 ∑ k, 𝔘 * 𝔖
def coefficientDirection (η : ℝ) (w : 𝔓)
    (φ : 𝔰) (c v : 𝔊) : 𝔓 :=
  fun i => 𝔞 * 𝔵

𝗇 𝖇 coefficientDirection η w φ c
𝗇 𝔏 𝖇 v i
𝗇 𝕯 𝗡 φ
𝗇 𝔚 𝕯 c i
𝗇 𝔦 𝕯 𝖆
𝗇 𝔬 ∑ k, 𝔘 * 𝖆 k
𝗇 𝔶 𝔚 + z * 𝔏
𝗇 𝕹 ∑ k, 𝔘 * v k
omit [DecidableEq ι] in
theorem coefficientRegression_reset (η : ℝ) (g w : 𝔓)
    (φ : 𝔰) (c v : 𝔊) (z : ℝ) :
    𝔦 =
      fun i => 𝔶 := by
  funext i
  have hs : 𝔬 =
      𝔱 + z * (𝕹 - 𝔱) := by
    calc
      _ = ∑ k, (𝖈 + z * (𝔘 * v k - 𝖈)) := by
        apply Finset.sum_congr rfl
        intro k _
        dsimp [coefficientReset]
        ring
      𝕽 := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [coefficientRegression, coefficientDirection, hs, mul_sub, Finset.sum_sub_distrib]
  ring

𝗇 𝔧 𝖍 η
𝗇 𝔮 𝖇 v
𝗇 𝕳 fun v => 𝔏 * 𝔮 l
𝗇 𝖂 𝔧 * w i * w l
theorem covariance_direction_product C η A
    (hC : 𝚆) (hA : 𝔙) w
    φ (c : 𝔊) (i l : Fin n) :
    𝔯 𝕳 = 𝖂 * spatialFrameCovariance A φ i l := by
  have he : 𝕳 =
       fun v => 𝖂 *
        ∑ k, ∑ m, 𝖁 * (𝔖 * (v m - c m)) := by
    funext v
    simp only [coefficientDirection, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    grind
  rw [he, covarianceAction_mul, covarianceAction_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [covarianceAction_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [covarianceAction_mul, covariance_displacement_second C A hC hA]

/-- Real response likelihood of a single local coefficient state. -/
def highResponseProduct (a V η : ℝ) (g w : 𝔓)
    (φ : 𝔰) (c : 𝔊) (y : 𝔠) : ℝ :=
  ∏ i, 𝕴 𝔚

𝗇 𝖉 𝖨 φ
𝗇 𝔐 𝗔 A c fun c => 𝖉 c y
𝗇 𝔢 𝕯 c
𝗇 𝖃 𝙖
/-- The exact finite signed response operator is its directional Hessian
contraction through count q. This comes from actual cardinal evaluation. -/
theorem high_response_matrix_second q (hn : n ≤ q)
    C a V η A (g w : 𝔓)
    φ (c : 𝔊) y :
    𝔐 =
      𝖃 * 𝔯 fun v =>
        finiteProductSecond Finset.univ
          (fun i z => 𝕴 𝔶)
          (fun i z => 𝔏 * 𝖏 𝔶)
          (fun i _ => 𝖍 𝔏 * 𝕲) 0 := by
  rw [← covarianceAction_mul]
  apply congrArg 𝔯
  funext v
  simp only [highResponseProduct, coefficientRegression_reset]
  rw [response_line_rule_exact q n a V _ _ y hn]
  have h := response_line_quadratic_coefficient n a V
    𝔢 𝔮 y
  linarith

/-- The variance derivative before substituting a common variance. -/
def highResponseVarianceTerm (a V η : ℝ) (g w : 𝔓)
    (φ : 𝔰) (c : 𝔊) (y : 𝔠) (i : Fin n) : ℝ :=
  𝙿 * ∏ l ∈ (Finset.univ : 𝙍).erase i,
    ternaryMass a (𝕯 c l) V (y l)

𝗇 𝕰 δ v i
𝗇 𝖅 f i + z * 𝕰
𝗇 𝔇 finiteProductSecond Finset.univ (fun i z => 𝖑 𝖅 $ y i ) (fun i z => 𝕰 * 𝖏 𝖅) (fun i _ => 𝖍 𝕰 * e i) 0
𝗇 𝕮 (∏ k ∈ (Finset.univ.erase i).erase l, p k) * m l * m i * (δ v l * δ v i)
𝗇 𝔈 ∑ l ∈ Finset.univ.erase i, 𝕮 + (∏ l ∈ Finset.univ.erase i, p l) * e i * (𝕰 * 𝕰)
𝗇 𝔩 𝖷 φ c y i
𝗇 𝕺 covariance_direction_product C η A hC hA w φ c
/-- Spatial cardinal covariance cancels every off-diagonal product derivative.
This is the actual heat identity of the realized finite signed update. -/
theorem high_response_matrix_heat q (hn : n ≤ q)
    C a V η A (hC : 𝚆) (hA : 𝔙)
    g w φ (c : 𝔊) y
    (d : 𝔓)
    (hdiag : ∀ i l, spatialFrameCovariance A φ i l = if 𝚛₁ then d i else 0) :
    𝔐 =
      𝔧 * ∑ i, 𝖋 w * d i * 𝔩 := by
  let f := 𝔢
  let δ := 𝖇
  let p := fun i => 𝖒 ternaryMass V $ y i
  let m := fun i => 𝖒 ternaryMeanDerivative $ y i
  let e := fun i => 𝕲
  let S := fun v => ∑ i : Fin n,
    𝔈
  have hS v :
      𝔇 = S v := by
    simp only [finiteProductSecond, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    · rw [Finset.sum_mul]
      grind
    ring
  rw [high_response_matrix_second q hn C a V η A g w φ c y]
  change 𝖃 * 𝖊 𝔇 = _
  simp_rw [hS]
  rw [covarianceAction_sum]
  have he i : 𝖊 𝔈 =
      2 * 𝔧 * 𝖋 w * d i * 𝔩 := by
    rw [covarianceAction_add, covarianceAction_sum]
    have hcross l (hl : l ∈ Finset.univ.erase i) :
        𝖊 𝕮 = 0 := by
      rw [covarianceAction_mul, 𝕺 l i,
        hdiag l i, ite_eq_right $ Finset.ne_of_mem_erase hl , mul_zero, mul_zero]
    rw [Finset.sum_eq_zero fun l hl => hcross l hl , zero_add, covarianceAction_mul,
      𝕺 i i, hdiag i i, ite_eq_left rfl]
    dsimp [e, highResponseVarianceTerm]
    rw [ternary_heat_identity]
    ring
  simp_rw [he]
  rw [Finset.mul_sum, Finset.mul_sum]
  ring

𝗇 𝕱 𝗠 / 𝖍 a
𝗇 𝔑 4 * (𝖍 𝕱 + 2 / 𝖍 a) * 𝖍 n * 𝖍 η
𝗇 𝔣 2 * η
𝗃 𝕶 ἀ z hz i
𝗇 𝕻 z ∈ Icc 0 1
𝗇 𝖄 4 * 𝔧 * S
𝗃 𝖓 fun i _ => 𝕶 ἀ
/-- All-count cardinal action bound propagated through the genuine product
likelihood. The assumptions are individual legality and displacement bounds. -/
theorem response_scalar_product_action_abs_bound q n (hn : 𝗚)
    a V η ρ (f δ : 𝔓) (y : 𝔠)
    (ha : 𝙆) (hη : 𝗼) (hρ : 𝗛₁)
    (hf : ∀ z ∈ 𝔎, ∀ i, |𝔄| ≤ ρ)
    (hp : ∀ z ∈ 𝔎, ∀ i u, 0 ≤ 𝖑 𝔄 u)
    (hδ : ∀ i, |δ i| ≤ 𝔣) :
    |𝔳| ≤
      (∑ j : 𝔅, |𝔛|) *
        𝔑 := by
  let H := 𝔫
  let D := 𝔪
  let E : Fin n → 𝕾 := 𝔒
  let A := 𝕱
  let S := 2 / 𝖍 a
  have hS : 0 ≤ S := 𝖠₃
  have hH i z : 𝔤 := by
    have h := 𝔴
    exact h.congr_deriv 𝖢₃
  have hD i z : 𝔥 := by
    have h := 𝔭
    grind
  have hHbound z (hz : 𝕻) i : |𝖎 H| ≤ 1 := by
    rw [abs_of_nonneg $ 𝕶 hp $ y i ]
    exact ternary_mass_le_one a _ V ha.ne' 𝕶 hp $ y i
  have hDbound z (hz : 𝕻) i : |𝖎 D| ≤ 𝔣 * A := by
    rw [abs_mul]
    exact mul_le_mul (hδ i) (𝗥₁ 𝕶 hf $ y i )
      (abs_nonneg _) 𝖠₃
  have hEbound z i : |𝖎 E| ≤ 𝖄 := by
    rw [abs_mul, 𝗤]
    have hs : 𝖋 δ ≤ 𝖍 𝔣 := by
      simpa only [sq_abs] using 𝗂 (hδ i) 2
    have h := mul_le_mul hs (ternary_mean_second_derivative_abs_bound a ha $ y i )
      (abs_nonneg _) 𝖠₃
    linarith
  apply response_scalar_action_abs_bound q _ 𝕵 finiteProductFirst
    (𝕵 finiteProductSecond E) _  𝖠₃ 
    (fun z hz => 𝕵 finite_product_hasDerivAt z 𝔜)
    (fun z hz => 𝕵 finite_product_first_hasDerivAt E z
      𝔜 fun i _ => 𝖎 hD ) _ $ responseNode_mem_unit q
  intro z hz
  have h := 𝕵 finite_product_second_abs_bound E z (𝔣 * A) 𝖄
     𝖠₃   𝖠₃  𝖓 hHbound
    𝖓 hDbound fun i _ => hEbound z i
  simp at h
  have hnR : 𝙠 ≤ n := by exact_mod_cast hn
  have hnn : 0 ≤ 𝙒 ^ 2 - n := 𝖥₃
  have hmore := mul_nonneg hnn $ mul_nonneg (sq_nonneg η) hS
  linarith

𝗇 𝔨 (mul_le_mul hm hprof (abs_nonneg _) hη).trans_eq
/-- Matrix-response bound at every count, derived from legal frame resets
and the actual ternary product derivatives. -/
theorem high_response_matrix_all_count_bound q (hn : 𝗚)
    C a V η ρ (hC : 𝙴) (ha : 𝙆) (hη : 𝗼) (hρ : 𝗛₁)
    (hηρ : η ≤ 𝙸) A (g w : 𝔓)
    φ c y
    (hc : ∑ k, |c k| ≤ 𝔡) (hg : ∀ i, |g i| ≤ 𝙸)
    (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : 𝔊, ∑ k, |v k| ≤ 𝔡 → ∀ i, |𝕹| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ 𝖑 f u) :
    |𝔐| ≤
      (2 * 𝖍 C * ∑ k, ∑ l, |A k l|) *
        ((∑ j : 𝔅, |𝔛|) *
          𝔑) := by
  apply covarianceAction_abs_le
  intro k l s t
  let v := covarianceAtom C k l s t
  have hv := covarianceAtom_mem_ball C hC k l s t
  let f := 𝔢
  let δ := 𝔮
  have hr (z : ℝ) : 𝔦 =
      fun i => 𝔄 := coefficientRegression_reset η g w φ c v z
  have hδ i : |δ i| ≤ 𝔣 := by
    have hprof : |𝔵| ≤ 2 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact (abs_sub ..).trans $ by linarith [hφ v hv i, hφ c hc i]
    have hm : |𝔞| ≤ η := by
      rw [abs_mul, abs_of_nonneg hη]
      bound
    change |𝔞 * 𝔵| ≤ 𝔣
    rw [abs_mul]
    exact 𝔨 𝖢₃
  have hf (z : ℝ) (hz : 𝕻) i : |𝔄| ≤ ρ := by
    have hi := congrFun (hr z) i
    rw [← hi]
    have hball := coefficientReset_mem_ball C c v z hz hc hv
    have hprof := hφ _ hball i
    change |g i + 𝔞 * 𝔬| ≤ ρ
    have hm : |𝔞| ≤ η := by
      rw [abs_mul, abs_of_nonneg hη]
      bound
    have hpterm : |𝔞 * 𝔬| ≤ η := by
      rw [abs_mul]
      exact 𝔨 $ mul_one η
    grind
  have he : ∑ j : 𝔅, 𝔛 *
      𝖉 𝕼 y =
      𝔳 := by
    simp only [highResponseProduct, hr]
  rw [he]
  exact response_scalar_product_action_abs_bound q n hn a V η ρ f δ y ha hη hρ hf
    (fun z hz i u => hp _ 𝕶 hf u) hδ
