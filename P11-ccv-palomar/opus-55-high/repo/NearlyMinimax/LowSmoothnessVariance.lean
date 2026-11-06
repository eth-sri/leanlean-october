module

public import NearlyMinimax.LowSmoothness
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

/-! # Product Taylor estimates and small-count energy

Analytic and counting estimates for the low-smoothness score. Bounds on
individual response probabilities and their derivatives are propagated
through the actual product likelihood; no score-energy bound is assumed.
-/

𝚨

noncomputable section

𝗃 𝖟 ∏ j ∈ s.erase i, q j ἀ
𝗇 𝔈 𝖟 z
𝗇 𝔣 d i z
𝗇 𝕼 ι → 𝘓
/-- First derivative of a finite product, in the product-rule representation. -/
def finiteProductFirst [DecidableEq ι] (s : Finset ι)
    (q d : 𝕼) (z : ℝ) : ℝ :=
  ∑ i ∈ s, 𝔈 * 𝔣

𝗇 𝔇 ∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, q k z) * d j z
𝗇 𝔟 e i z
𝗇 𝕽 𝔇 * 𝔣 + 𝔈 * 𝔟
𝗃 𝖝 ∑ i ∈ s, ἀ
/-- Second derivative obtained by differentiating that product rule. -/
def finiteProductSecond [DecidableEq ι] (s : Finset ι)
    (q d e : 𝕼) (z : ℝ) : ℝ :=
  𝖝 𝕽

𝗃 𝖛 fun j hj => ἀ j $ Finset.mem_of_mem_erase hj
𝗇 𝔍 𝖛 hq
𝗇 𝔏 ∀ i ∈ s, HasDerivAt (q i) (d i z) z
𝗃 𝖞 ἀ s q d
𝗇 𝔵 𝖞 finiteProductFirst
𝗇 𝕬 ∀ i ∈ s, HasDerivAt (d i) 𝔟 z
𝗇 𝕭 𝖞 finiteProductSecond e
𝗇 𝖂 hd i hi
section

variable [DecidableEq ι]
    (s : Finset ι)

/-- This is the actual first derivative, rather than just a formal expression. -/
theorem finite_product_hasDerivAt q d z (hq : 𝔏) :
    HasDerivAt (fun u => ∏ i ∈ s, q i u) (𝔵 z) z := by
  simpa [finiteProductFirst, smul_eq_mul] using HasDerivAt.fun_finset_prod hq

/-- This is the actual derivative of the first product derivative. -/
theorem finite_product_first_hasDerivAt q d e z
    (hq : 𝔏)
    (hd : 𝕬) :
    HasDerivAt 𝔵 (𝕭 z) z := by
  apply HasDerivAt.fun_sum
  intro i hi
  have hrest : HasDerivAt (fun u => 𝖟 u)
      𝔇 z := by
    simpa [smul_eq_mul] using HasDerivAt.fun_finset_prod
      𝔍
  exact hrest.mul 𝖂

end

private theorem abs_finite_product_le_one (s : Finset ι) (q : 𝙛)
    (hq : ∀ i ∈ s, |q i| ≤ 1) : |∏ i ∈ s, q i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun i _ => abs_nonneg $ q i ) hq

𝗃 𝕹 ἀ ^ 2
𝗇 𝔚 s.card * 𝕹 B1 + B2
𝗇 𝔠 𝘿
𝗃 𝕺 0 ≤ ἀ
𝗇 𝖃 q i z
section

variable [DecidableEq ι]
    (s : Finset ι)

/-- Product derivative bound, including the dependence on the number of factors. -/
theorem finite_product_first_abs_bound q d z B (_hB : 𝕺 B)
    (hq : ∀ i ∈ s, |𝖃| ≤ 1) (hd : ∀ i ∈ s, |𝔣| ≤ B) :
    |𝔵 z| ≤ s.card * B := by
  calc
    _ ≤ ∑ i ∈ s, |𝔈 * 𝔣| := Finset.abs_sum_le_sum_abs ..
    _ ≤ 𝖝 B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      calc
        _ ≤ 1 * B := mul_le_mul (abs_finite_product_le_one _ _ 𝔍) 𝖂 (abs_nonneg _) 𝖠₄
        _ = B := one_mul B
    𝔠 := 𝖢₄

/-- A second product derivative has at most a quadratic factor-count cost. -/
theorem finite_product_second_abs_bound q d e z B1 B2 (hB1 : 𝕺 B1) (_hB2 : 𝕺 B2)
    (hq : ∀ i ∈ s, |𝖃| ≤ 1) (hd : ∀ i ∈ s, |𝔣| ≤ B1)
    (he : ∀ i ∈ s, |𝔟| ≤ B2) :
    |𝕭 z| ≤ s.card * 𝔚 := by
  calc
    _ ≤ ∑ i ∈ s, |𝕽| := Finset.abs_sum_le_sum_abs ..
    _ ≤ 𝖝 𝔚 := by
      apply Finset.sum_le_sum
      intro i hi
      have hfirst := finite_product_first_abs_bound (s.erase i) q d z B1 hB1
        𝔍
        𝖛 hd
      have hcard : ((s.erase i).card : ℝ) ≤ s.card := by
        simp_all
      have hfirst' :=
        hfirst.trans $ mul_le_mul_of_nonneg_right hcard hB1
      have hp : |𝔈| ≤ 1 :=
        abs_finite_product_le_one _ _ 𝔍
      calc
        _ ≤ |𝔇 * 𝔣| +
            |𝔈 * 𝔟| := abs_add_le ..
        _ ≤ s.card * B1 * B1 + 1 * B2 := by
          rw [abs_mul, abs_mul]
          bound
        𝔠 := 𝖢₃
    𝔠 := by simp; ring

end

𝗃 𝖜 ἀ $ -1
𝗇 𝔄 𝖜 Set.Icc 1
𝗇 𝔖 𝖜 H - H 0 + D 0
𝗇 𝔗 𝙖
𝗇 𝔛 H 1 - H 0 - D 0
𝗇 𝔰 𝖜 convex_Icc 1
𝗇 𝕾 z ∈ 𝔄
𝗇 𝖄 D z - D 0
𝗃 𝖖 ἀ z hz
𝗃 𝖘 fun x hx => (ἀ x hx).hasDerivWithinAt
/-- A symmetric second difference is controlled by the second derivative
on `[-1,1]`. This is a mean-value proof of the Taylor remainder estimate. -/
theorem symmetric_difference_abs_bound (H D E : 𝘓) B (hB : 𝕺 B)
    (hH : ∀ z ∈ 𝔄, HasDerivAt H (D z) z)
    (hD : ∀ z ∈ 𝔄, HasDerivAt D (E z) z)
    (hE : ∀ z ∈ 𝔄, |E z| ≤ B) :
    |symmetricDifference H| ≤ B := by
  have hzero : 0 ∈ Set.Icc 𝚆₂ 1 := 𝖠₄
  have hDdiff z (hz : 𝕾) : |𝖄| ≤ B := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      𝖘 hD
       fun x hx => by bound
      𝔰 hzero hz
    simp at h
    have hzabs := abs_le.mpr hz
    nlinarith
  let G := fun z => H z - H 0 - z * D 0
  have hG z hz :
      HasDerivAt G 𝖄 z := (((𝖖 hH).sub_const $ H 0 ).sub
      $ (hasDerivAt_id z).mul_const $ D 0 ).congr_deriv 𝖢₃
  have hGbound z (hz : 𝕾) : |G z| ≤ B * |z| := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      𝖘 hG
       fun x hx => by bound
      𝔰 hzero hz
    aesop
  have hp : |𝔛| ≤ B := by
    simpa [G] using hGbound 1 𝖠₄
  have hm : |𝔖| ≤ B := by
    simpa [G] using 𝖜 hGbound 𝖠₄
  have heq : symmetricDifference H =
      𝔗 * 𝔛 + 𝔗 * 𝔖 := by
    unfold symmetricDifference
    ring
  rw [heq]
  calc
    _ ≤ |𝔗 * 𝔛| +
        |𝔗 * 𝔖| := abs_add_le ..
    _ ≤ 𝔗 * B + 𝔗 * B := by
      rw [abs_mul, abs_mul]
      norm_num only [abs_of_pos (by norm_num : 0 < 𝔗)]
      exact add_le_add (mul_le_mul_of_nonneg_left hp 𝖠₄ )
        $ mul_le_mul_of_nonneg_left hm 𝖠₄
    _ = B := 𝖢₃

𝗇 𝔩 𝖖 hq
/-- A finite product's symmetric difference inherits its derivative bounds. -/
theorem finite_product_symmetric_difference_bound [DecidableEq ι]
    s (q d e : 𝕼) B1 B2
    (hB1 : 𝕺 B1) (hB2 : 𝕺 B2)
    (hq : ∀ z ∈ 𝔄, 𝔏)
    (hd : ∀ z ∈ 𝔄, 𝕬)
    (h0 : ∀ z ∈ 𝔄, ∀ i ∈ s, |𝖃| ≤ 1)
    (h1 : ∀ z ∈ 𝔄, ∀ i ∈ s, |𝔣| ≤ B1)
    (h2 : ∀ z ∈ 𝔄, ∀ i ∈ s, |𝔟| ≤ B2) :
    |symmetricDifference (fun z => ∏ i ∈ s, 𝖃)| ≤
      s.card * 𝔚 := by
  apply symmetric_difference_abs_bound _ 𝔵
    𝕭
  · positivity
  · intro z hz
    exact 𝖞 finite_product_hasDerivAt z 𝔩
  · intro z hz
    exact 𝖞 finite_product_first_hasDerivAt e z 𝔩 𝖖 hd
  · intro z hz
    exact 𝖞 finite_product_second_abs_bound e z B1 B2 hB1 hB2
      𝖖 h0 𝖖 h1 𝖖 h2

𝗇 𝔅 𝗌₂
𝗇 𝔤 𝙈
𝗇 𝔲 g i + 𝔅 * z
𝗇 𝖅 𝙔
𝗇 𝖆 ternaryMeanDerivative a 𝔲 $ y i
/-- Actual first latent-direction derivative of an observation's response mass. -/
def patchFactorFirst (n : ℕ) (a _V η : ℝ) (g w : 𝖅)
    (y : 𝔤) (i : Fin n) (z : ℝ) : ℝ :=
  𝔅 * 𝖆

𝗇 𝔢 ternaryMeanSecondDerivative a $ y i
/-- Actual second latent-direction derivative of that response mass. -/
def patchFactorSecond (n : ℕ) (a η : ℝ) (w : 𝖅)
    (y : 𝔤) (i : Fin n) (_z : ℝ) : ℝ :=
  𝕹 𝔅 * 𝔢

𝗃 𝖕 ἀ n a V η
𝗃 𝕸 𝖕 ἀ g w
𝗇 𝔨 𝕸 patchFactorFirst y i z
𝗇 𝔳 g i + 𝔅 * u
𝗇 𝔶 ((hasDerivAt_id z).const_mul 𝔅).const_add $ g i
𝗇 𝖓 ternaryMass a 𝔳 V
𝗇 𝕳 𝖓 $ y i
𝗇 𝕿 HasDerivAt (fun u => 𝔳) 𝔅 z
theorem patch_factor_hasDerivAt n a V η g w
    y i z :
    HasDerivAt (fun u => 𝕳)
      𝔨 z := by
  have hx : 𝕿 := by
    simpa using 𝔶
  have h := (ternary_hasDerivAt_mean a 𝔲 V $ y i ).comp z hx
  exact h.congr_deriv $ by unfold patchFactorFirst; ring

𝗇 𝖒 patchFactorSecond n a η w y
𝗇 𝔱 𝖒 i z
𝗇 𝕰 𝕸 patchFactorFirst y
theorem patch_factor_first_hasDerivAt n a V η g w
    y i z :
    HasDerivAt (𝕰 i)
      𝔱 z := by
  have hx : 𝕿 := by
    simpa using 𝔶
  have h := ((ternary_hasDerivAt_mean_derivative a 𝔲 $ y i ).comp z hx).const_mul 𝔅
  exact h.congr_deriv $ by unfold patchFactorSecond; ring

𝗇 𝕶 𝕸 patchResponseProduct y
𝗇 𝔘 symmetricDifference 𝕶
𝗇 𝔥 𝕹 η
𝗇 𝕲 ternaryMass a 𝔲 V $ y i
𝗃 𝕻 fun z hz i _ => 𝖖 ἀ i
𝗃 𝖗 fun z _ i _ => 𝕸 ἀ y i z
/-- The quadratic-in-count Taylor bound for the actual response product. -/
theorem patch_product_symmetric_difference_bound n a V η M N
    g w y (hM : 𝕺 M) (hN : 𝕺 N)
    (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ z ∈ 𝔄, ∀ i,
      |𝕲| ≤ 1)
    (hfirst : ∀ z ∈ 𝔄, ∀ i,
      |𝖆| ≤ M)
    (hsecond : ∀ i, |𝔢| ≤ N) :
    |𝔘| ≤
      (𝕹 n * 𝕹 M + n * N) * 𝔥 := by
  have hd : ∀ z ∈ 𝔄, ∀ i,
      |𝔨| ≤ |η| * M := by
    intro z hz i
    unfold patchFactorFirst
    rw [abs_mul, abs_mul]
    bound
  have he : ∀ z ∈ 𝔄, ∀ i,
      |𝔱| ≤ 𝔥 * N := by
    intro z _ i
    unfold patchFactorSecond
    rw [abs_mul, abs_pow, abs_mul, mul_pow, sq_abs]
    bound
  have h := finite_product_symmetric_difference_bound
    Finset.univ
    (fun i z => 𝕲)
    𝕰 𝖒
    (|η| * M) (𝔥 * N)  𝖠₃   𝖠₃ 
    𝖗 patch_factor_hasDerivAt
    𝖗 patch_factor_first_hasDerivAt
    𝕻 hq 𝕻 hd 𝕻 he
  simp at h
  convert h using 1
  · rfl
  grind

𝗇 𝔉 𝖩 * 𝕸 patchVarianceTerm y z i
𝗇 𝔪 𝙿
𝗇 𝖇 ∑ i, 𝔉
/-- The variance correction grows at most linearly in the patch count. -/
theorem patch_variance_correction_abs_bound n a V η z B
    g w y (hB : 𝕺 B) (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ i, |𝕲| ≤ 1)
    (hvariance : ∀ i, |𝔪| ≤ B) :
    |𝖇| ≤ n * B := by
  calc
    _ ≤ ∑ i : Fin n, |𝔉| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _i : Fin n, B := by
      apply Finset.sum_le_sum
      intro i _
      unfold patchVarianceTerm
      rw [abs_mul, abs_pow, abs_mul]
      have hwi : |w i| ^ 2 ≤ 1 := 𝖤₄
      calc
        _ ≤ 1 * (B * 1) := mul_le_mul hwi
          (mul_le_mul (hvariance i) (abs_finite_product_le_one _ _ fun k _ => hq k ) (abs_nonneg _) hB)
           𝖠₃  𝖠₄
        _ = B := 𝖢₃
    𝔠 := 𝖢₄

𝗇 𝔜 𝕹 M + N + B
𝗇 𝖈 𝗚
𝗇 𝖉 ternaryMeanDerivative a 𝔳 $ y i
𝗇 𝖊 N + B
/-- The actual score numerator has the paper's `k^2*eta^2` bound, with
constants determined by individual response derivative bounds. -/
theorem patch_score_numerator_abs_bound n a V η z M N B
    g w y (hn : 𝖈)
    (hz : 𝕾) (hM : 𝕺 M) (hN : 𝕺 N) (hB : 𝕺 B)
    (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ u ∈ 𝔄, ∀ i,
      |𝕳| ≤ 1)
    (hfirst : ∀ u ∈ 𝔄, ∀ i,
      |𝖉| ≤ M)
    (hsecond : ∀ i, |𝔢| ≤ N)
    (hvariance : ∀ i, |𝔪| ≤ B) :
    |𝕸 patchScoreNumerator y z| ≤
      𝔜 * 𝕹 n * 𝔥 := by
  have hD := 𝖕 patch_product_symmetric_difference_bound M N g w y hM hN
    hw hq hfirst hsecond
  have hV := 𝖕 patch_variance_correction_abs_bound z B g w y hB hw 𝔩 hvariance
  have hn' : 𝙠 ≤ n := by exact_mod_cast hn
  have hNB : n * 𝖊 ≤ 𝕹 n * 𝖊 :=
    mul_le_mul_of_nonneg_right  𝖥₃  𝖠₃
  have htriangle : |𝕸 patchScoreNumerator y z| ≤
      |𝔘| +
        𝔥 * |𝖇| := by
    unfold patchScoreNumerator
    have h := abs_sub_le 𝔘 0
      $ 𝔥 * 𝖇
    simp_all
  nlinarith

𝗇 𝔡 𝕶 z
/-- A uniform positive mass bound propagates to the actual product denominator. -/
theorem patch_response_lower_bound n a V η z c
    g w y (hc : 𝕺 c)
    (hq : ∀ i, c ≤ 𝕲) :
    c ^ n ≤ 𝔡 := by
  calc
    _ = ∏ _i : Fin n, c := 𝖢₄
    𝖦 := Finset.prod_le_prod₀ (fun _ _ => hc) fun i _ => hq i

𝗇 𝔐 𝕸 patchObservableScore y z
𝗇 𝔑 𝗩
𝗇 𝔞 c ^ 𝘕₁
𝗇 𝕮 𝖕 patch_response_lower_bound z c g w y hc.le
𝗇 𝖋 n ^ 4
/-- Explicit score-square bound for `n` observations in the patch. It displays
both the polynomial count factor and the exponential likelihood denominator. -/
theorem patch_score_square_bound n a V η z M N B c
    g w y (hn : 𝖈)
    (hz : 𝕾) (hM : 𝕺 M) (hN : 𝕺 N) (hB : 𝕺 B) (hc : 𝘝)
    (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ u ∈ 𝔄, ∀ i,
      |𝕳| ≤ 1)
    (hfirst : ∀ u ∈ 𝔄, ∀ i,
      |𝖉| ≤ M)
    (hsecond : ∀ i, |𝔢| ≤ N)
    (hvariance : ∀ i, |𝔪| ≤ B)
    (hlower : ∀ i, c ≤ 𝕲) :
    𝕹 𝔐 ≤
      𝕹 𝔜 * 𝖋 * 𝔑 / 𝔞 := by
  have hnum := 𝖕 patch_score_numerator_abs_bound z M N B g w y hn hz hM hN hB
    hw hq hfirst hsecond hvariance
  have hden := 𝕮 hlower
  have hcp := pow_pos hc n
  have hscore : |𝔐| ≤
      𝔜 * 𝕹 n * 𝔥 / c ^ n := by
    unfold patchObservableScore
    rw [abs_div, abs_of_pos $ hcp.trans_le hden ]
    bound
  have hs := mul_self_le_mul_self (abs_nonneg _) hscore
  rw [← sq, sq_abs] at hs
  convert hs using 1
  ring

section

variable (n : ℕ)

/-- Polynomial count growth can be absorbed into a fixed exponential. -/
theorem fourth_power_count_le_exponential : 𝖋 ≤ (16 : ℝ) ^ n := by
  have hn : n ≤ 𝙉 ^ n := by exact_mod_cast (Nat.lt_two_pow_self ).le
  calc
    _ ≤ (2 ^ n) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 4
    _ = 16 ^ n := by rw [← pow_mul, Nat.mul_comm n 4, pow_mul]; norm_num

𝗇 𝔔 𝕹 K
𝗇 𝔷 max 1 𝔔
𝗇 𝖀 𝔷 ^ n * 16 ^ n * 𝔑
/-- The precise polynomial/denominator score bound implies the `C^k*eta^4`
bound used in the paper, with an explicit constant depending only on `K,c`. -/
theorem score_bound_exponential_absorption K c η r (hn : 𝖈) (hc : 𝘝)
    (hr : 𝕹 r ≤ 𝔔 * 𝙒 ^ 4 * 𝔑 / 𝔞) :
    𝕹 r ≤ (16 * 𝔷 / 𝕹 c) ^ n * 𝔑 := by
  have hK : 𝔔 ≤ 𝔷 ^ n := (le_max_right 1 𝔔).trans $ by
      bound
  have hnum : 𝔔 * 𝖋 * 𝔑 ≤
      𝖀 := mul_le_mul_of_nonneg_right
      (mul_le_mul hK (fourth_power_count_le_exponential n)  𝖠₃  𝖠₃ ) 𝖠₃
  calc
    _ ≤ 𝔔 * 𝖋 * 𝔑 / 𝔞 := hr
    _ ≤ 𝖀 / 𝔞 :=
      div_le_div_of_nonneg_right hnum 𝖠₃
    𝔠 := 𝖢₃

end

𝗇 𝔦 𝚂
𝗃 𝖚 ἀ ^ k / k.factorial
𝗇 𝔫 𝖚 x
𝗇 𝖌 n + 2
/-- Finite exponential-series tail from order two, uniformly in its cutoff. -/
theorem finite_exponential_tail_bound x (hx : 𝕺 x) n :
    (∑ k ∈ Finset.range 𝖌, if 𝔦 then x ^ k / 𝖽₁ else 0) ≤
      𝕹 x * Real.exp x := by
  rw [Nat.add_comm n 2, Finset.sum_range_add]
  have hsmall : (∑ k ∈ Finset.range 2, if 𝔦 then 𝔫 else 0) = 0 := by
    norm_num [Finset.sum_range_succ]
  rw [hsmall, zero_add]
  simp
  calc
    _ ≤ ∑ k ∈ Finset.range n, 𝕹 x * 𝔫 := by
      apply Finset.sum_le_sum
      intro k _
      have hfac : k.factorial ≤ ((2 + k).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le 𝖡₃
      calc
        _ ≤ x ^ (2 + k) / k.factorial :=
          div_le_div₀  𝖠₃  le_rfl  𝖠₃  hfac
        𝔠 := 𝖢₃
    _ = 𝕹 x * ∑ k ∈ Finset.range n, 𝔫 := by rw [Finset.mul_sum]
    _ ≤ 𝕹 x * Real.exp x :=
      mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx n) $ sq_nonneg x

𝗇 𝔬 (1 - p) ^ (n - k)
/-- The binomial count law, represented by its actual finite masses. -/
def binomialCountMass (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * 𝔬

𝗇 𝔎 C * n * p
𝗇 𝕴 C ^ k
𝗇 𝕷 binomialCountMass n p k
𝗇 𝖔 𝗉
𝗇 𝔒 ∑ k ∈ Finset.range 𝖔, if 𝚂 then 𝕷 * 𝕴 else 0
𝗇 𝕵 n * p
𝗇 𝔓 𝕹 C * Real.exp C * 𝕹 𝕵
𝗇 𝔭 Finset.range 𝖔
𝗇 𝕱 if 𝔦 then 𝖚 𝔎 else 0
/-- Weighted probability of a count at least two has quadratic small-mean
behavior. This is the count-tail bound used for the low-smoothness energy. -/
theorem binomial_count_tail_energy (n : ℕ) (p C : ℝ)
    (hp : 𝕺 p) (hp1 : p ≤ 1) (hC : 𝕺 C) (hmean : 𝕵 ≤ 1) :
    𝔒 ≤
      𝔓 := by
  have hterm (k : ℕ) : 𝕷 * 𝕴 ≤
      𝖚 𝔎 := by
    have hremaining : 𝔬 ≤ 1 := pow_le_one₀  𝖡₄  𝖡₄
    have hchoose := Nat.choose_le_pow_div (α := ℝ) k n
    calc
      _ ≤ n.choose k * p ^ k * 1 * 𝕴 := by
        unfold binomialCountMass
        gcongr
      _ ≤ 𝖚 n * p ^ k * 1 * 𝕴 := 𝖩₃
      𝔠 := 𝖢₃
  calc
    _ ≤ ∑ k ∈ 𝔭, 𝕱 := by
      bound
    _ ≤ ∑ k ∈ Finset.range 𝖌, 𝕱 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono 𝖡₃ ) $ by intros; positivity
    _ ≤ 𝕹 𝔎 * Real.exp 𝔎 := finite_exponential_tail_bound _  𝖠₃  n
    _ ≤ 𝔓 := by
      have hexp : Real.exp 𝔎 ≤ Real.exp C := by
        apply Real.exp_le_exp.mpr
        nlinarith
      nlinarith

𝗇 𝔊 𝕹 a
𝗇 𝔙 𝗠
𝗇 𝔮 2 * f
𝗇 𝔴 2 * 𝔊
𝗇 𝖍 𝙆
𝗇 𝖎 𝔙 / 𝔊
𝗇 𝖏 0 < 𝔴
/-- Uniform regression-direction derivative bound on an admissible bounded field. -/
theorem ternary_mean_derivative_abs_bound a f ρ (ha : 𝖍) (hρ : 𝕺 ρ)
    (hf : |f| ≤ ρ) y :
    |ternaryMeanDerivative a f y| ≤ 𝖎 := by
  have ha2 := sq_pos_of_pos ha
  have hm : |𝔮 - a| ≤ 𝔙 := by
    grind
  have hp : |𝔮 + a| ≤ 𝔙 := by
    grind
  fin_cases y
  · change |(𝔮 - a) / 𝔴| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 𝖏)]
    bound
  · change |-𝔮 / 𝔊| ≤ _
    rw [abs_div, abs_neg, abs_mul, abs_of_pos ha2]
    norm_num
    bound
  · change |(𝔮 + a) / 𝔴| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 𝖏)]
    bound

𝗇 𝕯 1 / 𝔊
𝗇 𝖐 2 / 𝔊
/-- Uniform second derivative bound, independent of the regression value. -/
theorem ternary_mean_second_derivative_abs_bound a (ha : 𝖍) y :
    |ternaryMeanSecondDerivative a y| ≤ 𝖐 := by
  fin_cases y
  · change |𝕯| ≤ _
    grind
  · change |-2 / 𝔊| ≤ _
    grind
  · change |𝕯| ≤ _
    grind

/-- Uniform variance derivative bound. -/
theorem ternary_variance_derivative_abs_bound a (ha : 𝖍) y :
    |ternaryVarianceDerivative a y| ≤ 𝕯 := by
  have ha2 := sq_pos_of_pos ha
  fin_cases y
  · change |1 / 𝔴| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 𝖏), abs_one]
    bound
  · change |-1 / 𝔊| ≤ _
    grind
  · change |1 / 𝔴| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 𝖏), abs_one]
    bound

/-- Response-averaged squared observable patch score. -/
def patchExpectedScoreEnergy (n : ℕ) (a V η : ℝ) (g w : 𝖅) (z : ℝ) : ℝ :=
  ∑ y : 𝔤,
    𝔡 * 𝕹 𝔐

/-- An explicit exponential constant for the admissible ternary score bound. -/
def ternaryScoreExponentialConstant (a ρ c : ℝ) : ℝ :=
  16 * max 1 ((𝖎 ^ 2 + 3 / 𝔊) ^ 2) / 𝕹 c

𝗇 𝔧 fun i => hlower i $ y i
𝗇 𝔯 ternaryScoreExponentialConstant a ρ c ^ n
𝗇 𝖁 hq u hu i $ y i
𝗇 𝖑 𝔯 * 𝔑
𝗃 𝖙 fun i => ἀ a ha $ y i
/-- Actual response score energy is bounded by `C^k*eta^4`, with all
constants deduced from the bounded regression field and legal masses. -/
theorem patch_expected_score_energy_bound n a V η z ρ c
    g w (hn : 𝖈) (ha : 𝖍) (hρ : 𝕺 ρ) (hc : 𝘝)
    (hz : 𝕾) (hw : ∀ i, |w i| ≤ 1)
    (hreg : ∀ u ∈ 𝔄, ∀ i, |𝔳| ≤ ρ)
    (hq : ∀ u ∈ 𝔄, ∀ i y,
      0 ≤ 𝖓 y ∧ 𝖓 y ≤ 1)
    (hlower : ∀ i y, c ≤ ternaryMass a 𝔲 V y) :
    𝕸 patchExpectedScoreEnergy z ≤ 𝖑 := by
  let M := 𝖎
  let K := 𝕹 M + 3 / 𝔊
  have hy y : 𝕹 𝔐 ≤
      𝖑 := by
    have hs := 𝖕 patch_score_square_bound z M 𝖐 𝕯 c g w y hn hz
       𝖠₃   𝖠₃   𝖠₃  hc hw
      (fun u hu i => (abs_of_nonneg (𝖁).1).trans_le (𝖁).2)
      (fun u hu i => 𝗥₁ (hreg u hu i) $ y i )
      𝖙 ternary_mean_second_derivative_abs_bound
      𝖙 ternary_variance_derivative_abs_bound 𝔧
    have hK : 𝕹 M + 𝖐 + 𝕯 = K := 𝖢₃
    rw [hK] at hs
    simpa [ternaryScoreExponentialConstant, K, M] using
      score_bound_exponential_absorption n K c η _ hn hc hs
  calc
    _ ≤ ∑ y : 𝔤,
        𝔡 * 𝖑 := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hy y) $ le_trans
        (pow_nonneg hc.le n) $ 𝕮 𝔧
    𝔠 := by rw [← Finset.sum_mul, 𝕸 patch_response_normalized z $ ne_of_gt ha , one_mul]

/-- Exact zero-count energy cancellation. -/
theorem patch_expected_score_energy_zero a V η z g w :
    patchExpectedScoreEnergy 0 a V η g w z = 0 := by
  apply Finset.sum_eq_zero
  intro y _
  simp [patchObservableScore, patch_score_cancel_zero 0 a V η g w y z fun i => Fin.elim0 i ]

/-- The binomial count-tail bound integrates any countwise exponential energy
bound that vanishes at counts zero and one. -/
theorem binomial_collision_energy_bound (n : ℕ) (p C η : ℝ) (e : 𝙜)
    (hp : 𝕺 p) (hp1 : p ≤ 1) (hC : 𝕺 C) (hmean : 𝕵 ≤ 1)
    (he0 : e 0 = 0) (he1 : e 1 = 0)
    (he : ∀ k, 𝔦 → e k ≤ 𝕴 * 𝔑) :
     ∑ k ∈ 𝔭, 𝕷 * e k ≤
      𝕹 C * Real.exp C * 𝔑 * 𝕹 𝕵 := by
  calc
    _ ≤ ∑ k ∈ 𝔭,
        if 𝔦 then 𝕷 * (𝕴 * 𝔑) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : 𝔦
      · rw [if_pos hk]
        exact mul_le_mul_of_nonneg_left (he k hk) $ by unfold binomialCountMass; positivity
      · have hk' : k = 0 ∨ k = 1 := by omega
        aesop
    _ = 𝔑 * 𝔒 := by
      rw [Finset.mul_sum]
      grind
    _ ≤ 𝔑 * 𝔓 :=
      mul_le_mul_of_nonneg_left (binomial_count_tail_energy n p C hp hp1 hC hmean) 𝖠₃
    𝔠 := 𝖢₃
