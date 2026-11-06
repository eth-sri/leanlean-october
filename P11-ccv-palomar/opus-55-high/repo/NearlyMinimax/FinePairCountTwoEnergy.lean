module

public import NearlyMinimax.FinePairScoreBounds
public import NearlyMinimax.CardinalProductDesign
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Spatial square bounds for the genuine count-two three-row numerator. -/
𝚫
𝚪
𝚨
𝚩
𝚭

𝗇 𝔊 N * exactEuclideanDistance x y
def finePairDistanceFactor (N : ℝ) (x y : Covariate d) : ℝ :=
  (1 + 𝔊) * Real.exp (-𝔊)

𝗃 𝔞 0 ≤ ἀ
theorem finePairDistanceFactor_nonneg (hN : 𝔞 N) (x y : Covariate d) :
    0 ≤ finePairDistanceFactor N x y := mul_nonneg (by have h := exactEuclideanDistance_nonneg x y; positivity) 𝙫

𝗇 𝔏 finePairDistanceFactor N xy.1 xy.2
theorem finePairDistanceFactor_measurable d N :
    Measurable fun xy : 𝙩 => 𝔏 := ((continuous_const.add $ exactEuclideanDistance_continuous.const_mul N ).mul
    $ exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp ).measurable

theorem finePairDistanceFactor_square_absorption (hN : 𝔞 N)
    (x y : Covariate d) :
     finePairDistanceFactor N x y ^2 ≤ 6 * Real.exp (-𝔊) := by
  unfold finePairDistanceFactor
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : 2 * -𝔊 = -(2 * 𝔊) := 𝖢₃
  rw [he]
  exact pair_defect_exponential_absorption _
    $ mul_nonneg hN $ exactEuclideanDistance_nonneg x y

𝗇 𝔛 𝖪
𝗇 𝔅 (𝔛).prod 𝔛
𝗇 𝔍 fun xy => Real.exp $ -(N * exactEuclideanDistance xy.1 xy.2)
𝗇 𝔎 neg_nonpos.mpr $ mul_nonneg hN.le $ exactEuclideanDistance_nonneg ..
𝗃 𝔜 ἀ^2
theorem finePairDistanceFactor_square_integrable (hN : 𝘹) :
    Integrable (fun xy => 𝔜 𝔏)
      𝔅 := by
  have hm := (finePairDistanceFactor_measurable d N).pow_const 2
  have he : Integrable 𝔍
      𝔅 :=
    Integrable.of_bound
      (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp).measurable.aestronglyMeasurable 1
      $ Filter.Eventually.of_forall fun xy => by
        rw [Real.norm_eq_abs, 𝚖]
        exact Real.exp_le_one_iff.mpr 𝔎
  apply (he.const_mul 6).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun xy => by
    rw [Real.norm_eq_abs, abs_sq]
    exact finePairDistanceFactor_square_absorption hN.le ..

theorem finePairDistanceFactor_square_integral_le (hd : 𝗆) (hN : 𝘹) :
     ∫ xy : 𝙩, 𝔜 𝔏
      ∂𝔅 ≤
      6 * 𝖥 * spatialExponentialConstant d / 𝚝₂ := by
  have he : Integrable 𝔍
      𝔅 :=
    Integrable.of_bound
      (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp).measurable.aestronglyMeasurable 1
      $ Filter.Eventually.of_forall fun xy => by
        rw [Real.norm_eq_abs, 𝚖]
        exact Real.exp_le_one_iff.mpr 𝔎
  have hi := integral_mono (finePairDistanceFactor_square_integrable hN) (he.const_mul 6)
     fun xy => finePairDistanceFactor_square_absorption hN.le xy.1 xy.2
  rw [integral_const_mul] at hi
  exact hi.trans $ (mul_le_mul_of_nonneg_left (spatialPatchBox_pair_exponential_integral_le hd hN)
    𝖠₄ ).trans_eq 𝖢₃

𝗇 𝔉 𝙬
𝗇 𝔒 𝔜 η
𝗇 𝔔 𝖲
𝗇 𝔖 Fin 2 → Fin 3
def finePairCountTwoRawNumerator [NeZero d]
    (ad bd T0 N : ℝ) (D M q : ℕ) (C a V η : ℝ)
    (U : 𝖿₁) (p g w : 𝖷₂)
    (c : 𝔔) (y : 𝔖) : ℝ :=
  finePairThreeRowFirstAction ad bd T0 N D M q C U p c
    (fun v => 𝖨 𝔉 v y) -
    𝔒 * (p 0 * p 1) * ∑ i, 𝖩 *
      𝖷 𝔉 c y i

𝗇 𝔙 𝔒*d
theorem fine_pair_scalar_product_abs_le (η b L d w0 w1 p0 p1 m0 m1 : ℝ)
    (hb : 𝔞 b) (hL : 𝔞 L) (hd : 𝔞 d)
    (hw0 : |w0| ≤ 1) (hw1 : |w1| ≤ 1) (hp0 : |p0| ≤ b) (hp1 : |p1| ≤ b)
    (hm0 : |m0| ≤ L) (hm1 : |m1| ≤ L) :
    |𝔒 * w0 * w1 * p0 * p1 * d * m0 * m1| ≤ 𝔒 * 𝔜 b * 𝔜 L * d := by
  have hw : |w0*w1| ≤ 1 := by
    rw [abs_mul]
    bound
  have hp : |p0*p1| ≤ 𝔜 b := by
    rw [abs_mul, pow_two]
    bound
  have hm : |m0*m1| ≤ 𝔜 L := by
    rw [abs_mul, pow_two]
    bound
  have hprod := mul_le_mul (mul_le_mul hw hp (abs_nonneg _) 𝖠₄ ) hm
    (abs_nonneg _) 𝖠₃
  calc
    _ = 𝔙 * ( |w0*w1| * |p0*p1| * |m0*m1|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_sq, abs_of_nonneg hd]
      grind
    _ ≤ 𝔙 * ( 1*𝔜 b *𝔜 L) := mul_le_mul_of_nonneg_left hprod $ mul_nonneg (sq_nonneg η) hd
    𝘿 := 𝖢₃

𝗇 𝔑 𝗠/𝔜 a
𝗇 𝔄 𝔒 * 𝔜 bd * 𝔜 𝔑
𝗇 𝔇 𝙬₂
𝗇 𝔈 finePairDistanceFactor N (U 0) $ U 1
𝗇 𝔐 finePairDistanceFactor_nonneg (hT0.trans hN) ..
𝗃 𝔓 ἀ hF ad bd T0 N haD hab hT0 hN D M q hD hM hq C a V η
𝗇 𝔗 𝖳
𝗇 𝔘 𝖾₁
𝗇 𝔚 𝗡 𝔉 c i
theorem finePairCountTwoRawNumerator_abs_le [NeZero d] (hF : 3 ≤ F)
    ad bd T0 N (haD : 𝖼) (hab : 𝖽) (hT0 : 𝔞 T0) (hN : 𝖽₂)
    D M q (hD : 2 ≤ D) (hM : 𝗜₁) (hq : 𝖯₂)
    C a V η ρ (hC : 𝚆) (ha : 𝙆) (hρ : 𝔞 ρ)
    U (hU : 𝔘)
    p g w (hp : 𝔗) (hw : ∀ i, |w i| ≤ 1)
    (c : 𝔔)
    (hf : ∀ i, |𝔚| ≤ ρ)
    y :
    |𝔇| ≤
      𝔄 * 𝔈 := by
  unfold finePairCountTwoRawNumerator
  rw [𝔓 finePairThreeRow_count_two_numerator hC U hU p hp g w c y]
  exact fine_pair_scalar_product_abs_le η bd 𝔑 𝔈
    _ _ _ _ _ _ (haD.trans hab).le  𝖠₃ 
    𝔐 (hw 0) (hw 1)
     𝖤₃ 
     𝖤₃ 
    (𝗥₁ (hf 0) $ y 0 )
    $ 𝗥₁ (hf 1) $ y 1

theorem finePairCountTwoRawNumerator_sum_square_le [NeZero d] (hF : 3 ≤ F)
    ad bd T0 N (haD : 𝖼) (hab : 𝖽) (hT0 : 𝔞 T0) (hN : 𝖽₂)
    D M q (hD : 2 ≤ D) (hM : 𝗜₁) (hq : 𝖯₂)
    C a V η ρ (hC : 𝚆) (ha : 𝙆) (hρ : 𝔞 ρ)
    U (hU : 𝔘)
    p g w (hp : 𝔗) (hw : ∀ i, |w i| ≤ 1)
    (c : 𝔔)
    (hf : ∀ i, |𝔚| ≤ ρ) :
     ∑ y : 𝔖,
      𝔜 𝔇 ≤
      9 * 𝔜 𝔄 * 𝔜 𝔈 := by
  have hy (y : 𝔖) :
      𝔜 𝔇 ≤
      (𝔄 * 𝔈)^2 := by
    have h := 𝔓 finePairCountTwoRawNumerator_abs_le ρ hC ha hρ U hU p g w hp hw c hf y
    simpa only [sq_abs] using (𝘉 $ mul_nonneg  𝖠₃  𝔐 ).mpr h
  exact (Finset.sum_le_sum 𝘖₂).trans_eq $ by simp; ring
