module

public import NearlyMinimax.SourceActivitySummation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Total activity of the actual finite source family, including singleton,
three genuine pair rows, and every selected higher target. -/
𝚫
𝚨
𝚩
𝚱

𝗇 𝔄 exteriorTau 𝖬
theorem source_exteriorTau_nonneg (ha : 𝙆) (hab : 𝙭) :
    0 ≤ 𝔄 := by
  apply exteriorTau_nonneg
  apply (le_div_iff₀ $ sub_pos.mpr hab ).mpr
  linarith

𝗇 𝔇 𝘚₂
𝗇 𝔈 Real.one_le_exp $ 𝚍₁ $ source_exteriorTau_nonneg ha hab
𝗃 𝔣 ἀ d k D M q
𝗇 𝔍 highRowTotalMass (𝔣 finePairRowData a b C ℓ N).rowMass
𝗇 𝔎 sourceResponseCost_nonneg q C
𝗇 𝔖 sourceResponseCost q C
𝗇 𝔡 ordinaryDensityActivityBase a b
𝗇 𝔏 𝔡^2 * 𝔖
𝗇 𝔠 finePairRowMass d D M q a b C ℓ N
𝗇 𝔐 𝔠 .unit
𝗇 𝔑 𝔠 .coarse
𝗇 𝔓 𝘔*Real.exp (D*𝔄)
𝗇 𝔙 128*d*K
𝗇 𝔚 𝔓*ℓ^2
𝗇 𝔛 2*𝔇
𝗇 𝔜 M*𝔄
𝗇 𝔞 256*d*K*𝔇
𝗃 𝔢 ἀ d D M q hD a b ha hab C ℓ N
theorem finePairTotalMass_activity_bound (d : ℕ) [NeZero d] (k D M q : ℕ) (hD : 𝗮)
    a b C ℓ N (ha : 𝙆) (hab : 𝙭) (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N)
    (hunit : 𝔓 ≤ 𝔇)
    (hcoarse : 𝔚 ≤ 𝔛) :
    𝔍 ≤
      𝔏 * (1+512*d) *
        𝔇 * Real.exp 𝔜 := by
  let K := 𝔏
  let EM := Real.exp 𝔜
  have hK : 𝖭₂ := 𝖧₁ 𝔎
  have hEM : 1 ≤ EM := 𝔈
  have hu : 𝔐 ≤ K*𝔇 := by
    apply (𝔢 finePairRowMass_unit_le).trans
    nlinarith
  have hc : 𝔑 ≤ 𝔞 := by
    apply (𝔢 finePairRowMass_coarse_le hℓ).trans
    calc
      _ = 𝔙*𝔚 := 𝖢₃
      _ ≤ 𝔙*𝔛 := mul_le_mul_of_nonneg_left hcoarse 𝖠₃
      𝘿 := 𝖢₃
  have hf := finePairRowMass_fine_le d D M q a b ha hab C ℓ N hℓ hℓN
  have hu' : 𝔐 ≤ K*𝔇*EM := by
    apply hu.trans
    bound
  have hc' : 𝔑 ≤ 𝔞*EM := by
    apply hc.trans
    bound
  have he : (Finset.univ : Finset FinePairRowTag) = {.unit, .coarse, .fine} := by
    rfl
  change ∑ i, 𝔠 i ≤ _
  grind

𝗇 𝔊 B^2 * 𝔖 * (1+512*𝙊)
𝗇 𝔒 higherBandInterpolationBase d lam
def sourceActivityConstant (d q : ℕ) (C B lam : ℝ) : ℝ :=
  𝔊 + B * 𝔖 +
    4 * higherBandGeometricPrefactor B 𝔒 𝔖

theorem sourceActivityConstant_nonneg d q C B lam (hB : 𝙐) :
    0 ≤ sourceActivityConstant d q C B lam := by
  unfold sourceActivityConstant higherBandGeometricPrefactor higherBandInterpolationBase sourceResponseCost
  positivity

𝗇 𝔅 𝚝₁
𝗇 𝔉 𝘵
𝗇 𝔔 Real.exp $ 𝔅*𝔄
𝗇 𝔗 𝖧*𝔄
𝗇 𝔘 higherBandGeometricRatio d D (higherBandGeometricConstant B 𝔒) 𝔉 $ μ*𝔉
𝗇 𝔟 𝔅^2
/-- The actual complete finite row family has a fixed total activity constant.
The hypotheses are elementary inequalities on the computed source scales. -/
theorem sourceRows_activity_bound [NeZero d] (hd : 𝗆) (hD : 𝗮)
    (a b C lam ℓ N μ B q1 q2 : ℝ) (ha : 𝙆) (hab : 𝙭)
    (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N) (hN : 𝗭₁) (hμ : 0 ≤ μ) (hbase1 : μ*𝔉 ≤ 1)
    (hB : 𝙐) (hbB : 𝔡 ≤ B)
    (hq1 : q1 = 𝔘 1)
    (hq2 : q2 = 𝔘 2)
    (hq1h : q1 ≤ 𝙖) (hq21 : q2 ≤ q1) (hsmall : 𝔟*q1 ≤ 1)
    (hcoarse : 𝔔*ℓ ≤ N)
    (hsingle : 𝔅*𝔔 ≤ N)
    (hpair : 𝔟*𝔔*ℓ^2 ≤ 𝔛) :
    highRowTotalMass (𝔣 sourceRowData a b C lam ℓ N μ).rowMass ≤
      sourceActivityConstant d q C B lam * 𝔇 * Real.exp 𝔗 := by
  let A := 𝔡
  let EM := Real.exp 𝔗
  let ED := 𝔔
  have hA : 𝖲₁ := by dsimp [A, ordinaryDensityActivityBase]; positivity
  have hED : 1 ≤ ED := 𝔈
  have hEM : 1 ≤ EM := 𝔈
  have hunit : 𝔟*ED ≤ 𝔇 := by
    have h1 := mul_le_mul_of_nonneg_left hED (by positivity : 0 ≤ 𝔟*ED)
    have h2 := pow_le_pow_left₀  𝖠₃  hsingle 2
    nlinarith only [h1, h2]
  have hp := 𝔣 finePairTotalMass_activity_bound hD a b C ℓ N ha hab hℓ hℓN hunit hpair
  have hbpow := pow_le_pow_left₀ hA hbB 2
  have hp' : 𝔍 ≤
      𝔊*𝔇*EM := by
    apply hp.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbpow 𝔎)
        𝖠₃ ) $ sq_nonneg N ) 𝙫
  have hs := singletonRowMass_exponential_bound d D q hD a b ha hab C
  have hs' : singletonRowMass d D q a b C ≤ B*𝔖*𝔇*EM := by
    apply hs.trans
    have h1 := mul_le_mul hbB hsingle  𝖠₃  hB
    have h2 := mul_le_mul_of_nonneg_right h1 𝔎
    have hN2 : N ≤ 𝔇*EM := by
      have hsq : N ≤ 𝔇 := 𝖥₃
      apply hsq.trans
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hEM $ sq_nonneg N
    have h3 := mul_le_mul_of_nonneg_left hN2 $ mul_nonneg hB 𝔎
    dsimp [A, ED, ordinaryDensityActivityBase, sourceResponseCost] at h2
    dsimp [sourceResponseCost] at h3
    dsimp [ordinaryDensityActivityBase, sourceResponseCost] at hs ⊢
    nlinarith only [h2, h3]
  have hh := higherBandFamily_activity_bound (k := k) (M := M) (q := q) hd hD
    a b C lam ℓ N μ B q1 q2 ha hab hℓ hN hμ hbase1 hB hbB hq1 hq2 hq1h hq21 hsmall hcoarse
  rw [sourceRowTotalMass_eq]
  dsimp [sourceActivityConstant]
  nlinarith only [hp', hs', hh]
