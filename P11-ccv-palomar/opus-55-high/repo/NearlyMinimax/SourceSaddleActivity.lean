module

public import NearlyMinimax.SourceShrunkActivity
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Eventual total activity of the actual complete row family at the
paper's rounded canonical saddle parameters. -/
𝛊
open scoped BigOperators Topology
𝚨
𝚩
𝚭

𝗇 𝔈 𝘦₂
𝗃 𝔖 ἀ+1
𝗇 𝔏 uniformOrdinaryDensityActivityBase a b 𝔖 𝔈
def sourceSaddleActivityConstant (d q : ℕ) (a b C lam : ℝ) : ℝ :=
  1 + sourceActivityConstant d q C
    𝔏 lam

𝗇 𝔒 sourceSaddleActivityConstant d q a b C lam
theorem sourceSaddleActivityConstant_positive d q a b C lam
    (ha : 𝙆) (hab : 𝙭) : 0 < 𝔒 := by
  have hB : 0 ≤ 𝔏 := by
    unfold uniformOrdinaryDensityActivityBase
    positivity
  have h := sourceActivityConstant_nonneg d q C _ lam hB
  unfold sourceSaddleActivityConstant
  linarith

𝗃 𝔗 (ἀ : ℝ)
𝗇 𝔄 𝔗 d
𝗇 𝔅 𝙉₂
𝗇 𝔇 𝔗 M⁻¹
𝗃 𝔐 ἀ s 𝔄 m theta shift
def sourceSaddleTotalMass (d k q : ℕ) (s a b C lam shift x : ℝ) : ℝ :=
  let tau := 𝔈
  let m := lowerSaddleCoefficient s 𝔄 tau
  let theta := lowerSaddleTheta s 𝔄 tau
  let M := 𝗫
  let D := lowerSaddleD 𝔄 m x
  let N := 𝔐 lowerSaddleN 𝔅 x
  let mu := lowerSaddleMu 𝔄 m theta shift x
  let ell := 𝔐 lowerAliasCutoff 𝔖 tau 𝔅 x
  highRowTotalMass (𝙴₂ (a+𝔇) (b-𝔇) C lam ell N mu).rowMass

𝗇 𝔉 𝔗 D
𝗇 𝔊 higherBandSourceCact d a b c0 lam
𝗇 𝔍 eventually_ge_atTop 𝙠
𝗇 𝔎 lowerSaddleCoefficient s 𝔄 𝔈
𝗇 𝔑 𝙋
𝗇 𝔓 𝘅/2
𝗇 𝔔 c0*𝔉
/-- A fixed positive constant bounds the entire actual row activity for
all sufficiently large sample scales and every spatial grid. No activity,
row-budget, density-neighborhood, or selected-target hypothesis is assumed. -/
theorem sourceSaddleTotalMass_eventually_bound (d q : ℕ) [NeZero d]
    (s a b C lam shift : ℝ) (hs : 𝚊₁) (hd : 𝚄 < 𝔄)
    (ha : 𝙆) (hab : 𝙭) :
    ∀ᶠ x in atTop, ∀ k : ℕ,
      sourceSaddleTotalMass d k q s a b C lam shift x ≤
        𝔒 *
           lowerSaddleN s 𝔄 𝔎
            (lowerSaddleTheta s 𝔄 𝔈) shift 𝔅 x ^2 *
          Real.exp (𝔅 (lowerSaddleM 𝔎 x)*
            (lowerSaddleM 𝔎 x : ℝ)) := by
  let tau := 𝔈
  let c0 := 𝔖 tau
  let m := lowerSaddleCoefficient s 𝔄 tau
  let theta := lowerSaddleTheta s 𝔄 tau
  have hτ : 0 < tau := densityIntervalExponent_pos ha hab
  have hc0 : 1 ≤ c0 := by dsimp [c0]; linarith
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd hτ
  have hdR : 𝔑 < d := 𝖡₄
  have hdNat : 𝗆 := by exact_mod_cast hdR
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hhier := actual_lowerAlias_hierarchy (Cact := 𝔊)
    (Cs := 1) hs hd ha hab (higherBandSourceCact_positive d ha hab)  𝖠₄  shift
  have hM := lowerSaddleM_tendsto_atTop hm
  have hN := lowerSaddleN_tendsto_atTop hs hd hm (lowerSaddleTheta_pos hs hd hτ) hcontrol shift
  have hsmall := hM.inv_tendsto_atTop.eventually $ gt_mem_nhds (by linarith : 𝔑 < 𝔓)
  filter_upwards [hhier, hsmall, hM.eventually 𝔍,
    hN.eventually 𝔍, eventually_gt_atTop 𝔑] with x hx hsh hMx hNx hxp
  intro k
  let M := 𝗫
  let D := lowerSaddleD 𝔄 m x
  let N := 𝔐 lowerSaddleN 𝔅 x
  let mu := lowerSaddleMu 𝔄 m theta shift x
  let ell := 𝔐 lowerAliasCutoff c0 𝔅 x
  rcases hx with ⟨hell, htau, hbase, _, _, hq21, hq1, hDq, _, hsingle, _, _⟩
  have hD : 𝗮 := by
    have hc : (𝔄+8)/4*𝔗 M ≤ 𝔉 := Nat.le_ceil _
    have hh : 𝙠 ≤ D := 𝖥₃
    exact_mod_cast hh
  have hmu : 0 ≤ mu := by
    dsimp [mu]
    rw [lowerSaddleMu_eq_exp hxp]
    exact 𝙫
  have hshrink : a+𝔇 < b-𝔇 := by
    change 𝔇 < 𝔓 at hsh
    linarith
  have hDN : 𝔉*Real.exp 𝔔 ≤ N := by
    have he : Real.exp 𝔔 ≤ Real.exp (c0*𝔖 𝔉) := Real.exp_le_exp.mpr 𝖥₃
    have hh := mul_le_mul_of_nonneg_left he $ Nat.cast_nonneg D
    apply hh.trans
    simpa only [one_mul] using hsingle
  have hb := sourceRows_shrunk_activity_bound (k := k) (M := M) (q := q) hdNat hD
    a b C lam N mu c0
    (𝔐 lowerAliasQ 𝔊 1 𝔅 x)
    (𝔐 lowerAliasQ 𝔊 2 𝔅 x)
    ha hshrink htau hc0 hNx hmu hbase hDN rfl rfl hq1 hq21 hDq
  apply hb.trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by unfold sourceSaddleActivityConstant; dsimp [c0, tau]; linarith) $ sq_nonneg N ) 𝙫
