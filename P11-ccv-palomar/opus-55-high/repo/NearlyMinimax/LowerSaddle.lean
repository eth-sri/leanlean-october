module

public import NearlyMinimax.Rates
public import NearlyMinimax.SaddleAsymptotics
public import NearlyMinimax.LowerEndpoint
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
# The actual lower saddle allocation

This file constructs and analyzes the scalar parameters of `lem:saddle` in
`sections/lower_fisher.tex`. Natural ceilings are used for the polynomial
degree and the spatial grid. The statements in this file are deterministic
numeric allocation results; they do not postulate the local score construction
or its statistical energy estimate.
-/

𝚷
𝚶

𝚨

𝗃 𝕺 ἀ $ Real.log x
𝗇 𝔦 m * 𝕺 Real.sqrt
def lowerSaddleM (m x : ℝ) : ℕ := Nat.ceil 𝔦

𝗇 𝔅 𝗫
𝗇 𝔓 𝙶
𝗃 𝕵₁ ἀ * 𝔅
𝗇 𝖅 𝕵₁ 𝔓
def lowerSaddleD (d m x : ℝ) : ℕ := Nat.ceil 𝖅

def lowerSaddleOmegaZero (m θ C x : ℝ) : ℝ :=
  𝕵₁ θ - Real.log 𝔅 + C

𝗇 𝔫 lowerSaddleOmegaZero m θ C x
𝗇 𝔐₁ Real.log x + 𝔫
𝗃 𝕶₁ ἀ / d
def lowerSaddleGridBase (d m θ C x : ℝ) : ℝ :=
  Real.exp 𝕶₁ 𝔐₁

𝗃 𝕯 ἀ d m θ C
𝗇 𝔐 𝕯 lowerSaddleGridBase x
def lowerSaddleGrid (d m θ C x : ℝ) : ℕ := Nat.ceil 𝔐

𝗇 𝔒 𝕯 lowerSaddleGrid x
𝗃 𝕲 (ἀ : ℝ)
def lowerSaddleH (d m θ C x : ℝ) : ℝ := 𝕲 𝔒⁻¹

𝗇 𝔖 𝕯 lowerSaddleH x
𝗇 𝔒₁ 𝔖 ^ d
def lowerSaddleMu (d m θ C x : ℝ) : ℝ := x * 𝔒₁

𝗇 𝖜 d * Real.log 𝔒 - Real.log x
def lowerSaddleOmega (d m θ C x : ℝ) : ℝ :=
  𝖜

𝗃 𝔬₁ ἀ + 1
theorem lowerSaddleM_rounding (hm : 0 ≤ m) :
    𝔦 ≤ 𝔅 ∧
      𝔅 < 𝔬₁ 𝔦 := ⟨Nat.le_ceil _, Nat.ceil_lt_add_one $ mul_nonneg hm $ Real.sqrt_nonneg _ ⟩

𝗃 𝕬 0 < ἀ
𝗇 𝔑 𝕬 m
𝗃 𝕯₁ Tendsto (fun x => 𝕲 ἀ) atTop atTop
theorem lowerSaddleM_tendsto_atTop (hm : 𝔑) :
    𝕯₁ 𝔅 := by
  apply tendsto_atTop_mono fun x => (lowerSaddleM_rounding hm.le).1
  exact tendsto_sqrt_log_atTop.const_mul_atTop hm

𝗇 𝖂 (Real.sqrt_pos.2 $ Real.log_pos hx ).ne'
𝗇 𝖆 lowerSaddleM_rounding (x := x) hm.le
𝗇 𝖙 sub_nonneg.2 (lowerSaddleM_rounding hm.le).1
𝗇 𝖝 𝔅 - 𝔦
𝗃 𝔫₁ tendsto_const_nhds (x := ἀ)
𝗃 𝔳₁ fun x => ἀ / 𝕺 Real.sqrt
theorem lowerSaddleM_div_sqrt_log_limit (hm : 𝔑) :
    Tendsto 𝔳₁ 𝔅
      atTop $ 𝓝 m := by
  have herr : Tendsto 𝔳₁ 𝖝 atTop $ 𝓝 0 := by
    have hu : Tendsto (fun x => 1 / 𝕺 Real.sqrt) atTop $ 𝓝 0 := by
      simpa only [one_div] using! tendsto_sqrt_log_atTop.inv_tendsto_atTop
    apply squeeze_zero' _ _ hu
    · filter_upwards [eventually_gt_atTop 1] with x hx
      exact div_nonneg 𝖙 $ Real.sqrt_nonneg _
    · filter_upwards [eventually_gt_atTop 1] with x hx
      exact div_le_div_of_nonneg_right (by linarith [(𝖆).2])
        $ Real.sqrt_nonneg _
  have hh := (𝔫₁ m).add herr
  simp at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hz := 𝖂
  field_simp
  ring

𝗃 𝔱₁ ἀ ^ 2
𝗇 𝔡 𝔱₁ m
𝗇 𝖇 𝔱₁ 𝔅
𝗃 𝔴₁ fun x => ἀ / Real.log x
theorem lowerSaddleM_sq_div_log_limit (hm : 𝔑) :
    Tendsto 𝔴₁ 𝖇 atTop $ 𝓝 𝔡 := by
  have hh := (lowerSaddleM_div_sqrt_log_limit hm).pow 2
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp only [div_pow, Real.sq_sqrt (Real.log_pos hx).le]

𝗃 𝕴₁ ἀ $ eventually_gt_atTop 0
𝗇 𝔛 𝕴₁ 𝘂₂
𝗇 𝖞 Real.log 𝔅 - 𝕺 Real.log / 2
𝗃 𝔪₁ fun x => ἀ
theorem log_lowerSaddleM_residual_limit (hm : 𝔑) :
    Tendsto 𝔪₁ 𝖞
      atTop $ 𝓝 $ Real.log m := by
  have hh := (Real.continuousAt_log hm.ne').tendsto.comp $ lowerSaddleM_div_sqrt_log_limit hm
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 1,
    𝔛] with x hx hM
  simp
  rw [Real.log_div hM.ne' 𝖂,
    Real.log_sqrt (Real.log_pos hx).le]

𝗇 𝔴 𝕴₁ ht.eventually
𝗃 𝕶 Tendsto (fun x => ἀ / 𝔅) atTop
theorem lowerSaddleOmegaZero_div_M_limit (hm : 𝔑) θ C :
    𝕶 𝔫 $ 𝓝 θ := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hc : 𝕶 C $ 𝓝 0 := by
    simpa [div_eq_mul_inv] using ht.inv_tendsto_atTop.const_mul C
  have hh := ((𝔫₁ θ).sub $ Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht ).add hc
  simp only [sub_zero, add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [𝔴] with x hx
  simp
  unfold lowerSaddleOmegaZero
  field_simp

𝗇 𝔚 𝕬 θ
theorem lowerSaddleOmegaZero_tendsto_atTop (hm : 𝔑) (hθ : 𝔚) C :
    Tendsto (lowerSaddleOmegaZero m θ C) atTop atTop := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hh := ht.atTop_mul_pos hθ $ lowerSaddleOmegaZero_div_M_limit hm θ C
  refine hh.congr' ?_
  filter_upwards [𝔴] with x hx
  field_simp

theorem lowerSaddleGrid_positive d m θ C x : 0 < 𝕲 𝔒 := by
  exact (Real.exp_pos _).trans_le $ Nat.le_ceil 𝔐

𝗇 𝔮 𝕯 lowerSaddleGrid_positive x
theorem lowerSaddleH_positive d m θ C x : 𝕬 𝔖 :=
  inv_pos.2 𝔮

𝗇 𝔔 𝕬 d
theorem lowerSaddleGridBase_tendsto_atTop
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) C :
    Tendsto 𝕯 lowerSaddleGridBase atTop atTop := Real.tendsto_exp_atTop.comp
    $ (Real.tendsto_log_atTop.atTop_add_atTop $ lowerSaddleOmegaZero_tendsto_atTop hm hθ C ).atTop_div_const hd

𝗃 𝕰₁ ἀ hd hm hθ
𝗃 𝕮 𝕰₁ ἀ C
theorem lowerSaddleGrid_tendsto_atTop
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) C :
    𝕯₁ 𝔒 := by
  apply tendsto_atTop_mono fun x => Nat.le_ceil _
  exact 𝕮 lowerSaddleGridBase_tendsto_atTop

𝗇 𝖈 (Real.exp_pos _).ne'
𝗇 𝖑 𝙫
𝗇 𝖟 sub_nonneg.2 $ Nat.le_ceil _
𝗇 𝔄₁ (tendsto_const_nhds (x := 1)).add
𝗃 𝔰₁ 1 / ἀ
theorem lowerSaddleGrid_div_base_limit
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) C :
    Tendsto (fun x => 𝔒 / 𝔐)
      atTop $ 𝓝 1 := by
  have hb := 𝕮 lowerSaddleGridBase_tendsto_atTop
  have herr : Tendsto (fun x =>
      (𝔒 - 𝔐) /
        𝔐) atTop $ 𝓝 0 := by
    have hu : Tendsto (fun x => 𝔰₁ 𝔐) atTop $ 𝓝 0 := by
      simpa only [one_div] using! hb.inv_tendsto_atTop
    apply squeeze_zero' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_) hu
    · exact div_nonneg 𝖟 𝖑
    · apply div_le_div_of_nonneg_right _ 𝖑
      have hh := Nat.ceil_lt_add_one $ show 0 ≤ 𝔐 from 𝖑
      change 𝔒 < 𝔬₁ 𝔐 at hh
      linarith
  have hh := 𝔄₁ herr
  simp at hh
  refine hh.congr fun x => ?_
  have hp : 𝔐 ≠ 0 := 𝖈
  field_simp
  ring

𝗇 𝔏 𝕯 lowerSaddleOmega x
theorem lowerSaddleOmega_rounding_limit
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) C :
    Tendsto (fun x => 𝔏 - 𝔫)
      atTop $ 𝓝 0 := by
  have hh := ((Real.continuousAt_log 𝖠₄ ).tendsto.comp
    𝕮 lowerSaddleGrid_div_base_limit).const_mul d
  simp only [Real.log_one, mul_zero] at hh
  refine hh.congr fun x => ?_
  simp
  rw [Real.log_div (𝔮).ne'
    $ show 𝔐 ≠ 0 from 𝖈 ]
  unfold lowerSaddleGridBase lowerSaddleOmega
  rw [Real.log_exp]
  field_simp
  ring

𝗃 𝕵 2 * ἀ
theorem lowerSaddleOmega_rounding_bounds (hd : 𝔔)
    (hb : 1 ≤ 𝔐) :
    𝔫 ≤ 𝔏 ∧
      𝔏 ≤ 𝔫 + d * Real.log 2 := by
  have hpos : 𝕬 𝔐 := Real.exp_pos _
  have hlow := Real.log_le_log hpos $ Nat.le_ceil 𝔐
  change Real.log 𝔐 ≤
    Real.log 𝔒 at hlow
  have hceil : 𝔒 ≤ 𝕵 𝔐 := by
    have hh := Nat.ceil_lt_add_one hpos.le
    change 𝔒 < 𝔬₁ 𝔐 at hh
    linarith
  have hhigh := Real.log_le_log 𝔮 hceil
  rw [Real.log_mul  𝖠₄  hpos.ne'] at hhigh
  unfold lowerSaddleGridBase at hlow hhigh
  rw [Real.log_exp] at hlow hhigh
  unfold lowerSaddleOmega
  constructor <;> nlinarith [mul_div_cancel₀
      𝔐₁ hd.ne']

𝗇 𝔉 𝕯 lowerSaddleH_positive x
𝗇 𝔠 𝕯 lowerSaddleMu x
theorem lowerSaddleMu_eq_exp (hx : 𝕬 x) :
    𝔠 = Real.exp (-𝔏) := by
  unfold lowerSaddleMu
  calc
    _ = 𝕺 Real.exp * Real.exp (Real.log 𝔖 * d) := by
      rw [Real.exp_log hx, Real.rpow_def_of_pos 𝔉]
    _ = Real.exp (Real.log x + Real.log 𝔖 * d) := (Real.exp_add ..).symm
    𝘿 := by
      unfold lowerSaddleH lowerSaddleOmega
      rw [Real.log_inv]
      ring

𝗃 𝔵₁ -(Real.log x + ἀ) / d
theorem lowerSaddleH_eq_exp (hd : 𝚙₂) :
    𝔖 =
      Real.exp 𝔵₁ 𝔏 := by
  unfold lowerSaddleH lowerSaddleOmega
  have hh : 𝔵₁ 𝖜 =
      -Real.log 𝔒 := by field_simp; ring
  rw [hh, Real.exp_neg, Real.exp_log 𝔮]

theorem lowerSaddleOmega_div_M_limit
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) C :
    𝕶 𝔏 $ 𝓝 θ := by
  have hr := (𝕮 lowerSaddleOmega_rounding_limit).mul
    (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop
  have hh := (lowerSaddleOmegaZero_div_M_limit hm θ C).add hr
  simp at hh
  grind

𝗇 𝔬 𝕮 lowerSaddleOmega_div_M_limit
theorem lowerSaddleOmega_tendsto_atTop
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) C :
    Tendsto 𝕯 lowerSaddleOmega atTop atTop := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hh := ht.atTop_mul_pos hθ 𝔬
  refine hh.congr' ?_
  filter_upwards [𝔴] with x hx
  field_simp

𝗃 𝕴 Tendsto 𝔴₁ ἀ atTop
theorem lowerSaddleM_div_log_limit (hm : 𝔑) :
    𝕴 𝔅 $ 𝓝 0 := by
  have hh := (lowerSaddleM_div_sqrt_log_limit hm).mul tendsto_sqrt_log_div_log
  simp at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hz := 𝖂
  field_simp

theorem lowerSaddleOmega_div_log_limit
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) C :
    𝕴 𝔏 $ 𝓝 0 := by
  have hh := (𝔬).mul $ lowerSaddleM_div_log_limit hm
  simp at hh
  refine hh.congr' ?_
  filter_upwards [𝔛] with x hx
  field_simp

𝗇 𝔲 𝙜
𝗃 𝕹 ἀ s d
/-- `τM` denotes the interval exponent evaluated at the actual natural degree. -/
def lowerSaddleN (s d m θ C : ℝ) (τM : 𝔲) (x : ℝ) : ℝ :=
  Real.exp $ 𝕹 lowerSaddleLogN (Real.log x) 𝔏
    (τM 𝔅) 𝔅

def lowerSaddleEta (s d m θ C cf x : ℝ) : ℝ := cf * 𝔖 ^ s

𝗃 𝔷 ἀ s d m θ C
𝗃 𝔲₁ 𝔷 ἀ τM x
𝗇 𝔊 𝔲₁ lowerSaddleN
def lowerSaddleActivity (s d m θ C : ℝ) (τM : 𝔲) (x : ℝ) : ℝ :=
  𝔱₁ 𝔊 * Real.exp (τM 𝔅 * 𝔅)

𝗇 𝔜 𝔷 lowerSaddleEta cf x
𝗇 𝔡₁ 𝔲₁ lowerSaddleActivity
def lowerSaddleRisk (s d m θ C cf : ℝ) (τM : 𝔲) (x : ℝ) : ℝ :=
  𝔱₁ 𝔜 / 𝔡₁

𝗃 𝕷 4 * ἀ
𝗇 𝔎 𝕷 s
𝗇 𝖉 𝗟
def lowerSaddleEnergyOne (s d m θ C : ℝ) (τM : 𝔲) (x : ℝ) : ℝ :=
  x ^ 𝖉 * 𝔖 ^ (d + 𝔎) *
    𝔊 ^ (-d)

𝗃 𝕰 (𝔬₁ ἀ).factorial
𝗇 𝔓₁ CG * 𝔠
𝗃 𝔭₁ (𝕰 ἀ : ℝ)
def lowerSaddleEnergyTwo (s d m θ C CG : ℝ) (τM : 𝔲) (x : ℝ) : ℝ :=
  x * 𝔖 ^ 𝔎 *
    Real.exp (2 * τM 𝔅 * 𝔅) *
    𝔊 ^ 𝚜₂ *
    𝔓₁ ^ 𝔅 /
      𝔭₁ 𝔅

𝗇 𝔈 𝔱₁ 𝔡₁
𝗇 𝔥 𝙵
def lowerSaddleEnergyThree (s d m θ C CG : ℝ) (τM : 𝔲) (x : ℝ) : ℝ :=
  x * 𝔖 ^ 𝔎 *
    𝔈 *
    𝔓₁ ^ 𝔥 /
      𝔭₁ 𝔥

theorem lowerSaddleN_positive s d m θ C τM x :
    𝕬 𝔊 := Real.exp_pos _

𝗇 𝔙 𝔲₁ lowerSaddleN_positive
theorem lowerSaddleActivity_positive s d m θ C τM x :
    0 < 𝔡₁ := mul_pos (sq_pos_of_pos 𝔙) $ Real.exp_pos _

𝗇 𝔍 𝙾₁
𝗃 𝕱₁ ἀ * Real.log x
theorem lowerSaddleEnergyOne_eq_activity_sq
    (hd : 𝔔) (hd4 : 𝔍 ≠ 0) (hx : 𝕬 x) τM :
    𝔲₁ lowerSaddleEnergyOne = 𝔈 := by
  have hx2 : 𝔱₁ x = Real.exp (2 * Real.log x) := by
    change 𝔱₁ x = Real.exp 𝕱₁ 𝖉
    rw [Real.exp_nat_mul, Real.exp_log hx]
  unfold lowerSaddleEnergyOne lowerSaddleActivity lowerSaddleN
  rw [hx2, Real.rpow_def_of_pos 𝔉,
    Real.rpow_def_of_pos $ Real.exp_pos _ , mul_pow]
  simp only [Real.log_exp, ← Real.exp_nat_mul, ← Real.exp_add]
  rw [lowerSaddleH_eq_exp hd.ne', Real.log_exp]
  unfold lowerSaddleLogN
  field_simp
  ring

/-- The fixed endpoint estimate `τ≤τ_M≤τ+Cτ/M`, expressed without division. -/
def LowerExponentControl (τM : 𝔲) (τ Cτ : ℝ) : Prop :=
  ∀ᶠ M : ℕ in atTop, τ ≤ τM M ∧ (τM M - τ) * 𝕲 M ≤ Cτ

𝗃 𝔶₁ ἀ $ lowerSaddleM_tendsto_atTop hm
theorem lowerSaddleM_nat_tendsto_atTop (hm : 𝔑) :
    Tendsto (lowerSaddleM m) atTop atTop :=
  𝔶₁ tendsto_natCast_atTop_iff.1

𝗇 𝔩 LowerExponentControl τM τ Cτ
𝗇 𝖒 τM 𝔅 - τ
𝗇 𝔅₁ (lowerSaddleM_nat_tendsto_atTop hm).eventually
𝗃 𝔯₁ Tendsto 𝔪₁ ἀ atTop $ 𝓝 0
theorem lowerSaddleTau_limit
    (hm : 𝔑) (hcontrol : 𝔩) :
    Tendsto (fun x => τM 𝔅) atTop $ 𝓝 τ := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have he := 𝔅₁ hcontrol
  have hu : 𝕶 Cτ $ 𝓝 0 := by
    simpa [div_eq_mul_inv] using! ht.inv_tendsto_atTop.const_mul Cτ
  have hh : 𝔯₁ 𝖒 := by
    apply squeeze_zero' (he.mono fun x hx => sub_nonneg.2 hx.1) _ hu
    filter_upwards [he, 𝔴] with x hx hM
    exact (le_div_iff₀ hM).2 hx.2
  have h := hh.add_const τ
  simp_all

𝗇 𝔠₁ d * 𝙾₁
𝗇 𝔄 (d - 𝕷 s) / 𝔠₁
𝗇 𝔯 (Real.log_pos hx).ne'
𝗇 𝔔₁ Real.log 𝔊 / Real.log x
𝗇 𝔖₁ d - 𝔎
𝗇 𝔦₁ 𝕶₁ 𝔎
theorem lowerSaddleLogN_div_log_limit
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚)
    (hcontrol : 𝔩) s C :
    Tendsto 𝔪₁ 𝔔₁
      atTop $ 𝓝 𝔄 := by
  have hcost := (lowerSaddleTau_limit hm hcontrol).mul $ lowerSaddleM_div_log_limit hm
  have hh := (((tendsto_const_nhds (x := 𝕶₁ 𝔖₁)).sub $ (𝕮 lowerSaddleOmega_div_log_limit).const_mul $ 1 + 𝔦₁ ).sub
    $ hcost.const_mul 2 ).div_const 𝔍
  simp at hh
  rw [ div_div .. ] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  unfold lowerSaddleN lowerSaddleLogN
  rw [Real.log_exp]
  field_simp [𝔯]

𝗇 𝔗₁ 𝔄 / 𝔡
𝗃 𝔷₁ pow_ne_zero 2 ἀ
theorem lowerSaddleLogN_div_M_sq_limit
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚)
    (hcontrol : 𝔩) s C :
    Tendsto (fun x => Real.log 𝔊 / 𝖇)
      atTop $ 𝓝 𝔗₁ := by
  have hh := (𝕰₁ lowerSaddleLogN_div_log_limit hcontrol s C).div
    (lowerSaddleM_sq_div_log_limit hm) 𝔷₁ hm.ne'
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  change 𝔔₁ /
    (𝖇 / Real.log x) =
      Real.log 𝔊 / 𝖇
  field_simp [𝔯]

𝗇 𝔧 𝚊₁
𝗇 𝕽 𝔎 < d
𝗃 𝔮₁ ἀ hd0 hm hθ
𝗇 𝔇₁ 𝔮₁ lowerSaddleLogN_div_log_limit hcontrol s C
theorem lowerSaddleN_tendsto_atTop
    (hs : 𝔧) (hd : 𝕽) (hm : 𝔑) (hθ : 𝔚)
    (hcontrol : 𝔩) C :
    Tendsto (𝔷 lowerSaddleN τM) atTop atTop := by
  have hd0 : 𝔔 := 𝖡₄
  have hh := Real.tendsto_log_atTop.atTop_mul_pos  𝖠₃ 
    𝔇₁
  have ht : Tendsto (fun x => Real.log 𝔊) atTop atTop := by
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact mul_div_cancel₀ _ 𝔯
  have h := Real.tendsto_exp_atTop.comp ht
  exact h.congr fun x => Real.exp_log 𝔙

theorem lowerSaddleMu_tends_zero
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) C :
    Tendsto 𝕯 lowerSaddleMu atTop $ 𝓝 0 := by
  have hh := Real.tendsto_exp_atBot.comp
    $ tendsto_neg_atTop_atBot.comp 𝕮 lowerSaddleOmega_tendsto_atTop
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  exact (lowerSaddleMu_eq_exp hx).symm

theorem lowerSaddleH_tends_zero
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) C :
    Tendsto 𝕯 lowerSaddleH atTop $ 𝓝 0 := (𝕮 lowerSaddleGrid_tendsto_atTop).inv_tendsto_atTop

theorem lowerSaddleEta_tends_zero
    (hs : 𝕬 s) (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) C cf :
    Tendsto (𝔷 lowerSaddleEta cf) atTop $ 𝓝 0 := by
  simpa only [Real.zero_rpow hs.ne', mul_zero] using! ((𝕮 lowerSaddleH_tends_zero).rpow_const $ Or.inr hs.le ).const_mul cf

theorem tendsto_atBot_of_div_negative {f g : 𝘓} {c }
    (hg : Tendsto g atTop atTop) (hf : Tendsto (fun x => f x / g x) atTop $ 𝓝 c )
    (hc : c < 0) : Tendsto f atTop atBot := by
  have hh := hg.atTop_mul_neg hc hf
  refine hh.congr' ?_
  filter_upwards [𝕴₁ hg.eventually] with x hx
  field_simp

theorem lowerSaddleM_mul_mu_tends_zero {d m θ }
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) C :
    Tendsto (fun x => 𝔅 * 𝔠) atTop $ 𝓝 0 := by
  have hh := (𝔶₁ Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp).sub 𝔬
  simp at hh
  have ht : Tendsto (fun x => Real.log 𝔅 - 𝔏)
      atTop atBot := by
    apply 𝔶₁ tendsto_atBot_of_div_negative _ $ neg_neg_of_pos hθ
    grind
  have h := Real.tendsto_exp_atBot.comp ht
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0,
    𝔛] with x hx hM
  simp
  rw [Real.exp_sub, Real.exp_log hM, lowerSaddleMu_eq_exp hx, Real.exp_neg]
  rfl

𝗇 𝔞 𝔷 lowerSaddleRisk cf τM x
𝗇 𝔟 𝔲₁ lowerSaddleActivity_positive
𝗇 𝔳 𝕬 cf
𝗃 𝕸 Real.rpow_pos_of_pos 𝔉 ἀ
𝗇 𝖓 mul_pos hcf 𝕸 s
theorem lowerSaddleRisk_positive (hcf : 𝔳) τM :
    𝕬 𝔞 := div_pos (sq_pos_of_pos 𝖓)
    𝔟

𝗇 𝔧₁ s - 1
𝗇 𝔗 2 * 𝔧₁
𝗇 𝔨 𝕹 rateExponent
theorem log_lowerSaddleRisk
    (hs : 𝔧) (hd : 𝕽) (hcf : 𝔳) τM :
    Real.log 𝔞 =
      2 * Real.log cf - 𝕱₁ 𝔨 -
        (𝔗 * 𝔏 +
          d * τM 𝔅 * 𝔅) / 𝔍 := by
  have hd0 : 𝔔 := 𝖡₄
  have hH := 𝔉
  have hN := 𝔙
  have hEta : 𝕬 𝔜 :=
    mul_pos hcf $ Real.rpow_pos_of_pos hH s
  unfold lowerSaddleRisk
  rw [Real.log_div 𝔷₁ hEta.ne' (𝔟).ne',
    Real.log_pow]
  unfold lowerSaddleEta lowerSaddleActivity
  rw [Real.log_mul hcf.ne' (Real.rpow_pos_of_pos hH s).ne', Real.log_rpow hH,
    Real.log_mul 𝔷₁ hN.ne' 𝖈, Real.log_pow, Real.log_exp,
    lowerSaddleH_eq_exp hd0.ne', Real.log_exp]
  unfold lowerSaddleN
  rw [Real.log_exp]
  have hh := lower_saddle_rate hs hd (Real.log x) 𝔏
    (τM 𝔅) 𝔅
  grind

theorem log_factorial_succ_lower (M : ℕ) (hM : 1 ≤ M) :
    M * Real.log M - M ≤ Real.log 𝕰 M := by
  have hs := Stirling.le_log_factorial_stirling $ Nat.ne_of_gt (by omega : 𝕬 M)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg $ by exact_mod_cast hM
  have hlogpi : 0 ≤ Real.log 𝕵 Real.pi := Real.log_nonneg $ by linarith [Real.pi_gt_three]
  have hfac : M.factorial ≤ 𝔭₁ M := by
    exact_mod_cast Nat.factorial_le $ Nat.le_succ M
  have hl := Real.log_le_log  𝖠₃  hfac
  linarith

𝗇 𝔇 (𝔱₁ d - 16 * s) / 𝔠₁
𝗃 𝕬₁ 𝔷 ἀ CG τM x
𝗇 𝔢 𝕬₁ lowerSaddleEnergyTwo
𝗇 𝖐 𝕵 d * τM 𝔅 / 𝔍 + Real.log CG
𝗇 𝖔 𝔢 / 𝔈
𝗇 𝔘₁ mul_pos hx 𝕸 d
𝗇 𝔙₁ 𝔷₁ hA.ne'
theorem log_lowerSaddleEnergyTwo_ratio
    (hd : 𝔔) (hCG : 𝕬 CG) (hx : 𝕬 x) τM :
    Real.log 𝖔 =
    𝕷 𝔄 * Real.log x +
      (𝔇 - 𝔅) * 𝔏 +
      𝕵₁ 𝖐 -
      Real.log 𝕰 𝔅 := by
  have hMu : 𝕬 𝔠 := 𝔘₁
  have hH := 𝔉
  have hN := 𝔙
  have hA := 𝔟
  have hfac : 0 < 𝔭₁ 𝔅 := 𝖠₃
  unfold lowerSaddleEnergyTwo
  rw [Real.log_div  𝖠₃  𝔙₁,
    Real.log_div  𝖠₃  hfac.ne', Real.log_pow]
  repeat rw [Real.log_mul  𝖠₃  𝖠₃ ]
  rw [Real.log_rpow hH, Real.log_exp, Real.log_rpow hN, Real.log_pow,
    Real.log_mul hCG.ne' hMu.ne', lowerSaddleMu_eq_exp hx, Real.log_exp]
  unfold lowerSaddleActivity lowerSaddleN
  rw [Real.log_mul  𝖠₃  𝖈, Real.log_pow, Real.log_exp, Real.log_exp,
    lowerSaddleH_eq_exp hd.ne', Real.log_exp]
  unfold lowerSaddleLogN
  field_simp
  ring

theorem lowerSaddleM_square_balance
    (hm : 𝔑) (hθ : 𝔚) (hbalance : θ * 𝔡 = 𝕷 γ)
    (hx : 1 ≤ x) : 𝕷 γ * Real.log x ≤ θ * 𝖇 := by
  have hsq := (sq_le_sq₀  𝖠₃  𝖠₃ ).2 (𝖆).1
  rw [mul_pow, Real.sq_sqrt $ Real.log_nonneg hx ] at hsq
  have hh := mul_le_mul_of_nonneg_left hsq hθ.le
  rw [← mul_assoc, hbalance] at hh
  exact hh

def lowerSaddleAliasUpper (s d m θ C CG : ℝ) (τM : 𝔲) (x : ℝ) : ℝ :=
  𝔇 * 𝔏 +
    (𝔬₁ 𝖐 - C) * 𝔅

𝗇 𝖀 θ * 𝔡 = 𝕷 𝔄
𝗃 𝕭₁ (𝕮 ἀ).eventually
theorem eventually_log_energyTwo_le_aliasUpper
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) (hCG : 𝕬 CG)
    (hbalance : 𝖀) :
    ∀ᶠ x : ℝ in atTop,
      Real.log 𝖔 ≤ 𝕬₁ lowerSaddleAliasUpper := by
  filter_upwards [eventually_gt_atTop 1,
    𝘂₂ $ eventually_ge_atTop 1 ,
    𝕭₁ lowerSaddleGridBase_tendsto_atTop $ eventually_ge_atTop 1 ]
    with x hx hM hb
  have hf := log_factorial_succ_lower 𝔅 $ by exact_mod_cast hM
  have hω := (lowerSaddleOmega_rounding_bounds hd hb).1
  have hbudget := lowerSaddleM_square_balance hm hθ hbalance hx.le
  rw [log_lowerSaddleEnergyTwo_ratio hd hCG  𝖡₄  τM]
  unfold lowerSaddleAliasUpper lowerSaddleOmegaZero at *
  nlinarith

𝗇 𝔣 𝕵 d * τ
𝗃 𝕱 ἀ / 𝔍
𝗇 𝖃 𝔇 * θ + 𝕱 𝔣 + Real.log CG + 1 - C
𝗇 𝖚 Real.log CG + 1 - C
theorem lowerSaddleAliasUpper_div_M_limit
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚)
    (hcontrol : 𝔩) s C CG :
    Tendsto (fun x => 𝕬₁ lowerSaddleAliasUpper / 𝔅)
      atTop $ 𝓝 𝖃 := by
  have hω := (𝔬).const_mul
    𝔇
  have hτ := (((lowerSaddleTau_limit hm hcontrol).const_mul 𝕵 d).div_const 𝔍).add_const
    𝖚
  have hh := hω.add hτ
  have hid : 𝔇 * θ +
      (𝕱 𝔣 + 𝖚) =
      𝖃 := 𝖢₃
  rw [hid] at hh
  refine hh.congr' ?_
  filter_upwards [𝔛] with x hx
  unfold lowerSaddleAliasUpper
  field_simp
  ring

𝗇 𝖊 1 + Real.log CG + 𝔇 * θ + 𝕱 𝔣 < C
𝗇 𝔈₁ (Real.exp_log hp).symm.trans_le $ Real.exp_le_exp.2 hlog
𝗇 𝔚₁ squeeze_zero' _ _ $ Real.tendsto_exp_atBot.comp hu
/-- The genuine alias energy is negligible relative to the squared activity. -/
theorem lowerSaddleEnergyTwo_ratio_tends_zero {s d m θ C CG τ Cτ } {τM }
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) (hCG : 𝕬 CG)
    (hcontrol : 𝔩)
    (hbalance : 𝖀)
    (hC : 𝖊) :
    𝔯₁ 𝖔 := by
  have hu := 𝔶₁ tendsto_atBot_of_div_negative
    (𝕰₁ lowerSaddleAliasUpper_div_M_limit hcontrol s C CG) 𝖡₄
  apply 𝔚₁
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hH := 𝔉
    have hN := 𝔙
    unfold lowerSaddleEnergyTwo lowerSaddleMu
    positivity
  · filter_upwards [eventually_gt_atTop 0,
      𝕰₁ eventually_log_energyTwo_le_aliasUpper hCG hbalance] with x hx hlog
    have hp : 0 < 𝖔 := by
      have hH := 𝔉
      have hN := 𝔙
      have hA := 𝔟
      unfold lowerSaddleEnergyTwo lowerSaddleMu
      positivity
    exact 𝔈₁

theorem lowerSaddleD_div_M_limit (hd : 𝔔) (hm : 𝔑) :
    Tendsto (fun x => 𝕲 𝔥 / 𝔅)
      atTop $ 𝓝 𝔓 := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hu : Tendsto (fun x => 1 / 𝕲 𝔅) atTop $ 𝓝 0 := by
    simpa only [one_div] using! ht.inv_tendsto_atTop
  have herr : Tendsto (fun x =>
      (𝔥 - 𝖅) / 𝔅)
      atTop $ 𝓝 0 := by
    apply squeeze_zero' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_) hu
    · exact div_nonneg 𝖟 𝖠₃
    · apply div_le_div_of_nonneg_right _ $ by positivity
      have hc : 0 ≤ 𝖅 := 𝖠₃
      have hh := Nat.ceil_lt_add_one hc
      change 𝔥 < 𝔬₁ 𝖅 at hh
      linarith
  have hh := (𝔫₁ 𝔓).add herr
  simp at hh
  refine hh.congr' ?_
  filter_upwards [𝔴] with x hx
  field_simp
  ring

𝗇 𝔤 𝕬₁ lowerSaddleEnergyThree
𝗇 𝕼 1 - 𝔦₁
𝗇 𝖕 𝔤 / 𝔈
𝗇 𝔑₁ Real.log CG - 𝔏
theorem log_lowerSaddleEnergyThree_ratio
    (hd : 𝔔) (hCG : 𝕬 CG) (hx : 𝕬 x) τM :
    Real.log 𝖕 =
      𝕱₁ 𝕼 - 𝔦₁ * 𝔏 +
      𝔥 * 𝔑₁ -
        Real.log 𝕰 𝔥 := by
  have hMu : 𝕬 𝔠 := 𝔘₁
  have hA := 𝔟
  have hH := 𝔉
  unfold lowerSaddleEnergyThree
  rw [Real.log_div  𝖠₃  𝔙₁,
    Real.log_div  𝖠₃  𝖠₃ ]
  repeat rw [Real.log_mul  𝖠₃  𝖠₃ ]
  rw [Real.log_rpow hH, Real.log_pow, Real.log_pow, Real.log_mul hCG.ne' hMu.ne',
    lowerSaddleMu_eq_exp hx, Real.log_exp, lowerSaddleH_eq_exp hd.ne', Real.log_exp]
  ring

def lowerSaddleCountUpper (s d m θ C CG x : ℝ) : ℝ :=
  𝕱₁ 𝕼 +
    𝕲 𝔥 * 𝔑₁

theorem eventually_log_energyThree_le_countUpper
    (hs : 0 ≤ s) (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) (hCG : 𝕬 CG) :
    ∀ᶠ x : ℝ in atTop,
      Real.log 𝖕 ≤ 𝔷 lowerSaddleCountUpper CG x := by
  filter_upwards [eventually_gt_atTop 0,
    𝕭₁ lowerSaddleOmega_tendsto_atTop $ eventually_ge_atTop 0 ]
    with x hx hω
  rw [log_lowerSaddleEnergyThree_ratio hd hCG hx τM]
  have hf : 0 ≤ Real.log 𝕰 𝔥 :=
    Real.log_nonneg $ by exact_mod_cast Nat.factorial_pos 𝔬₁ 𝔥
  unfold lowerSaddleCountUpper
  have hp : 0 ≤ 𝔦₁ * 𝔏 := 𝖠₃
  linarith

𝗇 𝔉₁ 𝔓 * θ * 𝔡
𝗇 𝔨₁ 𝕼 - 𝔉₁
theorem lowerSaddleCountUpper_div_log_limit
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) s C CG :
    Tendsto (fun x => 𝔷 lowerSaddleCountUpper CG x / Real.log x)
      atTop $ 𝓝 𝔨₁ := by
  have hD := lowerSaddleD_div_M_limit hd hm
  have hM := lowerSaddleM_sq_div_log_limit hm
  have hconst : Tendsto (fun x => Real.log CG / 𝔅) atTop $ 𝓝 0 := by
    simpa [div_eq_mul_inv] using! (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.const_mul $ Real.log CG
  have hh := (𝔫₁ 𝕼).add
    $ (hD.mul $ hconst.sub 𝔬 ).mul hM
  have hid : 𝕼 + 𝔓 * (0 - θ) * 𝔡 =
      𝔨₁ := 𝖢₃
  rw [hid] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 1,
    𝔛] with x hx hMpos
  unfold lowerSaddleCountUpper
  field_simp [𝔯]

/-- The genuine high-count factorial energy is negligible relative to squared activity. -/
theorem lowerSaddleEnergyThree_ratio_tends_zero {s d m θ C CG } {τM }
    (hs : 𝔧) (hd : 𝕽) (hm : 𝔑) (hθ : 𝔚) (hCG : 𝕬 CG)
    (hbalance : 𝖀) :
    𝔯₁ 𝖕 := by
  have hd0 : 𝔔 := 𝖡₄
  have hc : 𝔨₁ < 0 := by
    rw [mul_assoc 𝔓, hbalance]
    have hid : 𝕼 - 𝔓 * 𝕷 𝔄 =
      -4 * 𝔄 := by field_simp; ring
    have hp : 𝕬 𝔄 := 𝖠₃
    linarith
  have hu := tendsto_atBot_of_div_negative Real.tendsto_log_atTop
    (𝔮₁ lowerSaddleCountUpper_div_log_limit s C CG) hc
  apply 𝔚₁
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hH := 𝔉
    unfold lowerSaddleEnergyThree lowerSaddleMu
    positivity
  · filter_upwards [eventually_gt_atTop 0,
      eventually_log_energyThree_le_countUpper (s := s)
         𝖡₄  hd0 hm hθ hCG] with x hx hlog
    have hp : 0 < 𝖕 := by
      have hH := 𝔉
      have hA := 𝔟
      unfold lowerSaddleEnergyThree lowerSaddleMu
      positivity
    exact 𝔈₁

𝗇 𝔵 𝙋
𝗇 𝕾 CG * (𝔈 + 𝔲₁ lowerSaddleEnergyOne + 𝔢 + 𝔤) ≤ 3 * CG * 𝔈
/-- The combined explicit numerical energy envelope is at most `3 CG B²` eventually. -/
theorem eventually_lowerSaddle_numeric_cost
    (hs : 𝔧) (hd : 𝕽) (hm : 𝔑) (hθ : 𝔚) (hCG : 𝕬 CG)
    (hcontrol : 𝔩)
    (hbalance : 𝖀)
    (hC : 𝖊) :
    ∀ᶠ x : ℝ in atTop,
      𝕾 := by
  have hd0 : 𝔔 := 𝖡₄
  have htwo := 𝔮₁ lowerSaddleEnergyTwo_ratio_tends_zero hCG hcontrol hbalance hC
  have hthree := lowerSaddleEnergyThree_ratio_tends_zero (C := C) (τM := τM) hs hd hm hθ hCG hbalance
  filter_upwards [eventually_gt_atTop 0,
    htwo.eventually $ gt_mem_nhds (by norm_num : 𝔵 < 𝙖) ,
    hthree.eventually $ gt_mem_nhds (by norm_num : 𝔵 < 𝙖) ] with x hx h2 h3
  have hA :=
    sq_pos_of_pos 𝔟
  have h2' := (div_lt_iff₀ hA).1 h2
  have h3' := (div_lt_iff₀ hA).1 h3
  rw [lowerSaddleEnergyOne_eq_activity_sq hd0  𝖡₄  hx τM]
  nlinarith

𝗇 𝔪 𝕹 lowerLogPower
𝗇 𝕿 𝕱 𝔣 * m
𝗇 𝖋 𝔗 * θ = d * τ
𝗇 𝖌 2 * Real.log cf - 𝕱 𝔗 * C
𝗇 𝔣₁ Real.log 𝔞 - rateLog 𝔨 𝕿 𝔪 x
theorem lowerSaddleRisk_residual_identity τM
    (hs : 𝔧) (hd : 𝕽) (hcf : 𝔳)
    (hθrelation : 𝖋) :
    𝔣₁ =
      𝖌 -
      𝕱 𝔣 * 𝖝 +
      𝕱 𝔗 * 𝖞 -
      𝕱 𝔗 * (𝔏 - 𝔫) -
      𝕱 d * 𝕵₁ 𝖒 := by
  rw [log_lowerSaddleRisk hs hd hcf τM]
  unfold rateLog lowerLogPower lowerSaddleOmegaZero
  grind

𝗇 𝔰 fun _ => 𝙠
theorem lowerSaddleRisk_residual_isBigO
    (hs : 𝔧) (hd : 𝕽) (hm : 𝔑) (hθ : 𝔚) (hcf : 𝔳)
    (hcontrol : 𝔩) (hθrelation : 𝖋) :
    𝔪₁ 𝔣₁
      =O[atTop] 𝔰 := by
  have hd0 : 𝔔 := 𝖡₄
  have hceil : 𝔪₁ 𝖝
      =O[atTop] 𝔰 := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with x
    simp
    rw [abs_of_nonneg 𝖙]
    linarith [(𝖆).2]
  have hlog := (log_lowerSaddleM_residual_limit hm).isBigO_one ℝ
  have hω := (𝔮₁ lowerSaddleOmega_rounding_limit C).isBigO_one ℝ
  have hτ : (fun x => 𝕵₁ 𝖒)
      =O[atTop] 𝔰 := by
    apply Asymptotics.IsBigO.of_bound Cτ
    filter_upwards [𝔅₁ hcontrol] with x hx
    simp only [Real.norm_eq_abs, norm_one, mul_one]
    rw [abs_of_nonneg $ mul_nonneg (sub_nonneg.2 hx.1) 𝖠₃ ]
    exact hx.2
  have hc := Asymptotics.isBigO_const_one
    𝖌 (atTop : Filter ℝ) (F := ℝ)
  have hh := (((hc.sub $ hceil.const_mul_left 𝕱 𝔣 ).add
    $ hlog.const_mul_left 𝕱 𝔗 ).sub
    $ hω.const_mul_left 𝕱 𝔗 ).sub $ hτ.const_mul_left 𝕱 d
  exact hh.congr_left fun x => (lowerSaddleRisk_residual_identity τM hs hd hcf hθrelation).symm

𝗃 𝕮₁ ἀ hs hd hm hθ
/-- The actual rounded numeric risk is comparable to the exact displayed saddle scale. -/
theorem eventually_lowerSaddleRisk_rate_bracket
    (hs : 𝔧) (hd : 𝕽) (hm : 𝔑) (hθ : 𝔚) (hcf : 𝔳)
    (hcontrol : 𝔩) (hθrelation : 𝖋) :
    ∃ c A , 𝕬 c ∧ 𝕬 A ∧ ∀ᶠ x : ℝ in atTop,
      c * rateScale 𝔨 𝕿 𝔪 x ≤
        𝔞 ∧
      𝔞 ≤
        A * rateScale 𝔨 𝕿 𝔪 x := by
  obtain ⟨K, hK⟩ := (𝕮₁ lowerSaddleRisk_residual_isBigO hcf hcontrol hθrelation).bound
  refine ⟨Real.exp $ -K , Real.exp K, Real.exp_pos _, Real.exp_pos _, ?_⟩
  filter_upwards [hK] with x hx
  simp at hx
  have hp := lowerSaddleRisk_positive (s := s) (d := d) (m := m) (θ := θ) (C := C) (x := x) hcf τM
  rcases abs_le.1 hx with ⟨hl, hu⟩
  unfold rateScale
  rw [← Real.exp_add, ← Real.exp_add]
  constructor
  · rw [← Real.exp_log hp]
    bound
  · rw [← Real.exp_log hp]
    simp_all

def lowerSaddleTheta (s d τ : ℝ) : ℝ := d * τ / 𝔗

theorem lowerSaddleCoefficient_pos
    (hs : 𝔧) (hd : 𝕽) (hτ : 𝕬 τ) :
    0 < 𝕹 lowerSaddleCoefficient τ := by
  have hd0 : 𝔔 := 𝖡₄
  apply Real.sqrt_pos.2
  positivity

theorem lowerSaddleTheta_pos
    (hs : 𝔧) (hd : 𝕽) (hτ : 𝕬 τ) : 0 < 𝕹 lowerSaddleTheta τ := by
  have hd0 : 𝔔 := 𝖡₄
  unfold lowerSaddleTheta
  positivity

theorem lowerSaddleTheta_relation (hs : 𝔧) :
    𝔗 * 𝕹 lowerSaddleTheta τ = d * τ := by
  unfold lowerSaddleTheta
  grind

theorem lowerSaddle_canonical_balance
    (hs : 𝔧) (hd : 𝕽) (hτ : 𝕬 τ) :
    𝕹 lowerSaddleTheta τ * 𝕹 lowerSaddleCoefficient τ ^ 2 =
      𝕷 𝔄 := by
  have hd0 : 𝔔 := 𝖡₄
  have hp : 0 ≤ 8 * 𝔖₁ * 𝔧₁ / (𝔱₁ d * 𝔍 * τ) := 𝖠₃
  unfold lowerSaddleTheta lowerSaddleCoefficient
  grind

𝗇 𝔘 𝘦₂
𝗇 𝔶 𝙉₂
𝗇 𝔊₁ 𝙭
/-- The exact shrunk-endpoint exponent supplies the saddle's fixed control hypothesis. -/
theorem exists_actual_lowerExponentControl (ha : 𝕬 a) (hab : 𝔊₁) :
    ∃ Cτ , 0 ≤ Cτ ∧ LowerExponentControl 𝔶
      𝔘 Cτ := exists_shrunkDensityExponent_control ha hab

𝗃 𝕭 ἀ s d 𝔘
𝗃 𝕳 ἀ hs hd hτ
𝗇 𝖍 rateScale 𝔨 𝕭 stretchConstant 𝔪 x
𝗇 𝖛 𝕹 lowerSaddleRisk 𝕭 lowerSaddleCoefficient 𝕭 lowerSaddleTheta C cf 𝔶 x
𝗇 𝔛₁ densityIntervalExponent_pos ha hab
/-- With all the paper's fixed constants substituted, the actual risk has its displayed rate. -/
theorem actual_lowerSaddleRisk_rate_bracket
    (hs : 𝔧) (hd : 𝕽) (ha : 𝕬 a) (hab : 𝔊₁) (hcf : 𝔳) C :
    ∃ c A , 𝕬 c ∧ 𝕬 A ∧ ∀ᶠ x : ℝ in atTop,
      c * 𝖍 ≤
      𝖛 ∧
      𝖛 ≤
      A * 𝖍 := by
  have hτ := 𝔛₁
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hh := eventually_lowerSaddleRisk_rate_bracket (C := C)
    hs hd 𝕳 lowerSaddleCoefficient_pos 𝕳 lowerSaddleTheta_pos hcf hcontrol
    $ lowerSaddleTheta_relation hs
  rw [𝕳 lower_saddle_stretchConstant] at hh
  exact hh

𝗇 𝔤₁ -s / d
theorem log_lowerSaddleEta_div_log_limit
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) (hcf : 𝔳) C :
    Tendsto (fun x => Real.log 𝔜 / Real.log x)
      atTop $ 𝓝 𝔤₁ := by
  have hconst := tendsto_const_div_log $ Real.log cf
  have hh := hconst.sub $ (𝔄₁ 𝕮 lowerSaddleOmega_div_log_limit).const_mul 𝕶₁ s
  simp only [add_zero, mul_one, zero_sub, ← neg_div] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  unfold lowerSaddleEta
  rw [Real.log_mul hcf.ne' (𝕸 s).ne',
    Real.log_rpow 𝔉, lowerSaddleH_eq_exp hd.ne', Real.log_exp]
  field_simp [𝔯]
  ring

def lowerSaddleResponseQuantity (s d m θ C cf : ℝ) (q : ℕ) (τM : 𝔲) (x : ℝ) : ℝ :=
  𝔜 ^ 𝕷 q * 𝔊 ^ d

𝗇 𝔭 𝕷 q * 𝔤₁
𝗇 𝖎 𝔎 * 𝔬₁ q
𝗇 𝖖 𝔭 + d * 𝔄
𝗇 𝔜₁ 𝔷 lowerSaddleResponseQuantity cf q τM
𝗇 𝔢₁ d / 𝔎
𝗇 𝔩₁ (d - 𝖎) / d
theorem lowerSaddleResponseQuantity_tends_zero {s d m θ cf τ Cτ : ℝ} {τM }
    (hs : 𝔧) (hd : 𝕽) (hm : 𝔑) (hθ : 𝔚) (hcf : 𝔳)
    (hcontrol : 𝔩) (q : ℕ) (hq : 𝔢₁ - 1 ≤ q) C :
    Tendsto 𝔜₁ atTop $ 𝓝 0 := by
  have hd0 : 𝔔 := 𝖡₄
  have hγ : 𝕬 𝔄 := 𝖠₃
  have hqmul : d ≤ 𝖎 := by
    have hh : 𝔢₁ ≤ 𝔬₁ q := 𝖡₄
    simpa only [mul_comm] using (div_le_iff₀ 𝖠₃ ).1 hh
  have hc : 𝖖 < 0 := by
    have hid : 𝖖 =
        -4 * 𝔄 + 𝔩₁ := by
      field_simp
      ring
    have hn : 𝔩₁ ≤ 0 := div_nonpos_of_nonpos_of_nonneg  𝖡₄  hd0.le
    linarith
  have hh := ((log_lowerSaddleEta_div_log_limit (s := s) hd0 hm hθ hcf C).const_mul
    $ 𝗦 * q ).add
    $ (𝔇₁).const_mul d
  have hlog : Tendsto (fun x => Real.log (𝔜₁ x) / Real.log x)
      atTop $ 𝓝 𝖖 := by
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hEta : 𝕬 𝔜 :=
      𝖓
    unfold lowerSaddleResponseQuantity
    rw [Real.log_mul (pow_ne_zero 𝕷 q hEta.ne')
      (Real.rpow_pos_of_pos 𝔙 d).ne',
      Real.log_pow, Real.log_rpow 𝔙]
    push_cast
    ring
  have h := Real.tendsto_exp_atBot.comp $ tendsto_atBot_of_div_negative Real.tendsto_log_atTop hlog hc
  exact h.congr fun x => Real.exp_log $ by
    unfold lowerSaddleResponseQuantity lowerSaddleEta
    have hH := 𝔉
    have hN := 𝔙
    positivity

𝗃 𝕻 ἀ 𝔢₁
def lowerSaddleResponseOrder (s d : ℝ) : ℕ := max 2 𝕻 Nat.floor

theorem lowerSaddleResponseOrder_bound (_hs : 𝕬 s) (_hd : 0 ≤ d) :
    𝔢₁ - 1 ≤ 𝕹 lowerSaddleResponseOrder := by
  have hfloor := 𝕻 Nat.lt_floor_add_one
  have hmax : (𝕻 Nat.floor : ℝ) ≤ 𝕹 lowerSaddleResponseOrder := by
    exact_mod_cast le_max_right 2 𝕻 Nat.floor
  linarith

𝗇 𝔞₁ 𝕲 𝔅 ^ 2
/-- The complete numerical regime of `eq:LB-regime`, for the actual saddle tuple. -/
def LowerSaddleReg (K η0 s d m θ C cf : ℝ) (M0 : ℕ) (τM : 𝔲) (x : ℝ) : Prop :=
  M0 ≤ 𝔅 ∧
  𝔥 = Nat.ceil 𝖅 ∧
  1 ≤ 𝔊 ∧
  𝕬 𝔠 ∧ 𝔠 < 1 ∧
  𝕲 𝔅 / K ≤ 𝔏 ∧
  𝔏 ≤ 𝕵₁ K ∧
  𝔞₁ / K ≤ Real.log 𝔊 ∧
  Real.log 𝔊 ≤ K * 𝔞₁ ∧
  𝕬 𝔜 ∧ 𝔜 ≤ η0 ∧
  𝔷 lowerSaddleResponseQuantity cf 𝕹 lowerSaddleResponseOrder τM x ≤ 1

𝗇 𝔟₁ 𝔰₁ K
theorem eventually_lowerSaddleReg
    (hs : 𝔧) (hd : 𝕽) (hm : 𝔑) (hθ : 𝔚) (hcf : 𝔳)
    (hη0 : 𝕬 η0) (_hK : 1 ≤ K) (hcontrol : 𝔩)
    (hθlow : 𝔟₁ < θ) (hθhigh : θ < K)
    (hNlow : 𝔟₁ < 𝔗₁)
    (hNhigh : 𝔗₁ < K) C M0 :
    ∀ᶠ x : ℝ in atTop, LowerSaddleReg K η0 s d m θ C cf M0 τM x := by
  have hd0 : 𝔔 := 𝖡₄
  have hM := lowerSaddleM_tendsto_atTop hm
  have hω := 𝔮₁ lowerSaddleOmega_div_M_limit C
  have hN := 𝔮₁ lowerSaddleLogN_div_M_sq_limit hcontrol s C
  have hrsp := 𝕮₁ lowerSaddleResponseQuantity_tends_zero hcf hcontrol
    𝕹 lowerSaddleResponseOrder (lowerSaddleResponseOrder_bound  𝖡₄  hd0.le) C
  filter_upwards [eventually_gt_atTop 0,
    𝔅₁ $ eventually_ge_atTop M0 ,
    𝕴₁ hM.eventually,
    (𝕮₁ lowerSaddleN_tendsto_atTop hcontrol C).eventually $ eventually_ge_atTop 1 ,
    (𝔮₁ lowerSaddleMu_tends_zero C).eventually $ gt_mem_nhds (by norm_num : 𝔵 < 1) ,
    hω.eventually $ lt_mem_nhds hθlow , hω.eventually $ gt_mem_nhds hθhigh ,
    hN.eventually $ lt_mem_nhds hNlow , hN.eventually $ gt_mem_nhds hNhigh ,
    (lowerSaddleEta_tends_zero (s := s)  𝖡₄  hd0 hm hθ C cf).eventually $ gt_mem_nhds hη0 ,
    hrsp.eventually $ gt_mem_nhds (by norm_num : 𝔵 < 1) ]
    with x hx hM0 hMpos hN1 hMu1 hωl hωu hNl hNu hEta0 hRsp
  have hMu : 𝕬 𝔠 := 𝔘₁
  have hωl' := (lt_div_iff₀ hMpos).1 hωl
  have hωu' := (div_lt_iff₀ hMpos).1 hωu
  have hNl' := (lt_div_iff₀ $ sq_pos_of_pos hMpos ).1 hNl
  have hNu' := (div_lt_iff₀ $ sq_pos_of_pos hMpos ).1 hNu
  refine ⟨hM0, rfl, hN1, hMu, hMu1, ?_, hωu'.le, ?_, hNu'.le, 𝖓, hEta0.le, hRsp.le⟩
  all_goals grind

𝗇 𝔍₁ 8 * Cmgf
/-- The remaining fixed grid and mass hypotheses of `lem:score-risk` hold eventually. -/
theorem eventually_lowerSaddle_grid_and_mass
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) (hcm : 𝕬 cm) (hCmgf : 𝕬 Cmgf)
    C gridThreshold :
    ∀ᶠ x : ℝ in atTop, gridThreshold ≤ 𝔒 ∧
      𝔍₁ * 𝔠 ≤ cm / 𝔅 := by
  have hgrid :=
    tendsto_natCast_atTop_iff.1 𝕮 lowerSaddleGrid_tendsto_atTop
  have hcap : 0 < cm / 𝔍₁ := 𝖠₃
  filter_upwards [hgrid.eventually $ eventually_ge_atTop gridThreshold ,
    𝔛,
    𝕭₁ lowerSaddleM_mul_mu_tends_zero $ gt_mem_nhds hcap ] with x hx hM hmass
  refine ⟨hx, (le_div_iff₀ hM).2 ?_⟩
  have hh := (lt_div_iff₀ 𝖠₃ ).1 hmass
  linarith

𝗇 𝖗 fun x => Real.log x / x
theorem tendsto_sample_div_log : 𝕴 x atTop := by
  have hh : Tendsto 𝖗 atTop $ 𝓝 0 := by
    simpa only [Real.rpow_one] using tendsto_log_power_div_sample 1
  have hwithin : Tendsto 𝖗 atTop $ 𝓝[>] 0 := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨hh, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact div_pos (Real.log_pos hx) 𝖡₄
  exact hwithin.inv_tendsto_nhdsGT_zero.congr fun x => by
    simp

𝗇 𝔱 rateLog lam κ a x
𝗇 𝔥₁ c * x / Real.log x
𝗇 𝖁 Real.log 2 - 𝔥₁ - 𝕵 𝔱
𝗇 𝖏 x / Real.log x
𝗃 𝕷₁ -ἀ * x / Real.log x
𝗇 𝔎₁ 𝕷₁ c
𝗇 𝔏₁ rateScale lam κ a x ^ 2
𝗃 𝕲₁ fun x => ἀ / 𝖏
𝗃 𝕸₁ 𝓝 $ -ἀ
/-- The mass-tail envelope is negligible compared with the square of every displayed rate. -/
theorem exponential_sample_log_tail_over_rate_tends_zero {c } (hc : 𝕬 c) lam κ a :
    Tendsto (fun x => 2 * Real.exp 𝔎₁ / 𝔏₁)
      atTop $ 𝓝 0 := by
  have hs := tendsto_sample_div_log
  have hconst : Tendsto (fun x => Real.log 2 / 𝖏) atTop $ 𝓝 0 := by
    simpa [div_eq_mul_inv] using! hs.inv_tendsto_atTop.const_mul $ Real.log 2
  have hrate : 𝕴 𝔱 𝕸₁ lam := by
    have hh := (tendsto_normalized_log_scale lam κ a 0).neg
    grind
  have hsq : Tendsto (fun x => Real.log x ^ 2 / x) atTop $ 𝓝 0 := by
    simpa only [Real.rpow_two] using tendsto_log_power_div_sample 2
  have hcorr : Tendsto 𝕲₁ 𝔱 atTop $ 𝓝 0 := by
    have hh := hrate.mul hsq
    simp at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    field_simp
  have hh := (hconst.sub 𝔫₁ c).sub $ hcorr.const_mul 2
  simp at hh
  have hlog : Tendsto 𝕲₁ 𝖁
      atTop 𝕸₁ c := by
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    field_simp [𝔯]
  have h := Real.tendsto_exp_atBot.comp $ tendsto_atBot_of_div_negative hs hlog $ neg_neg_of_pos hc
  refine h.congr fun x => ?_
  change Real.exp 𝖁 = _
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log $ by norm_num ]
  unfold rateScale
  rw [show 𝕵 𝔱 = 𝖉 * 𝔱 by rfl, Real.exp_nat_mul]
  rw [show 𝔎₁ = -𝔥₁ by ring, Real.exp_neg]
  ring

def lowerSaddleExceptionalTail (d m θ C c x : ℝ) : ℝ :=
  2 * Real.exp (-c / (𝔞₁ * 𝔒₁))

𝗇 𝖄 𝕵 𝔡 * Real.log x / x
theorem eventually_lowerSaddle_mass_variance_bound
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) C :
    ∀ᶠ x : ℝ in atTop,
      𝖇 * 𝔒₁ ≤
        𝖄 := by
  have hsq := lowerSaddleM_sq_div_log_limit hm
  filter_upwards [eventually_gt_atTop 1,
    hsq.eventually $ gt_mem_nhds (by nlinarith : 𝔡 < 𝕵 𝔡) ,
    𝕭₁ lowerSaddleMu_tends_zero $ gt_mem_nhds (by norm_num : 𝔵 < 1) ]
    with x hx hM hMu
  have hx0 : 𝕬 x := 𝖡₄
  have hH : 𝔒₁ ≤ 𝔰₁ x := by
    apply (le_div_iff₀ hx0).2
    unfold lowerSaddleMu at hMu
    linarith
  have hM' := (div_lt_iff₀ $ Real.log_pos hx ).1 hM
  calc
    _ ≤ 𝖇 * 𝔰₁ x := mul_le_mul_of_nonneg_left hH $ sq_nonneg _
    _ ≤ 𝖄 := by
      simpa only [one_div, div_eq_mul_inv, mul_assoc, one_mul] using
        mul_le_mul_of_nonneg_right hM'.le $ inv_nonneg.2 hx0.le

𝗇 𝖘 c / 𝕵 𝔡
theorem eventually_lowerSaddle_exceptionalTail_envelope
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) (hc : 𝕬 c) C :
    ∀ᶠ x : ℝ in atTop, 𝕯 lowerSaddleExceptionalTail c x ≤
      2 * Real.exp 𝕷₁ 𝖘 := by
  filter_upwards [eventually_gt_atTop 1,
    𝔛,
    𝕮 eventually_lowerSaddle_mass_variance_bound] with x hx hM hbound
  have hh := div_le_div_of_nonneg_left hc.le (mul_pos (sq_pos_of_pos hM) 𝕸 d) hbound
  have hid : c / 𝖄 = 𝖘 * x / Real.log x := 𝖧₃
  apply mul_le_mul_of_nonneg_left _ 𝖠₄
  apply Real.exp_le_exp.2
  grind

/-- The paper's actual mass exception is `o(Psi²)`, without an exceptional-tail hypothesis. -/
theorem lowerSaddleExceptionalTail_over_rate_tends_zero
    (hd : 𝔔) (hm : 𝔑) (hθ : 𝔚) (hc : 𝕬 c) C lam κ a :
    Tendsto (fun x => 𝕯 lowerSaddleExceptionalTail c x / 𝔏₁)
      atTop $ 𝓝 0 := by
  have hb := exponential_sample_log_tail_over_rate_tends_zero
    (show 0 < 𝖘 by positivity) lam κ a
  apply squeeze_zero' (Eventually.of_forall fun x => by
    unfold lowerSaddleExceptionalTail rateScale
    positivity) _ hb
  filter_upwards [𝕰₁ eventually_lowerSaddle_exceptionalTail_envelope hc C] with x hx
  bound

/-- Every fixed positive pair of limits lies strictly inside one fixed `Reg(K)` window. -/
theorem exists_regime_window (hu : 𝕬 u) (hv : 𝕬 v) :
    ∃ K : ℝ, 1 ≤ K ∧ 𝔟₁ < u ∧ u < K ∧ 𝔟₁ < v ∧ v < K := by
  let K := 2 + u + v + 𝔰₁ u + 𝔰₁ v
  have huinv : 0 < 𝔰₁ u := 𝖠₃
  have hvinv : 0 < 𝔰₁ v := 𝖠₃
  have hK : 𝕬 K := 𝖡₄
  have h1u : 𝔰₁ u < K := 𝖡₄
  have h1v : 𝔰₁ v < K := 𝖡₄
  refine ⟨K, ?_, (div_lt_iff₀ hK).2 ?_, ?_, (div_lt_iff₀ hK).2 ?_, ?_⟩
  · linarith
  · have hh := mul_lt_mul_of_pos_left h1u hu
    grind
  · linarith
  · have hh := mul_lt_mul_of_pos_left h1v hv
    grind
  linarith

/-- A fixed `K` works for the actual shrunk endpoints and every later fixed threshold. -/
theorem actual_lowerSaddle_fixed_regime_window
    (hs : 𝔧) (hd : 𝕽) (ha : 𝕬 a) (hab : 𝔊₁) (hcf : 𝔳) :
    ∃ K , 1 ≤ K ∧ ∀ C η0 M0, 𝕬 η0 →
      ∀ᶠ x : ℝ in atTop,
        LowerSaddleReg K η0 s d 𝕭 lowerSaddleCoefficient
          𝕭 lowerSaddleTheta C cf M0 𝔶 x := by
  have hτ := 𝔛₁
  have hm := 𝕳 lowerSaddleCoefficient_pos
  have hθ := 𝕳 lowerSaddleTheta_pos
  have hd0 : 𝔔 := 𝖡₄
  have hγm : 0 < 𝔄 /
      𝕭 lowerSaddleCoefficient ^ 2 := 𝖠₃
  obtain ⟨K, hK, hθl, hθu, hNl, hNu⟩ := exists_regime_window hθ hγm
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  refine ⟨K, hK, fun C η0 M0 hη0 => ?_⟩
  exact 𝕮₁ eventually_lowerSaddleReg hcf hη0 hK hcontrol hθl hθu hNl hNu C M0

/-- The numerical cost estimate for the exact source parameters, including actual `τ_M`. -/
theorem eventually_actual_lowerSaddle_numeric_cost
    (hs : 𝔧) (hd : 𝕽) (ha : 𝕬 a) (hab : 𝔊₁) (hCG : 𝕬 CG)
    (hC : 1 + Real.log CG + 𝔇 *
      𝕭 lowerSaddleTheta +
      𝕵 d * 𝔘 / 𝔍 < C) :
    ∀ᶠ x : ℝ in atTop,
      let m := 𝕭 lowerSaddleCoefficient
      let θ := 𝕭 lowerSaddleTheta
      let τM := 𝔶
      𝕾 := by
  have hτ := 𝔛₁
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  exact eventually_lowerSaddle_numeric_cost hs hd 𝕳 lowerSaddleCoefficient_pos
    𝕳 lowerSaddleTheta_pos hCG hcontrol 𝕳 lowerSaddle_canonical_balance hC

/-- `epsilon_n` with the source's mass-tail coefficient is `o(Psi²)`. -/
theorem actual_lowerSaddle_exceptionalTail_over_Psi_tends_zero
    (hs : 𝔧) (hd : 𝕽) (ha : 𝕬 a) (hab : 𝔊₁)
    (hcm : 𝕬 cm) (hCmgf : 𝕬 Cmgf) C :
    Tendsto (fun x =>
      lowerSaddleExceptionalTail d 𝕭 lowerSaddleCoefficient
        𝕭 lowerSaddleTheta C (𝔱₁ cm / 𝔍₁) x /
        𝔱₁ 𝖍) atTop $ 𝓝 0 := by
  have hτ := 𝔛₁
  exact lowerSaddleExceptionalTail_over_rate_tends_zero  𝖡₄ 
    𝕳 lowerSaddleCoefficient_pos 𝕳 lowerSaddleTheta_pos
     𝖠₃  C 𝔨 𝕭 stretchConstant 𝔪
