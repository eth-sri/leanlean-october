module

public import NearlyMinimax.LowerActivityHierarchy
public import NearlyMinimax.FieldTailSummation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual rounded saddle absorbs the higher-field scale energy into
mu² N^-d. The negative quadratic logarithmic scale is proved explicitly. -/
𝚷
𝚶
𝚨
𝚩

𝗇 𝔔 c0 * (𝖩₁ - 4)
𝗇 𝔉 𝔔
𝗇 𝔗 𝗫
𝗇 𝔍 2 * tauM 𝔗 * 𝔗
𝗇 𝔎 𝚜₂
𝗃 𝔐 ἀ s d m theta C
def lowerSaddleFineFieldScale (s d m theta C c0 : ℝ) (tauM : 𝙜) (x : ℝ) : ℝ :=
  Real.exp 𝔍 *
    𝔐 lowerSaddleN tauM x ^ 𝔎 *
    Real.exp (𝔉 * 𝙵)

𝗇 𝔊 𝔐 lowerSaddleN_positive tauM x
𝗇 𝔏 𝔐 lowerSaddleFineFieldScale c0 tauM
theorem lowerSaddleFineFieldScale_positive s d m theta C c0 tauM x :
    0 < 𝔏 x := by
  unfold lowerSaddleFineFieldScale
  positivity [𝔊]

𝗇 𝔅 (d - 𝚄) / (d * 𝙾₁) / m ^ 2
theorem lowerSaddleFineFieldScale_tends_zero
    (hs : 𝚊₁) (hd : 𝚄 < d) (hm : 0 < m) (htheta : 0 < theta)
    (hcontrol : LowerExponentControl tauM tau Ctau) C c0 :
    Tendsto 𝔏 atTop $ 𝓝 0 := by
  have hd0 : 𝗆 := 𝖡₄
  have hM := lowerSaddleM_tendsto_atTop hm
  have hM2 : Tendsto (fun x => (𝔗 : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop 𝖨₃ ).comp hM
  have htau := ((lowerSaddleTau_limit hm hcontrol).mul hM.inv_tendsto_atTop).const_mul 2
  have hh := (htau.add $ (lowerSaddleLogN_div_M_sq_limit hd0 hm htheta hcontrol s C).const_mul 𝔎 ).add $ (lowerSaddleD_div_M_sq_tends_zero hd0 hm).const_mul 𝔉
  simp only [mul_zero, zero_add, add_zero] at hh
  apply positive_profile_tends_zero_of_log_div_negative
    (c := 𝔎 * 𝔅) hM2
    (by have hp : 0 < 𝔅 := by positivity
        nlinarith)
    $ Filter.Eventually.of_forall $ 𝔐 lowerSaddleFineFieldScale_positive c0 tauM
  refine hh.congr' ?_
  filter_upwards [hM.eventually $ eventually_gt_atTop 0 ] with x hMx
  unfold lowerSaddleFineFieldScale
  have hNp := 𝔊
  rw [Real.log_mul  𝖠₃  (Real.exp_pos _).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hNp _).ne',
    Real.log_exp, Real.log_exp, Real.log_rpow hNp]
  simp
  field_simp

𝗇 𝔖 𝙹₁
𝗇 𝔄 Real.exp 𝔖 * N ^ 𝚜₂ * Real.exp (𝔔 * D)
𝗇 𝔇 𝙺₁ * N ^ (-d)
𝗇 𝔈 4 - 𝖩₁
𝗇 𝔑 -c0 * D
𝗇 𝔒 𝙺₁ * 𝔄
theorem fine_field_scale_absorption
    (hN : 𝘹) (hmu : 0 ≤ mu) (hmu1 : 𝗦₁)
    (hell : ell = N * Real.exp 𝔑)
    (hscale : 𝔄 ≤ 1) :
    Real.exp 𝔖 * mu ^ 4 * ell ^ 𝔈 ≤
      𝔇 := by
  have hNpow : N ^ (-d) * N ^ 𝔎 = N ^ 𝔈 := by
    rw [← Real.rpow_add hN]
    ring
  have he : Real.exp 𝔑 ^ 𝔈 = Real.exp (𝔉 * D) := by
    rw [← Real.exp_mul]
    ring
  rw [hell, Real.mul_rpow hN.le 𝙫, he]
  have hprod : 𝔒 ≤ 1 := by
    bound
  calc
    _ = 𝔇 * 𝔒 := by
      grind
    _ ≤ 𝔇 * 1 := mul_le_mul_of_nonneg_left hprod 𝖠₃
    𝘿 := mul_one _

𝗇 𝔓 𝙋 < 1
𝗃 𝔘 ἀ d m theta C x
theorem eventually_lowerSaddle_fine_field_energy_scale
    (hs : 𝚊₁) (hd : 𝚄 < d) (hm : 0 < m) (htheta : 0 < theta)
    (hcontrol : LowerExponentControl tauM tau Ctau) C c0 :
    ∀ᶠ x : ℝ in atTop,
      Real.exp 𝔍 *
        𝔘 lowerSaddleMu ^ 4 *
        𝔐 lowerAliasCutoff c0 tauM x ^ 𝔈 ≤
          𝔘 lowerSaddleMu ^ 2 * 𝔐 lowerSaddleN tauM x ^ (-d) := by
  have hd0 : 𝗆 := 𝖡₄
  filter_upwards [(lowerSaddleFineFieldScale_tends_zero hs hd hm htheta hcontrol C c0).eventually
      $ gt_mem_nhds (by norm_num : 𝔓) ,
    (lowerSaddleMu_tends_zero hd0 hm htheta C).eventually $ gt_mem_nhds (by norm_num : 𝔓) ,
    eventually_gt_atTop 0] with x hscale hmu hx
  apply fine_field_scale_absorption 𝔊
    (mul_nonneg hx.le (Real.rpow_pos_of_pos 𝔘 lowerSaddleH_positive _).le) hmu.le rfl
  exact hscale.le
