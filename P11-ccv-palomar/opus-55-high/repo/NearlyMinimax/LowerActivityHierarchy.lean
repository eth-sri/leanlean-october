module

public import NearlyMinimax.LowerSaddle
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual source activity hierarchy for the rounded lower saddle. These
numeric theorems derive small row ratios and legal fine targets from fixed
parameters, rather than assuming an activity estimate. -/
𝚷
𝚶
𝚨

𝗃 𝕳 0 < ἀ
𝗃 𝕻 (ἀ : ℝ)
section

variable {f M : 𝘓}
    {c }
    (hM : Tendsto M atTop atTop)

include hM

𝗇 𝔤 fun x => Real.log (f x) / M x
𝗇 𝔯 ∀ᶠ x in atTop, 0 < f x
/-- A positive polynomial-scale profile has logarithm negligible against the scale. -/
theorem log_profile_div_scale_tends_zero p (hc : 𝕳 c)
    (hf : 𝔯)
    (hr : Tendsto (fun x => f x / M x ^p) atTop $ 𝓝 c ) :
    Tendsto 𝔤 atTop $ 𝓝 0 := by
  have hlog := (Real.continuousAt_log hc.ne').tendsto.comp hr
  have hfirst := hlog.mul hM.inv_tendsto_atTop
  have hh := hfirst.add $ (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hM).const_mul 𝕻 p
  simp only [mul_zero, add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [hf, hM.eventually $ eventually_gt_atTop 0 ] with x hx hMx
  simp
  rw [Real.log_div hx.ne' (pow_pos hMx p).ne', Real.log_pow]
  ring

theorem positive_profile_tends_zero_of_log_div_negative
    (hc : c < 0) (hf : 𝔯)
    (hr : Tendsto 𝔤 atTop $ 𝓝 c ) :
    Tendsto f atTop $ 𝓝 0 := by
  have hh := Real.tendsto_exp_atBot.comp $ tendsto_atBot_of_div_negative hM hr hc
  refine hh.congr' $ hf.mono fun x hx => Real.exp_log hx

end

𝗃 𝕯 ἀ s d m θ C
𝗇 𝔒 𝕯 lowerSaddleN τM x
𝗇 𝔫 𝙜
def lowerAliasH (s d m θ C : ℝ) (τM : 𝔫) (x : ℝ) : ℝ :=
  1 + Real.log 𝔒

𝗇 𝔄 𝕯 lowerAliasH τM x
𝗇 𝔇 𝙵
𝗇 𝔓 lowerSaddleMu d m θ C x
𝗇 𝔥 a/d
𝗇 𝔲 𝔓 * 𝔄
𝗇 𝔳 𝕻 𝔇
def lowerAliasQ (s d m θ C Cact a : ℝ) (τM : 𝔫) (x : ℝ) : ℝ :=
  Cact * 𝔳 * 𝔄 *
    𝔲^𝔥

𝗇 𝕶 -c0 * 𝔇
def lowerAliasCutoff (s d m θ C c0 : ℝ) (τM : 𝔫) (x : ℝ) : ℝ :=
  𝔒 * Real.exp 𝕶

def lowerAliasTargetScale (s d m θ C : ℝ) (τM : 𝔫) (r : ℕ) (x : ℝ) : ℝ :=
  𝔒 *
    𝔲^((𝕻 r-2)/d)

variable {s d m θ τ Cτ : ℝ} {τM : 𝔫}

𝗇 𝔔 𝚄 < d
𝗇 𝔘 LowerExponentControl τM τ Cτ
𝗇 𝔙 𝕳 m
𝗇 𝔞 𝕳 θ
𝗇 𝔠 𝚊₁
𝗃 𝕮 ἀ hs hd hm hθ hcontrol
𝗃 𝕰 ∀ᶠ x in atTop, 0 < ἀ
𝗃 𝖁 𝕮 ἀ C
theorem lowerAliasH_eventually_positive
    (hs : 𝔠) (hd : 𝔔) (hm : 𝔙) (hθ : 𝔞)
    (hcontrol : 𝔘) C :
    𝕰 𝔄 := by
  filter_upwards [(𝖁 lowerSaddleN_tendsto_atTop).eventually
    $ eventually_gt_atTop 1 ] with x hx
  unfold lowerAliasH
  linarith [Real.log_pos hx]

𝗇 𝔈 (d-𝚄)/(d*𝙾₁) /m^2
𝗇 𝔉 𝗫
𝗇 𝔚 𝕳 d
𝗃 𝕾 fun x => ἀ / 𝔉^2
theorem lowerAliasH_div_M_sq_limit
    (hd : 𝔚) (hm : 𝔙) (hθ : 𝔞)
    (hcontrol : 𝔘) s C :
    Tendsto 𝕾 𝔄
      atTop $ 𝓝 𝔈 := by
  have h0 := (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.pow 2
  have hh := h0.add $ lowerSaddleLogN_div_M_sq_limit hd hm hθ hcontrol s C
  simp at hh
  convert hh using 1
  funext x
  simp only [lowerAliasH, add_div, one_div]

𝗇 𝔊 𝖁 lowerAliasH_eventually_positive
𝗃 𝕱 Tendsto (fun x => Real.log ἀ / 𝔉) atTop
𝗃 𝕼 ἀ hd0 hm
𝗃 𝕿 ἀ $ lowerSaddleM_tendsto_atTop hm
theorem log_lowerAliasH_div_M_tends_zero
    (hs : 𝔠) (hd : 𝔔) (hm : 𝔙) (hθ : 𝔞)
    (hcontrol : 𝔘) C :
    𝕱 𝔄 $ 𝓝 0 := by
  have hd0 : 𝔚 := 𝖡₄
  apply 𝕿 log_profile_div_scale_tends_zero 2
    (by positivity : 𝕳 𝔈)
    𝔊
  exact 𝕼 lowerAliasH_div_M_sq_limit hθ hcontrol s C

𝗇 𝔐 𝘂₂ $ eventually_gt_atTop 0
𝗇 𝕺 𝙶
theorem log_lowerSaddleD_div_M_tends_zero (hd : 𝔚) (hm : 𝔙) :
    𝕱 𝔇 $ 𝓝 0 := by
  have hpos : 𝕰 𝔳 := by
    filter_upwards [𝔐] with x hx
    exact lt_of_lt_of_le  𝖠₃  $ Nat.le_ceil _
  exact 𝕿 log_profile_div_scale_tends_zero 1
    (by linarith : 0 < 𝕺) hpos $ by simpa only [pow_one] using lowerSaddleD_div_M_limit hd hm

𝗇 𝔑 𝖁 log_lowerAliasH_div_M_tends_zero
𝗇 𝔩 (Real.exp_pos _).ne'
section

variable (hs : 𝔠)
    (hd : 𝔔)
    (hm : 𝔙)
    (hθ : 𝔞)
    (hcontrol : 𝔘)

include hs hd hm hθ hcontrol

/-- The exact source product mu*H has strictly negative logarithmic slope. -/
theorem lowerAliasMuH_log_div_M_limit C :
    𝕱 𝔲 $ 𝓝 $ -θ := by
  have hh := (lowerSaddleOmega_div_M_limit (d := d)  𝖡₄  hm hθ C).neg.add
    𝔑
  simp at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 0, 𝔊]
    with x hx hH
  rw [lowerSaddleMu_eq_exp hx, Real.log_mul 𝔩 hH.ne', Real.log_exp]
  ring

theorem lowerAliasMuH_tends_zero C :
    Tendsto (fun x => 𝔲) atTop $ 𝓝 0 := by
  apply 𝕿 positive_profile_tends_zero_of_log_div_negative
    $ neg_neg_of_pos hθ
  · filter_upwards [eventually_gt_atTop 0, 𝔊] with x hx hH
    rw [lowerSaddleMu_eq_exp hx]
    positivity
  · exact 𝖁 lowerAliasMuH_log_div_M_limit

end

theorem lowerSaddleD_eventually_positive (hd : 𝔚) (hm : 𝔙) :
    𝕰 𝔳 := by
  filter_upwards [𝔐] with x hx
  exact lt_of_lt_of_le  𝖠₃  $ Nat.le_ceil _

𝗇 𝕬 𝕯 lowerAliasQ Cact
𝗇 𝔍 𝕬 1 τM x
𝗇 𝔖 lowerSaddleOmega d m θ C x
𝗇 𝔗 𝙋<1
𝗇 𝔛 𝖁 lowerAliasMuH_eventually_positive
𝗇 𝔦 𝕼 lowerSaddleD_eventually_positive
𝗇 𝔧 (𝕼 lowerSaddleOmega_div_M_limit hθ C).sub
𝗇 𝔬 𝕳 Cact
𝗇 𝔰 𝕬 2 τM x
𝗃 𝖃 mul_pos ἀ hD
section

variable (hs : 𝔠)
    (hd : 𝔔)
    (hm : 𝔙)
    (hθ : 𝔞)
    (hcontrol : 𝔘)

include hs hd hm hθ hcontrol

theorem lowerAliasMuH_eventually_positive C :
    𝕰 𝔲 := by
  filter_upwards [eventually_gt_atTop 0, 𝔊] with x hx hH
  rw [lowerSaddleMu_eq_exp hx]
  positivity

𝗇 𝔜 𝕬 a τM x
/-- Every fixed target exponent a has the exact negative exponential slope -a*theta/d. -/
theorem lowerAliasQ_log_div_M_limit
    (hCact : 𝔬) C a :
    𝕱 𝔜 $ 𝓝 $ -θ * 𝔥 := by
  have hd0 : 𝔚 := 𝖡₄
  have hc := (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.const_mul $ Real.log Cact
  have hh := ((hc.add 𝕼 log_lowerSaddleD_div_M_tends_zero).add
    𝔑).add
      $ (𝖁 lowerAliasMuH_log_div_M_limit).const_mul 𝔥
  simp only [mul_zero, zero_add, mul_comm 𝔥] at hh
  refine hh.congr' ?_
  filter_upwards [𝔦,
    𝔊,
    𝔛] with x hD hH hbase
  simp
  unfold lowerAliasQ
  rw [Real.log_mul (mul_pos 𝖃 hCact hH).ne' (Real.rpow_pos_of_pos hbase _).ne',
    Real.log_mul (𝖃 hCact).ne' hH.ne', Real.log_mul hCact.ne' hD.ne', Real.log_rpow hbase]
  ring

𝗇 𝔡 𝕿 positive_profile_tends_zero_of_log_div_negative $ mul_neg_of_neg_of_pos (neg_neg_of_pos hθ) $ div_pos ha hd0
𝗇 𝔭 𝕮 lowerAliasQ_log_div_M_limit hCact C a
theorem lowerAliasQ_tends_zero
    {Cact a } (hCact : 𝔬) (ha : 𝕳 a) C :
    Tendsto (𝕬 a τM) atTop $ 𝓝 0 := by
  have hd0 : 𝔚 := 𝖡₄
  apply 𝔡
  · filter_upwards [𝔦,
      𝔊,
      𝔛] with x hD hH hbase
    unfold lowerAliasQ
    positivity
  · exact 𝔭

theorem lowerAliasD_sq_Q_tends_zero
    {Cact a } (hCact : 𝔬) (ha : 𝕳 a) C :
    Tendsto (fun x => 𝔇^2 * 𝔜)
      atTop $ 𝓝 0 := by
  have hd0 : 𝔚 := 𝖡₄
  have hh := ((𝕼 log_lowerSaddleD_div_M_tends_zero).const_mul 2).add
    𝔭
  simp only [mul_zero, zero_add] at hh
  have hqpos : 𝕰 𝔜 := by
    filter_upwards [𝔦,
      𝔊,
      𝔛] with x hD hH hbase
    unfold lowerAliasQ
    positivity
  apply 𝔡
  · filter_upwards [𝔦, hqpos] with x hD hQ
    positivity
  · refine hh.congr' ?_
    filter_upwards [𝔦, hqpos] with x hD hQ
    rw [Real.log_mul (sq_pos_of_pos hD).ne' hQ.ne', Real.log_pow]
    ring

/-- All source row-ratio smallness conditions follow eventually for fixed Cact. -/
theorem eventually_lowerAlias_row_smallness
    (hCact : 𝔬) C :
    ∀ᶠ x in atTop,
      𝔲 ≤ 1 ∧
      Real.log 𝔄 ≤ 𝔉 ∧
      2 * Real.log 𝔄 < 𝔖 ∧
      𝔰 ≤ 𝔍 ∧
      𝔍 ≤ 𝙖 ∧
      𝔇^2 * 𝔍 ≤ 1 := by
  have hd0 : 𝔚 := 𝖡₄
  have hgap := 𝔧
    $ (𝔑).const_mul 2
  simp at hgap
  filter_upwards [
    (𝖁 lowerAliasMuH_tends_zero).eventually $ gt_mem_nhds (by norm_num : 𝔗) ,
    (𝔑).eventually $ gt_mem_nhds (by norm_num : 𝔗) ,
    hgap.eventually $ lt_mem_nhds hθ ,
    (𝕮 lowerAliasQ_tends_zero hCact (by norm_num : 𝔗) C).eventually
      $ gt_mem_nhds (by norm_num : 𝙋<𝙖) ,
    (𝕮 lowerAliasD_sq_Q_tends_zero hCact (by norm_num : 𝔗) C).eventually
      $ gt_mem_nhds (by norm_num : 𝔗) ,
    𝔐,
    𝔛,
    𝔦, 𝔊]
    with x hbase hlog hgap hq hsmall hM hbase0 hD hH
  refine ⟨hbase.le, by simpa only [one_mul] using ((div_lt_iff₀ hM).1 hlog).le, ?_, ?_, hq.le, hsmall.le⟩
  · exact (div_lt_div_iff_of_pos_right hM).mp 𝖤₃
  · unfold lowerAliasQ
    bound

end

𝗇 𝕷 𝕻 𝔉^2
theorem lowerSaddleM_sq_tendsto_atTop (hm : 𝔙) :
    Tendsto (fun x => 𝕷) atTop atTop := by
  simpa only [pow_two] using (lowerSaddleM_tendsto_atTop hm).atTop_mul_atTop₀ $ lowerSaddleM_tendsto_atTop hm

𝗃 𝕲 Tendsto (fun x => Real.log ἀ / 𝔉^2) atTop
𝗃 𝖂 fun x => 𝔇 / ἀ
section

variable (hd : 𝔚)
    (hm : 𝔙)

include hd hm

𝗃 𝖀 (ἀ hd hm).mul (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop
theorem lowerSaddleD_div_M_sq_tends_zero :
    Tendsto 𝖂 𝕷 atTop $ 𝓝 0 := by
  have hh := 𝖀 lowerSaddleD_div_M_limit
  simp at hh
  grind

theorem log_lowerSaddleD_div_M_sq_tends_zero :
    𝕲 𝔇 $ 𝓝 0 := by
  have hh := 𝖀 log_lowerSaddleD_div_M_tends_zero
  simp at hh
  grind

end

𝗇 𝕭 𝕯 lowerAliasCutoff c0 τM
𝗇 𝔎 𝕭 x
𝗃 𝕽 ἀ+1
section

variable (hs : 𝔠)
    (hd : 𝔔)
    (hm : 𝔙)
    (hθ : 𝔞)
    (hcontrol : 𝔘)

include hs hd hm hθ hcontrol

𝗇 𝔮 (𝕼 lowerSaddleD_div_M_sq_tends_zero).const_mul c0
𝗇 𝕴 𝕼 lowerSaddleLogN_div_M_sq_limit hθ hcontrol s C
/-- The exponential cutoff still tends to infinity: log N is quadratic, D only linear. -/
theorem lowerAliasCutoff_tendsto_atTop C c0 :
    Tendsto 𝕭 atTop atTop := by
  have hd0 : 𝔚 := 𝖡₄
  have hh := (𝕴).sub
    𝔮
  simp at hh
  have hlog : 𝕲 𝔎 $ 𝓝 𝔈 := by
    convert hh using 1
    funext x
    rw [lowerAliasCutoff, Real.log_mul (lowerSaddleN_positive ..).ne' 𝔩, Real.log_exp]
    ring
  have hdiv := (lowerSaddleM_sq_tendsto_atTop hm).atTop_mul_pos  𝖠₃  hlog
  have ht : Tendsto (fun x => Real.log 𝔎) atTop atTop := by
    refine hdiv.congr' ?_
    filter_upwards [𝔐] with x hx
    field_simp
  convert Real.tendsto_exp_atTop.comp ht using 1
  funext x
  exact (Real.exp_log $ mul_pos (lowerSaddleN_positive ..) $ Real.exp_pos _ ).symm

𝗇 𝔪 mul_pos 𝖃 hCs $ Real.exp_pos _
𝗇 𝔷 Cs * 𝔇 * Real.exp (c0*𝕽 𝔇)
/-- Every fixed singleton representation cost is absorbed by actual N. -/
theorem lowerAliasSingleton_ratio_tends_zero
    {Cs } (hCs : 𝕳 Cs) C c0 :
    Tendsto (fun x => 𝔷 / 𝔒)
      atTop $ 𝓝 0 := by
  have hd0 : 𝔚 := 𝖡₄
  have hA : 𝕳 𝔈 := 𝖠₃
  have hconst : 𝕲 Cs $ 𝓝 0 := by
    simpa only [Pi.inv_apply, div_eq_mul_inv, mul_zero] using (lowerSaddleM_sq_tendsto_atTop hm).inv_tendsto_atTop.const_mul $ Real.log Cs
  have hconstc : Tendsto 𝕾 c0 atTop $ 𝓝 0 := by
    simpa only [Pi.inv_apply, div_eq_mul_inv, mul_zero] using (lowerSaddleM_sq_tendsto_atTop hm).inv_tendsto_atTop.const_mul c0
  have hh := (((hconst.add 𝕼 log_lowerSaddleD_div_M_sq_tends_zero).add
    𝔮).add hconstc).sub
      𝕴
  simp at hh
  apply positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_sq_tendsto_atTop hm) $ neg_neg_of_pos hA
  · filter_upwards [𝔦] with x hD
    exact div_pos 𝔪 $ lowerSaddleN_positive ..
  · refine hh.congr' ?_
    filter_upwards [𝔦] with x hD
    rw [Real.log_div (𝔪).ne' (lowerSaddleN_positive ..).ne',
      Real.log_mul (𝖃 hCs).ne' 𝔩, Real.log_mul hCs.ne' hD.ne', Real.log_exp]
    ring

theorem eventually_lowerAlias_singleton_le
    (hCs : 𝕳 Cs) C c0 :
    ∀ᶠ x in atTop, 𝔷 ≤ 𝔒 := by
  filter_upwards [(𝕮 lowerAliasSingleton_ratio_tends_zero hCs C c0).eventually
    $ gt_mem_nhds (by norm_num : 𝔗) ] with x hx
  simpa only [one_mul] using ((div_lt_iff₀ $ lowerSaddleN_positive .. ).1 hx).le

end

𝗇 𝔅 Real.exp (τM 𝗫 * 𝙵) * 𝕭 x / 𝕯 lowerSaddleN τM x
𝗇 𝔱 𝕯 lowerSaddleN_positive τM x
𝗇 𝕸 τM 𝔉 ≤ c0
/-- Exact source coarse-cutoff cancellation; no extra exponential in M is introduced. -/
theorem lowerAlias_coarse_ratio_le
    (hτ : 𝕸) :
    𝔅 ≤ 1 := by
  have he : 𝔅 =
      Real.exp ((τM 𝔉-c0)*𝔇) := by
    unfold lowerAliasCutoff
    calc
      _ = Real.exp (τM 𝔉 * 𝔇) * Real.exp 𝕶 := by
        field_simp [(𝔱).ne']
      𝘿 := by rw [← Real.exp_add]; ring

  rw [he]
  exact Real.exp_le_one_iff.mpr $ mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hτ) $ Nat.cast_nonneg _

theorem eventually_lowerAlias_cutoff_guards
    (hs : 𝔠) (hd : 𝔔) (hm : 𝔙) (hθ : 𝔞)
    (hcontrol : 𝔘) (hc0 : τ < c0) C :
    ∀ᶠ x in atTop, 1 < 𝔎 ∧
      𝕸 ∧
      𝔅 ≤ 1 := by
  filter_upwards [(𝖁 lowerAliasCutoff_tendsto_atTop c0).eventually
    $ eventually_gt_atTop 1 , (lowerSaddleTau_limit hm hcontrol).eventually $ gt_mem_nhds hc0 ] with x hell hτ
  exact ⟨hell, hτ.le, lowerAlias_coarse_ratio_le hτ.le⟩

𝗇 𝔢 d*c0
𝗇 𝔣 ω - Real.log H
𝗇 𝔨 r-2
𝗇 𝕹 -ω + Real.log H
/-- Exact scalar fine-band count restriction, obtained by taking logarithms
of the actual target scale above the common cutoff. -/
theorem fine_target_count_lt
    (hN : 𝕳 N) (hbase : 𝕳 base) (hd : 𝔚)
    (hgap : 𝕳 𝔣) (hlog : Real.log base = 𝕹)
    (hactive : 𝗐 < N * base^(𝔨/d)) :
    r < 2 + 𝔢*D/𝔣 := by
  have hln := Real.log_lt_log (Real.exp_pos _) $ (mul_lt_mul_iff_right₀ hN).mp hactive
  rw [Real.log_exp, Real.log_rpow hbase, hlog] at hln
  have he : 𝔨/d * 𝕹 *d = -𝔨*𝔣 := by
    grind
  have hp : 𝔨*𝔣 < 𝔢*D := 𝖥₃
  have hv := (lt_div_iff₀ hgap).2 hp
  linarith

𝗇 𝔏 𝕺/θ
𝗇 𝔵 𝔖 - Real.log 𝔄
/-- The ratio controlling all fine targets has a fixed finite limit. -/
theorem lowerAliasD_div_gap_limit
    (hs : 𝔠) (hd : 𝔔) (hm : 𝔙) (hθ : 𝔞)
    (hcontrol : 𝔘) C :
    Tendsto 𝖂 𝔵
      atTop $ 𝓝 𝔏 := by
  have hd0 : 𝔚 := 𝖡₄
  have hgap := 𝔧
    𝔑
  simp at hgap
  have hh := (𝕼 lowerSaddleD_div_M_limit).div hgap hθ.ne'
  refine hh.congr' ?_
  filter_upwards [𝔐] with x hx
  simp only [Pi.div_apply, ← sub_div, div_div_div_cancel_right₀ hx.ne']

𝗇 𝔴 3 + 𝔢*𝕽 𝔏
/-- One fixed rounded integer bounds every nonzero fine-band target. -/
def lowerAliasFineTargetBound (d θ c0 : ℝ) : ℕ :=
  Nat.ceil 𝔴

𝗇 𝔟 lowerAliasFineTargetBound d θ c0
𝗇 𝔶 𝔎 < 𝕯 lowerAliasTargetScale τM r x → r ≤ 𝔟
theorem eventually_lowerAlias_fine_targets
    (hs : 𝔠) (hd : 𝔔) (hm : 𝔙) (hθ : 𝔞)
    (hcontrol : 𝔘) (hc0 : 𝕳 c0) C :
    ∀ᶠ x in atTop,
      𝔟 ≤ 𝔉 ∧
      ∀ r , 𝔶 := by
  have hd0 : 𝔚 := 𝖡₄
  have hglim := 𝔧
    𝔑
  simp at hglim
  have hh := ((𝖁 lowerAliasD_div_gap_limit).const_mul 𝔢).const_add 2
  have hmargin : 2 + 𝔢*𝔏 < 𝔴 := 𝖥₃
  filter_upwards [hh.eventually $ gt_mem_nhds hmargin ,
    (lowerSaddleM_nat_tendsto_atTop hm).eventually $ eventually_ge_atTop 𝔟 ,
    hglim.eventually $ lt_mem_nhds hθ ,
    𝔐,
    𝔛,
    𝔊, eventually_gt_atTop 0]
    with x hthreshold hM hgapnorm hMpos hbase hH hx
  refine ⟨hM, fun r hr => ?_⟩
  have hlog : Real.log 𝔲 =
      -𝔖 + Real.log 𝔄 := by
    rw [lowerSaddleMu_eq_exp hx, Real.log_mul 𝔩 hH.ne', Real.log_exp]
  have hgap : 𝕳 𝔵 := by
    have hg : 0 < 𝔵 / 𝔉 := by
      grind
    simp_all
  have hrlt := fine_target_count_lt 𝔱 hbase hd0 hgap hlog hr
  have hbound : r < 𝕻 𝔟 := by
    apply hrlt.trans
    have hthr : 2 + 𝔢*𝔇 /
        𝔵 <
        𝔴 := 𝖤₃
    exact hthr.trans_le $ Nat.le_ceil _
  exact Nat.le_of_lt $ by exact_mod_cast hbound

/-- The complete source activity hierarchy, with a fixed target-count bound. -/
def LowerAliasHierarchy (s d m θ C Cact Cs c0 : ℝ) (τM : 𝔫) (x : ℝ) : Prop :=
  1 < 𝔎 ∧
  𝕸 ∧
  𝔲 ≤ 1 ∧
  Real.log 𝔄 ≤ 𝔉 ∧
  2 * Real.log 𝔄 < 𝔖 ∧
  𝔰 ≤ 𝔍 ∧
  𝔍 ≤ 𝙖 ∧
  𝔳^2 * 𝔍 ≤ 1 ∧
  𝔅 ≤ 1 ∧
  Cs * 𝔳 * Real.exp (c0*𝕽 𝔳) ≤
    𝔒 ∧
  𝔟 ≤ 𝔉 ∧
  ∀ r : ℕ, 𝔶

section

variable (hs : 𝔠)
    (hd : 𝔔)

include hs hd

theorem eventually_lowerAlias_hierarchy
    (hm : 𝔙) (hθ : 𝔞)
    (hcontrol : 𝔘)
    (hCact : 𝔬) (hCs : 𝕳 Cs) (hc0 : 𝕳 c0) (hτc0 : τ < c0) C :
    ∀ᶠ x in atTop, 𝕯 LowerAliasHierarchy Cact Cs c0 τM x := by
  filter_upwards [𝕮 eventually_lowerAlias_row_smallness hCact C,
    𝕮 eventually_lowerAlias_cutoff_guards hτc0 C,
    𝕮 eventually_lowerAlias_singleton_le hCs C c0,
    𝕮 eventually_lowerAlias_fine_targets hc0 C]
    with x hrow hcut hsingle hfine
  rcases hrow with ⟨hbase,hlog,hgap,hq21,hq1,hDq⟩
  exact ⟨hcut.1,hcut.2.1,hbase,hlog,hgap,hq21,hq1,hDq,hcut.2.2,hsingle,hfine⟩

𝗇 𝕵 𝘦₂
/-- The entire hierarchy holds for the paper's actual canonical M, grid,
mu, N and shrunk density endpoints, with c0=tau+1 and fixed representation
constants. The displayed activity bounds are consequences, not premises. -/
theorem actual_lowerAlias_hierarchy
    (ha : 𝕳 a) (hab : 𝙭)
    (hCact : 𝔬) (hCs : 𝕳 Cs) C :
    ∀ᶠ x in atTop,
      LowerAliasHierarchy s d
        (lowerSaddleCoefficient s d 𝕵)
        (lowerSaddleTheta s d 𝕵) C Cact Cs
        𝕽 𝕵 𝙉₂ x := by
  have hτ := densityIntervalExponent_pos ha hab
  obtain ⟨Cτ,_,hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  exact eventually_lowerAlias_hierarchy hs hd (lowerSaddleCoefficient_pos hs hd hτ)
    (lowerSaddleTheta_pos hs hd hτ) hcontrol hCact hCs  𝖡₄   𝖡₄  C
