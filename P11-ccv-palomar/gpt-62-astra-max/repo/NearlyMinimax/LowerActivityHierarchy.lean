module

public import NearlyMinimax.LowerSaddle


@[expose] public section

/-! Actual source activity hierarchy for the rounded lower saddle. These
numeric theorems derive small row ratios and legal fine targets from fixed
parameters, rather than assuming an activity estimate. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section
variable {f M : ℝ → ℝ} {c : ℝ} (hM : Tendsto M atTop atTop)
include hM

/-- A positive polynomial-scale profile has logarithm negligible against the scale. -/
theorem log_profile_div_scale_tends_zero (p : ℕ) (hc : 0 < c)
    (hf : ∀ᶠ x in atTop, 0 < f x)
    (hr : Tendsto (fun x => f x / (M x)^p) atTop (𝓝 c)) :
    Tendsto (fun x => Real.log (f x) / M x) atTop (𝓝 0) := by
  have hh := (((Real.continuousAt_log hc.ne').tendsto.comp hr).mul hM.inv_tendsto_atTop).add ((Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hM).const_mul (p : ℝ))
  simp only [mul_zero, add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [hf, hM.eventually (eventually_gt_atTop 0)] with x hx hMx
  simp
  rw [Real.log_div hx.ne' (pow_pos hMx p).ne', Real.log_pow]
  ring

theorem positive_profile_tends_zero_of_log_div_negative (hc : c < 0) (hf : ∀ᶠ x in atTop, 0 < f x)
    (hr : Tendsto (fun x => Real.log (f x) / M x) atTop (𝓝 c)) :
    Tendsto f atTop (𝓝 0) := by
  refine (Real.tendsto_exp_atBot.comp (tendsto_atBot_of_div_negative hM hr hc)).congr' (hf.mono fun x hx => Real.exp_log hx)

end

section
variable (s d m θ C Cact a c0 : ℝ) (τM : ℕ → ℝ) (r : ℕ) (x : ℝ)

def lowerAliasH : ℝ :=
  1 + Real.log (lowerSaddleN s d m θ C τM x)

def lowerAliasQ : ℝ :=
  Cact * (lowerSaddleD d m x) * lowerAliasH s d m θ C τM x *
    (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x)^(a/d)

def lowerAliasCutoff : ℝ :=
  lowerSaddleN s d m θ C τM x * Real.exp (-c0 * lowerSaddleD d m x)

def lowerAliasTargetScale : ℝ :=
  lowerSaddleN s d m θ C τM x *
    (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x)^((r-2)/d)

end

variable {s d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}

section
variable (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ) (hcontrol : LowerExponentControl τM τ Cτ)
    {Cact Cs : ℝ} (hCs : 0 < Cs) {a : ℝ} (hCact : 0 < Cact) (ha : 0 < a) (C c0 : ℝ)

include hs hd hm hθ hcontrol in
theorem lowerAliasH_eventually_positive
    :
    ∀ᶠ x in atTop, 0 < lowerAliasH s d m θ C τM x := by
  filter_upwards [(lowerSaddleN_tendsto_atTop hs hd hm hθ hcontrol C).eventually
    (eventually_gt_atTop 1)] with x hx
  unfold lowerAliasH
  linarith [Real.log_pos hx]

theorem lowerAliasH_div_M_sq_limit
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (s C : ℝ) :
    Tendsto (fun x => lowerAliasH s d m θ C τM x / (lowerSaddleM m x)^2)
      atTop (𝓝 (((d-4*s)/(d*(d+4)))/m^2)) := by
  have hh := ((lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.pow 2).add (lowerSaddleLogN_div_M_sq_limit hd hm hθ hcontrol s C)
  simp at hh
  convert hh using 1
  simp only [lowerAliasH, add_div, one_div, Pi.inv_apply, inv_pow]

include hs hd hm hθ hcontrol in
theorem log_lowerAliasH_div_M_tends_zero
    :
    Tendsto (fun x => Real.log (lowerAliasH s d m θ C τM x) / lowerSaddleM m x)
      atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  apply log_profile_div_scale_tends_zero (lowerSaddleM_tendsto_atTop hm) 2
    (by positivity : 0 < ((d-4*s)/(d*(d+4)))/m^2)
    (lowerAliasH_eventually_positive hs hd hm hθ hcontrol C)
  exact lowerAliasH_div_M_sq_limit hd0 hm hθ hcontrol s C

theorem log_lowerSaddleD_div_M_tends_zero (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun x => Real.log (lowerSaddleD d m x) / lowerSaddleM m x)
      atTop (𝓝 0) := by
  have hpos : ∀ᶠ x in atTop, 0 < (lowerSaddleD d m x : ℝ) := by
    filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0)] with x hx
    exact lt_of_lt_of_le (by positivity) (Nat.le_ceil _)
  exact log_profile_div_scale_tends_zero (lowerSaddleM_tendsto_atTop hm) 1
    (by linarith : 0 < (d+8)/4) hpos (by simpa using lowerSaddleD_div_M_limit hd hm)

include hs hd hm hθ hcontrol in
/-- The exact source product mu*H has strictly negative logarithmic slope. -/
theorem lowerAliasMuH_log_div_M_limit
    :
    Tendsto (fun x => Real.log (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x) /
      lowerSaddleM m x) atTop (𝓝 (-θ)) := by
  have hh := (lowerSaddleOmega_div_M_limit (d := d) (by linarith) hm hθ C).neg.add
    (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C)
  simp at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop 0, lowerAliasH_eventually_positive hs hd hm hθ hcontrol C]
    with x hx hH
  rw [lowerSaddleMu_eq_exp hx, Real.log_mul (Real.exp_pos _).ne' hH.ne', Real.log_exp]
  ring

include hs hd hm hθ hcontrol in
theorem lowerAliasMuH_tends_zero
    :
    Tendsto (fun x => lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x) atTop (𝓝 0) := by
  apply positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_tendsto_atTop hm)
    (neg_neg_of_pos hθ)
  · filter_upwards [eventually_gt_atTop 0, lowerAliasH_eventually_positive hs hd hm hθ hcontrol C] with x hx hH
    rw [lowerSaddleMu_eq_exp hx]
    positivity
  · exact lowerAliasMuH_log_div_M_limit hs hd hm hθ hcontrol C

theorem lowerSaddleD_eventually_positive (hd : 0 < d) (hm : 0 < m) :
    ∀ᶠ x in atTop, 0 < (lowerSaddleD d m x : ℝ) := by
  filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0)] with x hx
  exact lt_of_lt_of_le (by positivity) (Nat.le_ceil _)

include hs hd hm hθ hcontrol in
theorem lowerAliasMuH_eventually_positive
    :
    ∀ᶠ x in atTop, 0 < lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x := by
  filter_upwards [eventually_gt_atTop 0, lowerAliasH_eventually_positive hs hd hm hθ hcontrol C] with x hx hH
  rw [lowerSaddleMu_eq_exp hx]
  positivity

include hs hd hm hθ hcontrol hCact in
/-- Every fixed target exponent a has the exact negative exponential slope -a*theta/d. -/
theorem lowerAliasQ_log_div_M_limit
    (a : ℝ) :
    Tendsto (fun x => Real.log (lowerAliasQ s d m θ C Cact a τM x) / lowerSaddleM m x)
      atTop (𝓝 (-θ * (a/d))) := by
  have hd0 : 0 < d := by linarith
  have hh := ((((lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.const_mul (Real.log Cact)).add (log_lowerSaddleD_div_M_tends_zero hd0 hm)).add
    (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C)).add
      ((lowerAliasMuH_log_div_M_limit hs hd hm hθ hcontrol C).const_mul (a/d))
  simp only [mul_zero, zero_add, mul_comm (a/d)] at hh
  refine hh.congr' ?_
  filter_upwards [lowerSaddleD_eventually_positive hd0 hm,
    lowerAliasH_eventually_positive hs hd hm hθ hcontrol C,
    lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C] with x hD hH hbase
  simp
  unfold lowerAliasQ
  rw [Real.log_mul (mul_pos (mul_pos hCact hD) hH).ne' (Real.rpow_pos_of_pos hbase _).ne',
    Real.log_mul (mul_pos hCact hD).ne' hH.ne', Real.log_mul hCact.ne' hD.ne', Real.log_rpow hbase]
  ring

include hs hd hm hθ hcontrol hCact ha in
theorem lowerAliasQ_tends_zero
    :
    Tendsto (lowerAliasQ s d m θ C Cact a τM) atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  apply positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_tendsto_atTop hm)
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hθ) (div_pos ha hd0))
  · filter_upwards [lowerSaddleD_eventually_positive hd0 hm,
      lowerAliasH_eventually_positive hs hd hm hθ hcontrol C,
      lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C] with x hD hH hbase
    exact mul_pos (mul_pos (mul_pos hCact hD) hH) (Real.rpow_pos_of_pos hbase _)
  · apply lowerAliasQ_log_div_M_limit <;> assumption

include hs hd hm hθ hcontrol hCact ha in
theorem lowerAliasD_sq_Q_tends_zero
    :
    Tendsto (fun x => (lowerSaddleD d m x)^2 * lowerAliasQ s d m θ C Cact a τM x)
      atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  have hh := ((log_lowerSaddleD_div_M_tends_zero hd0 hm).const_mul 2).add
    (lowerAliasQ_log_div_M_limit hs hd hm hθ hcontrol hCact C a)
  simp only [mul_zero, zero_add] at hh
  have hqpos : ∀ᶠ x in atTop, 0 < lowerAliasQ s d m θ C Cact a τM x := by
    filter_upwards [lowerSaddleD_eventually_positive hd0 hm,
      lowerAliasH_eventually_positive hs hd hm hθ hcontrol C,
      lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C] with x hD hH hbase
    exact mul_pos (mul_pos (mul_pos hCact hD) hH) (Real.rpow_pos_of_pos hbase _)
  apply positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_tendsto_atTop hm)
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hθ) (div_pos ha hd0))
  · filter_upwards [lowerSaddleD_eventually_positive hd0 hm, hqpos] with x hD hQ
    positivity
  · refine hh.congr' ?_
    filter_upwards [lowerSaddleD_eventually_positive hd0 hm, hqpos] with x hD hQ
    rw [Real.log_mul (sq_pos_of_pos hD).ne' hQ.ne', Real.log_pow]
    ring

include hs hd hm hθ hcontrol hCact in
/-- All source row-ratio smallness conditions follow eventually for fixed Cact. -/
theorem eventually_lowerAlias_row_smallness
    :
    let aliasH := lowerAliasH s d m θ C τM
    let aliasQ := lowerAliasQ s d m θ C Cact
    ∀ᶠ x in atTop,
      lowerSaddleMu d m θ C x * aliasH x ≤ 1 ∧
      Real.log (aliasH x) ≤ lowerSaddleM m x ∧
      2 * Real.log (aliasH x) < lowerSaddleOmega d m θ C x ∧
      aliasQ 2 τM x ≤ aliasQ 1 τM x ∧
      aliasQ 1 τM x ≤ 1/2 ∧
      (lowerSaddleD d m x)^2 * aliasQ 1 τM x ≤ 1 := by
  have hd0 : 0 < d := by linarith
  have hgap := (lowerSaddleOmega_div_M_limit hd0 hm hθ C).sub
    ((log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C).const_mul 2)
  simp at hgap
  filter_upwards [
    (lowerAliasMuH_tends_zero hs hd hm hθ hcontrol C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hgap.eventually (lt_mem_nhds hθ),
    (lowerAliasQ_tends_zero hs hd hm hθ hcontrol hCact (by norm_num : (0 : ℝ)<1) C).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2)),
    (lowerAliasD_sq_Q_tends_zero hs hd hm hθ hcontrol hCact (by norm_num : (0 : ℝ)<1) C).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0),
    lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C,
    lowerSaddleD_eventually_positive hd0 hm, lowerAliasH_eventually_positive hs hd hm hθ hcontrol C]
    with x hbase hlog hgap hq hsmall hM hbase0 hD hH
  refine ⟨hbase.le, by simpa using ((div_lt_iff₀ hM).1 hlog).le, ?_, ?_, hq.le, hsmall.le⟩
  · exact (div_lt_div_iff_of_pos_right hM).mp (by simpa only [mul_div_assoc] using (sub_pos.mp hgap))
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hbase0 hbase.le (by apply div_le_div_of_nonneg_right (by norm_num) hd0.le))
      (by positivity)

include hm in
theorem lowerSaddleM_sq_tendsto_atTop :
    Tendsto (fun x => (lowerSaddleM m x : ℝ)^2) atTop atTop := by
  simpa only [pow_two] using (lowerSaddleM_tendsto_atTop hm).atTop_mul_atTop₀ (lowerSaddleM_tendsto_atTop hm)

theorem lowerSaddleD_div_M_sq_tends_zero (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun x => (lowerSaddleD d m x) / (lowerSaddleM m x : ℝ)^2) atTop (𝓝 0) := by
  have hh := (lowerSaddleD_div_M_limit hd hm).mul (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop
  simp at hh
  convert hh using 1
  simp [Pi.inv_apply, div_eq_mul_inv, pow_two, mul_inv, mul_assoc]

theorem log_lowerSaddleD_div_M_sq_tends_zero (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun x => Real.log (lowerSaddleD d m x) / (lowerSaddleM m x)^2) atTop (𝓝 0) := by
  have hh := (log_lowerSaddleD_div_M_tends_zero hd hm).mul (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop
  simp at hh
  convert hh using 1
  simp [Pi.inv_apply, div_eq_mul_inv, pow_two, mul_inv, mul_assoc]

include hs hd hm hθ hcontrol in
/-- The exponential cutoff still tends to infinity: log N is quadratic, D only linear. -/
theorem lowerAliasCutoff_tendsto_atTop
    :
    Tendsto (lowerAliasCutoff s d m θ C c0 τM) atTop atTop := by
  have hd0 : 0 < d := by linarith
  have hh := (lowerSaddleLogN_div_M_sq_limit hd0 hm hθ hcontrol s C).sub
    ((lowerSaddleD_div_M_sq_tends_zero hd0 hm).const_mul c0)
  simp at hh
  have hlog : Tendsto (fun x => Real.log (lowerAliasCutoff s d m θ C c0 τM x) /
      (lowerSaddleM m x)^2) atTop (𝓝 (((d-4*s)/(d*(d+4)))/m^2)) := by
    convert hh using 1
    funext x
    rw [lowerAliasCutoff, Real.log_mul (lowerSaddleN_positive ..).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have ht : Tendsto (fun x => Real.log (lowerAliasCutoff s d m θ C c0 τM x)) atTop atTop := by
    refine ((lowerSaddleM_sq_tendsto_atTop hm).atTop_mul_pos (by positivity) hlog).congr' ?_
    filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0)] with x hx
    field_simp <;> ring
  convert (Real.tendsto_exp_atTop.comp ht) using 1
  funext x
  exact (Real.exp_log (mul_pos (lowerSaddleN_positive ..) (Real.exp_pos _))).symm

include hs hd hm hθ hcontrol hCs in
/-- Every fixed singleton representation cost is absorbed by actual N. -/
theorem lowerAliasSingleton_ratio_tends_zero
    :
    Tendsto (fun x => Cs * (lowerSaddleD d m x) *
      Real.exp (c0*((lowerSaddleD d m x)+1)) / lowerSaddleN s d m θ C τM x)
      atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  have hA : 0 < ((d-4*s)/(d*(d+4)))/m^2 := by positivity
  have hconst : Tendsto (fun x => Real.log Cs / (lowerSaddleM m x)^2) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, div_eq_mul_inv, mul_zero] using (lowerSaddleM_sq_tendsto_atTop hm).inv_tendsto_atTop.const_mul (Real.log Cs)
  have hconstc : Tendsto (fun x => c0 / (lowerSaddleM m x)^2) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, div_eq_mul_inv, mul_zero] using (lowerSaddleM_sq_tendsto_atTop hm).inv_tendsto_atTop.const_mul c0
  have hh := (((hconst.add (log_lowerSaddleD_div_M_sq_tends_zero hd0 hm)).add
    ((lowerSaddleD_div_M_sq_tends_zero hd0 hm).const_mul c0)).add hconstc).sub
      (lowerSaddleLogN_div_M_sq_limit hd0 hm hθ hcontrol s C)
  simp at hh
  apply positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_sq_tendsto_atTop hm) (neg_neg_of_pos hA)
  · filter_upwards [lowerSaddleD_eventually_positive hd0 hm] with x hD
    exact div_pos (by positivity) (lowerSaddleN_positive ..)
  · refine hh.congr' ?_
    filter_upwards [lowerSaddleD_eventually_positive hd0 hm] with x hD
    rw [Real.log_div (mul_pos (mul_pos hCs hD) (Real.exp_pos _)).ne' (lowerSaddleN_positive ..).ne',
      Real.log_mul (mul_pos hCs hD).ne' (Real.exp_pos _).ne', Real.log_mul hCs.ne' hD.ne', Real.log_exp]
    ring

include hs hd hm hθ hcontrol hCs in
theorem eventually_lowerAlias_singleton_le
    :
    ∀ᶠ x in atTop, Cs * (lowerSaddleD d m x) *
      Real.exp (c0*((lowerSaddleD d m x)+1)) ≤ lowerSaddleN s d m θ C τM x := by
  filter_upwards [(lowerAliasSingleton_ratio_tends_zero hs hd hm hθ hcontrol hCs C c0).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ)<1))] with x hx
  simpa using ((div_lt_iff₀ (lowerSaddleN_positive ..)).1 hx).le

/-- Exact source coarse-cutoff cancellation; no extra exponential in M is introduced. -/
theorem lowerAlias_coarse_ratio_le {s d m θ C c0 x : ℝ} {τM : ℕ → ℝ}
    (hτ : τM (lowerSaddleM m x) ≤ c0) :
    let expScale := Real.exp (τM (lowerSaddleM m x) * lowerSaddleD d m x)
    expScale *
      lowerAliasCutoff s d m θ C c0 τM x / lowerSaddleN s d m θ C τM x ≤ 1 := by
  intro expScale
  have he : expScale *
      lowerAliasCutoff s d m θ C c0 τM x / lowerSaddleN s d m θ C τM x =
      Real.exp ((τM (lowerSaddleM m x)-c0)*lowerSaddleD d m x) := by
    unfold lowerAliasCutoff
    calc
      _ = expScale * Real.exp (-c0 * lowerSaddleD d m x) := by
        field_simp [(lowerSaddleN_positive s d m θ C τM x).ne']
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

  rw [he]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hτ) (Nat.cast_nonneg _))

include hs hd hm hθ hcontrol in
theorem eventually_lowerAlias_cutoff_guards
    {c0 : ℝ} (hc0 : τ < c0) (C : ℝ) :
    ∀ᶠ x in atTop, 1 < lowerAliasCutoff s d m θ C c0 τM x ∧
      τM (lowerSaddleM m x) ≤ c0 ∧
      Real.exp (τM (lowerSaddleM m x) * lowerSaddleD d m x) *
        lowerAliasCutoff s d m θ C c0 τM x / lowerSaddleN s d m θ C τM x ≤ 1 := by
  filter_upwards [(lowerAliasCutoff_tendsto_atTop hs hd hm hθ hcontrol C c0).eventually
    (eventually_gt_atTop 1), (lowerSaddleTau_limit hm hcontrol).eventually (gt_mem_nhds hc0)] with x hell hτ
  exact ⟨hell, hτ.le, lowerAlias_coarse_ratio_le hτ.le⟩

end

/-- Exact scalar fine-band count restriction, obtained by taking logarithms
of the actual target scale above the common cutoff. -/
theorem fine_target_count_lt {N base H ω d c0 D r : ℝ}
    (hN : 0 < N) (hbase : 0 < base) (hd : 0 < d)
    (hgap : 0 < ω - Real.log H) (hlog : Real.log base = -ω + Real.log H)
    (hactive : N * Real.exp (-c0*D) < N * base^((r-2)/d)) :
    r < 2 + d*c0*D/(ω-Real.log H) := by
  have hln := Real.log_lt_log (Real.exp_pos _) ((mul_lt_mul_iff_right₀ hN).mp hactive)
  rw [Real.log_exp, Real.log_rpow hbase, hlog] at hln
  have hm := mul_lt_mul_of_pos_right hln hd
  have he : ((r-2)/d * (-ω + Real.log H))*d = -(r-2)*(ω-Real.log H) := by
    field_simp [hd.ne']
    ring
  have hp : (r-2)*(ω-Real.log H) < d*c0*D := by nlinarith
  have hv := (lt_div_iff₀ hgap).2 hp
  linarith

section
variable (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ) (hcontrol : LowerExponentControl τM τ Cτ)
    {Cact Cs c0 : ℝ} (hCact : 0 < Cact) (hCs : 0 < Cs) (hc0 : 0 < c0) (hτc0 : τ < c0) (C : ℝ)

include hs hd hm hθ hcontrol in
/-- The ratio controlling all fine targets has a fixed finite limit. -/
theorem lowerAliasD_div_gap_limit
    :
    Tendsto (fun x => (lowerSaddleD d m x) /
      (lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x)))
      atTop (𝓝 (((d+8)/4)/θ)) := by
  have hd0 : 0 < d := by linarith
  have hgap := (lowerSaddleOmega_div_M_limit hd0 hm hθ C).sub
    (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C)
  simp at hgap
  refine ((lowerSaddleD_div_M_limit hd0 hm).div hgap hθ.ne').congr' ?_
  filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0)] with x hx
  simp [Pi.div_apply, ← sub_div, div_div_div_cancel_right₀ hx.ne']

/-- One fixed rounded integer bounds every nonzero fine-band target. -/
def lowerAliasFineTargetBound (d θ c0 : ℝ) : ℕ :=
  Nat.ceil (3 + d*c0*(((d+8)/4)/θ + 1))

include hs hd hm hθ hcontrol hc0 in
theorem eventually_lowerAlias_fine_targets
    :
    ∀ᶠ x in atTop,
      lowerAliasFineTargetBound d θ c0 ≤ lowerSaddleM m x ∧
      ∀ r, lowerAliasCutoff s d m θ C c0 τM x < lowerAliasTargetScale s d m θ C τM r x →
        r ≤ lowerAliasFineTargetBound d θ c0 := by
  have hd0 : 0 < d := by linarith
  have hglim := (lowerSaddleOmega_div_M_limit hd0 hm hθ C).sub
    (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C)
  simp at hglim
  have hh := ((lowerAliasD_div_gap_limit hs hd hm hθ hcontrol C).const_mul (d*c0)).const_add 2
  have hmargin : 2 + d*c0*(((d+8)/4)/θ) < 3 + d*c0*(((d+8)/4)/θ+1) := by nlinarith
  filter_upwards [hh.eventually (gt_mem_nhds hmargin),
    (lowerSaddleM_nat_tendsto_atTop hm).eventually (eventually_ge_atTop _),
    hglim.eventually (lt_mem_nhds hθ),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0),
    lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C,
    lowerAliasH_eventually_positive hs hd hm hθ hcontrol C, eventually_gt_atTop 0]
    with x hthreshold hM hgapnorm hMpos hbase hH hx
  refine ⟨hM, fun r hr => ?_⟩
  let logScale := Real.log (lowerAliasH s d m θ C τM x)
  have hgap : 0 < lowerSaddleOmega d m θ C x - logScale := by
    have hg : 0 < (lowerSaddleOmega d m θ C x - logScale) / lowerSaddleM m x := by
      simpa only [sub_div] using hgapnorm
    simpa using (lt_div_iff₀ hMpos).1 hg
  have hrlt := fine_target_count_lt (lowerSaddleN_positive s d m θ C τM x) hbase hd0 hgap (by
    rw [lowerSaddleMu_eq_exp hx, Real.log_mul (Real.exp_pos _).ne' hH.ne', Real.log_exp]) hr
  have hbound : r < (lowerAliasFineTargetBound d θ c0 : ℝ) := by
    apply hrlt.trans
    have hthr : 2 + d*c0*(lowerSaddleD d m x) /
        (lowerSaddleOmega d m θ C x - logScale) <
        3 + d*c0*(((d+8)/4)/θ+1) := by simpa only [mul_div_assoc] using hthreshold
    exact hthr.trans_le (Nat.le_ceil _)
  exact Nat.le_of_lt (by exact_mod_cast hbound)

/-- The complete source activity hierarchy, with a fixed target-count bound. -/
def LowerAliasHierarchy (s d m θ C Cact Cs c0 : ℝ) (τM : ℕ → ℝ) (x : ℝ) : Prop :=
  1 < lowerAliasCutoff s d m θ C c0 τM x ∧
  τM (lowerSaddleM m x) ≤ c0 ∧
  lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x ≤ 1 ∧
  Real.log (lowerAliasH s d m θ C τM x) ≤ lowerSaddleM m x ∧
  2 * Real.log (lowerAliasH s d m θ C τM x) < lowerSaddleOmega d m θ C x ∧
  lowerAliasQ s d m θ C Cact 2 τM x ≤ lowerAliasQ s d m θ C Cact 1 τM x ∧
  lowerAliasQ s d m θ C Cact 1 τM x ≤ 1/2 ∧
  (lowerSaddleD d m x)^2 * lowerAliasQ s d m θ C Cact 1 τM x ≤ 1 ∧
  Real.exp (τM (lowerSaddleM m x) * lowerSaddleD d m x) *
    lowerAliasCutoff s d m θ C c0 τM x / lowerSaddleN s d m θ C τM x ≤ 1 ∧
  Cs * (lowerSaddleD d m x) * Real.exp (c0*((lowerSaddleD d m x)+1)) ≤
    lowerSaddleN s d m θ C τM x ∧
  lowerAliasFineTargetBound d θ c0 ≤ lowerSaddleM m x ∧
  ∀ r, lowerAliasCutoff s d m θ C c0 τM x < lowerAliasTargetScale s d m θ C τM r x →
    r ≤ lowerAliasFineTargetBound d θ c0

include hs hd hm hθ hcontrol hCact hCs hc0 hτc0 in
theorem eventually_lowerAlias_hierarchy
    :
    ∀ᶠ x in atTop, LowerAliasHierarchy s d m θ C Cact Cs c0 τM x := by
  filter_upwards [eventually_lowerAlias_row_smallness hs hd hm hθ hcontrol hCact C,
    eventually_lowerAlias_cutoff_guards hs hd hm hθ hcontrol hτc0 C,
    eventually_lowerAlias_singleton_le hs hd hm hθ hcontrol hCs C c0,
    eventually_lowerAlias_fine_targets hs hd hm hθ hcontrol hc0 C]
    with x hrow hcut hsingle hfine
  rcases hrow with ⟨hbase,hlog,hgap,hq21,hq1,hDq⟩
  exact ⟨hcut.1,hcut.2.1,hbase,hlog,hgap,hq21,hq1,hDq,hcut.2.2,hsingle,hfine⟩

end

/-- The entire hierarchy holds for the paper's actual canonical M, grid,
mu, N and shrunk density endpoints, with c0=tau+1 and fixed representation
constants. The displayed activity bounds are consequences, not premises. -/
theorem actual_lowerAlias_hierarchy {s d a b Cact Cs : ℝ}
    (hs : 1 < s) (hd : 4*s < d) (ha : 0 < a) (hab : a < b)
    (hCact : 0 < Cact) (hCs : 0 < Cs) (C : ℝ) :
    ∀ᶠ x in atTop,
      LowerAliasHierarchy s d
        (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C Cact Cs
        (densityIntervalExponent a b + 1) (shrunkDensityExponent a b) x := by
  have hτ := densityIntervalExponent_pos ha hab
  obtain ⟨Cτ,_,hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  exact eventually_lowerAlias_hierarchy hs hd (lowerSaddleCoefficient_pos hs hd hτ)
    (lowerSaddleTheta_pos hs hd hτ) hcontrol hCact hCs (by linarith) (by linarith) C

end NearlyMinimax
