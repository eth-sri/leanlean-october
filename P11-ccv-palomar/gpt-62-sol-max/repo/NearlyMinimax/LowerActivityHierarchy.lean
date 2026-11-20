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

def lowerAliasH (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  1 + Real.log (lowerSaddleN s d m θ C τM x)

def lowerAliasQ (s d m θ C Cact a : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  Cact * (lowerSaddleD d m x : ℝ) * lowerAliasH s d m θ C τM x *
    (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x)^(a/d)

def lowerAliasCutoff (s d m θ C c0 : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  lowerSaddleN s d m θ C τM x * Real.exp (-c0 * lowerSaddleD d m x)

def lowerAliasTargetScale (s d m θ C : ℝ) (τM : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  lowerSaddleN s d m θ C τM x *
    (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x)^(((r : ℝ)-2)/d)

variable {s d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}

theorem lowerAliasH_div_M_sq_limit
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (s C : ℝ) :
    Tendsto (fun x => lowerAliasH s d m θ C τM x / (lowerSaddleM m x : ℝ)^2)
      atTop (𝓝 (((d-4*s)/(d*(d+4)))/m^2)) := by
  have h0 := (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.pow 2
  have hh := h0.add (lowerSaddleLogN_div_M_sq_limit hd hm hθ hcontrol s C)
  simp only [zero_pow (by decide : 2 ≠ 0), zero_add] at hh
  convert hh using 1
  funext x
  simp only [lowerAliasH, add_div, one_div, Pi.inv_apply, inv_pow]

local notation "scale" => (fun x => (lowerSaddleM m x : ℝ))
local notation "deg" => (fun x => (lowerSaddleD d m x : ℝ))
local notation "aliasH" => (fun C => lowerAliasH s d m θ C τM)
local notation "muH" => (fun C x => lowerSaddleMu d m θ C x * aliasH C x)

private theorem aliasH_slope (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (C : ℝ) : LogSlope atTop scale (aliasH C) 0 :=
  .of_poly (a := ((d-4*s)/(d*(d+4)))/m^2) (lowerSaddleM_tendsto_atTop hm) 2
    (by
      have hd0 : 0 < d := by linarith
      exact div_pos (div_pos (sub_pos.mpr hd) (by positivity)) (by positivity))
    (lowerAliasH_div_M_sq_limit (by linarith) hm hθ hcontrol s C)

private theorem degree_slope (hd : 0 < d) (hm : 0 < m) : LogSlope atTop scale deg 0 :=
  .of_poly (a := (d+8)/4) (lowerSaddleM_tendsto_atTop hm) 1 (by linarith)
    (by simpa only [pow_one] using lowerSaddleD_div_M_limit hd hm)

section
variable (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ)
include hs hd hm hθ hcontrol

private theorem aliasMuH_slope (C : ℝ) : LogSlope atTop scale (muH C) (-θ) := by
  simpa only [add_zero] using (lowerSaddleMu_logSlope (d := d) (by linarith) hm hθ C).mul
    (aliasH_slope hs hd hm hθ hcontrol C)

section
variable {Cact : ℝ} (hCact : 0 < Cact)
include hCact

private theorem aliasQ_slope (C a : ℝ) :
    LogSlope atTop scale (lowerAliasQ s d m θ C Cact a τM) (a / d * -θ) := by
  unfold lowerAliasQ
  simpa only [zero_add] using (((LogSlope.const (lowerSaddleM_tendsto_atTop hm) hCact).mul
    (degree_slope (d := d) (by linarith) hm)).mul (aliasH_slope hs hd hm hθ hcontrol C)).mul
    ((aliasMuH_slope hs hd hm hθ hcontrol C).rpow (a / d))

/-- The three row-ratio requirements for a fixed activity prefactor. -/
theorem eventually_lowerAlias_row_smallness (C : ℝ) :
    ∀ᶠ x in atTop,
      lowerAliasQ s d m θ C Cact 2 τM x ≤ lowerAliasQ s d m θ C Cact 1 τM x ∧
      lowerAliasQ s d m θ C Cact 1 τM x ≤ 1/2 ∧
      deg x ^ 2 * lowerAliasQ s d m θ C Cact 1 τM x ≤ 1 := by
  have hd0 : 0 < d := by linarith
  have hM := lowerSaddleM_tendsto_atTop hm
  have hbase := aliasMuH_slope hs hd hm hθ hcontrol C
  have hD := degree_slope hd0 hm
  have hH := aliasH_slope hs hd hm hθ hcontrol C
  have hq := aliasQ_slope hs hd hm hθ hcontrol hCact C 1
  have hc : 1 / d * -θ < 0 := mul_neg_of_pos_of_neg (by positivity) (neg_neg_of_pos hθ)
  filter_upwards [(hbase.tends_zero hM (neg_neg_of_pos hθ)).eventually (gt_mem_nhds zero_lt_one),
    (hq.tends_zero hM hc).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    (((hD.pow 2).mul hq).tends_zero hM (by simpa using hc)).eventually (gt_mem_nhds zero_lt_one),
    hbase.pos, hD.pos, hH.pos] with x hsmall hq1 hDq hb hdx hhx
  refine ⟨mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hb hsmall.le (by gcongr <;> norm_num)) ?_, hq1.le, hDq.le⟩
  positivity

end

end

theorem lowerSaddleM_sq_tendsto_atTop (hm : 0 < m) :
    Tendsto (fun x => scale x ^ 2) atTop atTop :=
  (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp (lowerSaddleM_tendsto_atTop hm)

private theorem ratio_scale_sq {f : ℝ → ℝ} {r : ℝ} (hm : 0 < m)
    (h : Tendsto (fun x => f x / scale x) atTop (𝓝 r)) :
    Tendsto (fun x => f x / scale x ^ 2) atTop (𝓝 0) := by
  simpa only [Pi.inv_apply, div_eq_mul_inv, pow_two, mul_inv, mul_assoc, mul_zero] using
    h.mul (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop

section
variable (hd : 0 < d) (hm : 0 < m)
include hd hm

theorem lowerSaddleD_div_M_sq_tends_zero :
    Tendsto (fun x => deg x / scale x ^ 2) atTop (𝓝 0) :=
  ratio_scale_sq hm (lowerSaddleD_div_M_limit hd hm)

theorem lowerSaddleN_quad_slope (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (s C : ℝ) :
    LogSlope atTop (fun x => scale x ^ 2) (lowerSaddleN s d m θ C τM) (((d-4*s)/(d*(d+4)))/m^2) :=
  ⟨.of_forall (lowerSaddleN_positive s d m θ C τM), lowerSaddleLogN_div_M_sq_limit hd hm hθ hcontrol s C⟩

end

section
variable (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ)
include hs hd hm hθ hcontrol

section
variable (C c0 : ℝ)

/-- The cutoff still diverges: the cost of the degree is only linear in `M`. -/
theorem lowerAliasCutoff_tendsto_atTop :
    Tendsto (lowerAliasCutoff s d m θ C c0 τM) atTop atTop := by
  have hd0 : 0 < d := by linarith
  have he : LogSlope atTop (fun x => scale x ^ 2) (fun x => Real.exp (-c0 * deg x)) 0 :=
    LogSlope.exp (by simpa only [mul_div_assoc, mul_zero] using
      (lowerSaddleD_div_M_sq_tends_zero hd0 hm).const_mul (-c0))
  exact ((lowerSaddleN_quad_slope hd0 hm hθ hcontrol s C).mul he).tends_top
    (lowerSaddleM_sq_tendsto_atTop hm) (by simp; positivity)

theorem eventually_lowerAlias_singleton_le :
    ∀ᶠ x in atTop, deg x * Real.exp (c0 * deg x) ≤ lowerSaddleN s d m θ C τM x := by
  have hd0 : 0 < d := by linarith
  have hM := lowerSaddleM_sq_tendsto_atTop hm
  have he : LogSlope atTop (fun x => scale x ^ 2) (fun x => Real.exp (c0 * deg x)) 0 :=
    LogSlope.exp (by simpa only [mul_div_assoc, mul_zero] using (lowerSaddleD_div_M_sq_tends_zero hd0 hm).const_mul c0)
  have hD := degree_slope hd0 hm
  have hD' : LogSlope atTop (fun x => scale x ^ 2) deg 0 := ⟨hD.pos, ratio_scale_sq hm hD.limit⟩
  have h := ((hD'.mul he).div (lowerSaddleN_quad_slope hd0 hm hθ hcontrol s C)).tends_zero hM
    (by simp; positivity)
  filter_upwards [h.eventually (gt_mem_nhds zero_lt_one)] with x hx
  simpa only [one_mul] using ((div_lt_iff₀ (lowerSaddleN_positive _ _ _ _ _ _ _)).1 hx).le

end

end

/-- Exact scalar fine-band count restriction, obtained by taking logarithms
of the actual target scale above the common cutoff. -/
theorem fine_target_count_lt {N base H ω d c0 D r : ℝ}
    (hN : 0 < N) (hbase : 0 < base) (hd : 0 < d)
    (hgap : 0 < ω - Real.log H) (hlog : Real.log base = -ω + Real.log H)
    (hactive : N * Real.exp (-c0*D) < N * base^((r-2)/d)) :
    r < 2 + d*c0*D/(ω-Real.log H) := by
  have hpow := (mul_lt_mul_iff_right₀ hN).mp hactive
  have hln := Real.log_lt_log (Real.exp_pos _) hpow
  rw [Real.log_exp, Real.log_rpow hbase, hlog] at hln
  have hm := mul_lt_mul_of_pos_right hln hd
  have he : ((r-2)/d * (-ω + Real.log H))*d = -(r-2)*(ω-Real.log H) := by
    field_simp [hd.ne']
    ring
  rw [he] at hm
  have hp : (r-2)*(ω-Real.log H) < d*c0*D := by nlinarith
  have hv := (lt_div_iff₀ hgap).2 hp
  linarith

/-- The ratio controlling all fine targets has a fixed finite limit. -/
theorem lowerAliasD_div_gap_limit
    (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (C : ℝ) :
    Tendsto (fun x => (lowerSaddleD d m x : ℝ) /
      (lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x)))
      atTop (𝓝 (((d+8)/4)/θ)) := by
  have hd0 : 0 < d := by linarith
  have hgap := (lowerSaddleOmega_div_M_limit hd0 hm hθ C).sub
    ((aliasH_slope hs hd hm hθ hcontrol C).limit)
  simp only [sub_zero] at hgap
  have hh := (lowerSaddleD_div_M_limit hd0 hm).div hgap hθ.ne'
  refine hh.congr' ?_
  filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  simp only [Pi.div_apply, ← sub_div, div_div_div_cancel_right₀ hx.ne']

/-- One fixed rounded integer bounds every nonzero fine-band target. -/
def lowerAliasFineTargetBound (d θ c0 : ℝ) : ℕ :=
  Nat.ceil (3 + d*c0*(((d+8)/4)/θ + 1))

theorem eventually_lowerAlias_fine_targets
    (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) {c0 : ℝ} (hc0 : 0 < c0) (C : ℝ) :
    ∀ᶠ x in atTop,
      lowerAliasFineTargetBound d θ c0 ≤ lowerSaddleM m x ∧
      ∀ r : ℕ, lowerAliasCutoff s d m θ C c0 τM x < lowerAliasTargetScale s d m θ C τM r x →
        r ≤ lowerAliasFineTargetBound d θ c0 := by
  have hd0 : 0 < d := by linarith
  have hglim := (lowerSaddleOmega_div_M_limit hd0 hm hθ C).sub
    ((aliasH_slope hs hd hm hθ hcontrol C).limit)
  simp only [sub_zero] at hglim
  have hh := ((lowerAliasD_div_gap_limit hs hd hm hθ hcontrol C).const_mul (d*c0)).const_add 2
  have hmargin : 2 + d*c0*(((d+8)/4)/θ) < 3 + d*c0*(((d+8)/4)/θ+1) := by nlinarith
  filter_upwards [hh.eventually (gt_mem_nhds hmargin),
    (lowerSaddleM_nat_tendsto_atTop hm).eventually (eventually_ge_atTop (lowerAliasFineTargetBound d θ c0)),
    hglim.eventually (lt_mem_nhds hθ),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ)),
    (aliasMuH_slope hs hd hm hθ hcontrol C).pos,
    (aliasH_slope hs hd hm hθ hcontrol C).pos, eventually_gt_atTop (0 : ℝ)]
    with x hthreshold hM hgapnorm hMpos hbase hH hx
  refine ⟨hM, fun r hr => ?_⟩
  have hlog : Real.log (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x) =
      -lowerSaddleOmega d m θ C x + Real.log (lowerAliasH s d m θ C τM x) := by
    rw [lowerSaddleMu_eq_exp hx, Real.log_mul (Real.exp_pos _).ne' hH.ne', Real.log_exp]
  have hgap : 0 < lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x) := by
    have hg : 0 < (lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x)) / lowerSaddleM m x := by
      simpa only [sub_div] using hgapnorm
    simpa only [zero_mul] using (lt_div_iff₀ hMpos).1 hg
  have hrlt := fine_target_count_lt (lowerSaddleN_positive s d m θ C τM x) hbase hd0 hgap hlog hr
  have hbound : (r : ℝ) < (lowerAliasFineTargetBound d θ c0 : ℝ) := by
    apply hrlt.trans
    have hthr : 2 + d*c0*(lowerSaddleD d m x : ℝ) /
        (lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x)) <
        3 + d*c0*(((d+8)/4)/θ+1) := by simpa only [mul_div_assoc] using hthreshold
    exact hthr.trans_le (Nat.le_ceil _)
  exact Nat.le_of_lt (by exact_mod_cast hbound)

/-- Numerical cutoff, base and fine-target guards common to the source rows. -/
structure LowerAliasGuards (s d m θ C c0 : ℝ) (τM : ℕ → ℝ) (x : ℝ) : Prop where
  cutoff : 1 < lowerAliasCutoff s d m θ C c0 τM x
  exponent_le : τM (lowerSaddleM m x) ≤ c0
  base_le : lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x ≤ 1
  log_le : Real.log (lowerAliasH s d m θ C τM x) ≤ lowerSaddleM m x
  target_le_M : lowerAliasFineTargetBound d θ c0 ≤ lowerSaddleM m x
  active_le : ∀ r : ℕ, lowerAliasCutoff s d m θ C c0 τM x < lowerAliasTargetScale s d m θ C τM r x →
    r ≤ lowerAliasFineTargetBound d θ c0

theorem actual_lowerAlias_guards {s d a b : ℝ}
    (hs : 1 < s) (hd : 4*s < d) (ha : 0 < a) (hab : a < b) (C : ℝ) :
    let τ := densityIntervalExponent a b
    ∀ᶠ x in atTop, LowerAliasGuards s d (lowerSaddleCoefficient s d τ) (lowerSaddleTheta s d τ)
      C (τ+1) (shrunkDensityExponent a b) x := by
  let τ := densityIntervalExponent a b
  have hτ := densityIntervalExponent_pos ha hab
  have hm := lowerSaddleCoefficient_pos hs hd hτ
  have hθ := lowerSaddleTheta_pos hs hd hτ
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hM := lowerSaddleM_tendsto_atTop hm
  have hH := (aliasH_slope hs hd hm hθ hcontrol C).limit
  have hb := (aliasMuH_slope hs hd hm hθ hcontrol C).tends_zero hM (neg_neg_of_pos hθ)
  filter_upwards [eventually_lowerAlias_fine_targets hs hd hm hθ hcontrol (by linarith : 0 < τ+1) C,
    (lowerAliasCutoff_tendsto_atTop hs hd hm hθ hcontrol C (τ+1)).eventually (eventually_gt_atTop 1),
    (lowerSaddleTau_limit hm hcontrol).eventually (gt_mem_nhds (show τ < τ+1 by linarith)),
    hb.eventually (gt_mem_nhds zero_lt_one), hH.eventually (gt_mem_nhds zero_lt_one),
    hM.eventually (eventually_gt_atTop 0)] with x hf hc hτx hb hl hMx
  exact ⟨hc, hτx.le, hb.le, by simpa only [one_mul] using ((div_lt_iff₀ hMx).1 hl).le, hf.1, hf.2⟩

end NearlyMinimax
