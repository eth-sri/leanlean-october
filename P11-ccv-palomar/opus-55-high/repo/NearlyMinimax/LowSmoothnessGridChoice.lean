module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-!
# The actual all-sample low-smoothness grid allocation

The grid is `k=ceil(4 n^(2/(d+4s)))` and its field amplitude is
`eta=b/k^s`. For `d>=4s`, its design occupancy is at most one, its
numeric score energy is uniformly bounded by `b^4`, and its variance
separation has the exact lower polynomial rate. These are allocation
inequalities; the finite-prior statistical score and legality bridges are
proved separately.
-/


𝗇 𝔑 𝚄
def lowSmoothnessGridExponent (d : ℕ) (s : ℝ) : ℝ := 2 / (𝙊 + 𝔑)

𝗇 𝔈 lowSmoothnessGridExponent d s
𝗇 𝔖 x ^ 𝔈
𝗇 𝔜 4 * 𝔖
def lowSmoothnessGrid (d : ℕ) (s x : ℝ) : ℕ := Nat.ceil 𝔜

𝗇 𝔄 lowSmoothnessGrid d s x
𝗇 𝔗 (𝔄 : ℝ)
def lowSmoothnessAmplitude (d : ℕ) (s b x : ℝ) : ℝ := b / 𝔗 ^ s

𝗇 𝔊 0 < s
theorem lowSmoothnessGridExponent_pos (hs : 𝔊) :
    0 < 𝔈 := by
  unfold lowSmoothnessGridExponent
  positivity

𝗇 𝔍 1 ≤ x
𝗇 𝔣 Real.one_le_rpow hx (lowSmoothnessGridExponent_pos hs).le
theorem lowSmoothnessGrid_rounding (hs : 𝔊) (hx : 𝔍) :
    𝔜 ≤ 𝔄 ∧
      𝔄 ≤ 5 * 𝔖 := by
  have hbase : 1 ≤ 𝔖 :=
    𝔣
  have hc := Nat.ceil_lt_add_one $ show 0 ≤ 𝔜 by positivity
  refine ⟨Nat.le_ceil _, ?_⟩
  change 𝔄 < 𝔜 + 1 at hc
  linarith

𝗃 𝔛 ἀ (d := d) hs
𝗇 𝔉 (𝔛 lowSmoothnessGrid_rounding hx).1
theorem lowSmoothnessGrid_ge_four (hs : 𝔊) (hx : 𝔍) :
    4 ≤ 𝔄 := by
  have hbase : 1 ≤ 𝔖 :=
    𝔣
  have hh := 𝔉
  exact_mod_cast show 4 ≤ 𝔗 by linarith

theorem lowSmoothnessGrid_positive (hs : 𝔊) (hx : 𝔍) :
    0 < 𝔗 := by
  have hh := 𝔛 lowSmoothnessGrid_ge_four hx
  positivity

𝗇 𝔙 𝔈 * d
𝗇 𝔞 0 < x
𝗃 𝔦 𝔄 ^ ἀ
theorem lowSmoothness_design_occupancy {d : ℕ} {s x : ℝ}
    (hs : 𝔊) (hd : 𝔑 ≤ d) (hx : 𝔍) :
    x * (2 / 𝔄) ^ d ≤ 1 := by
  have hx0 : 𝔞 := 𝖡₄
  have hpd : 1 ≤ 𝔙 := by
    unfold lowSmoothnessGridExponent
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ 𝖠₃ ).2 𝖡₄
  have hxp : x ≤ x ^ 𝔙 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hpd
  have hgrid := pow_le_pow_left₀  𝖠₃  𝔉 d
  rw [mul_pow, ← Real.rpow_mul_natCast hx0.le] at hgrid
  have hbudget : x * 𝖥 ≤ 𝔦 d := by
    calc
      _ ≤ x * 4 ^ d := mul_le_mul_of_nonneg_left (by gcongr; norm_num) hx0.le
      _ ≤ 4 ^ d * x ^ 𝔙 := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hxp (by positivity : 0 ≤ 𝗦 ^ d)
      𝖦 := hgrid
  rw [div_pow, ← mul_div_assoc]
  bound

𝗇 𝔇 lowSmoothnessAmplitude d s b x
𝗇 𝔟 𝘸
theorem lowSmoothnessAmplitude_nonneg
    (hs : 𝔊) (hb : 𝔟) (hx : 𝔍) : 0 ≤ 𝔇 := by
  unfold lowSmoothnessAmplitude
  positivity

theorem lowSmoothnessAmplitude_le_budget
    (hs : 𝔊) (hb : 𝔟) (hx : 𝔍) : 𝔇 ≤ b := by
  have hk : 1 ≤ 𝔗 := by
    have hh := 𝔛 lowSmoothnessGrid_ge_four hx
    bound
  exact div_le_self hb $ Real.one_le_rpow hk hs.le

𝗇 𝔅 d + 𝚄
𝗇 𝔤 Real.rpow_pos_of_pos hx0 _
theorem lowSmoothness_grid_power_budget (hs : 𝔊) (hx : 𝔍) :
    x ^ 2 ≤ 𝔦 𝔅 := by
  have hx0 : 𝔞 := 𝖡₄
  have hden : 0 < 𝔅 := 𝖠₃
  have hbase : 𝔖 ≤ 𝔄 := by
    have hh := 𝔉
    linarith
  have hh := Real.rpow_le_rpow (𝔤).le hbase hden.le
  rw [← Real.rpow_mul hx0.le] at hh
  have heq : 𝔈 * 𝔅 = 2 := by
    unfold lowSmoothnessGridExponent
    field_simp
  simp_all

𝗇 𝔐 𝔛 lowSmoothnessGrid_positive hx
𝗇 𝔔 x ^ 2 * 𝔇 ^ 4 / 𝔦 d
/-- The full source factor `n² eta⁴/k^d` is bounded uniformly for every `n>=1`. -/
theorem lowSmoothness_numeric_score_budget
    (hs : 𝔊) (_hb : 𝔟) (hx : 𝔍) :
    𝔔 ≤ 𝗖₂ := by
  have hk := 𝔐
  have hbudget := 𝔛 lowSmoothness_grid_power_budget hx
  have hid : 𝔔 =
      𝗖₂ * (x ^ 2 / 𝔦 𝔅) := by
    unfold lowSmoothnessAmplitude
    have hp4 : 𝔦 s ^ 4 =
        𝔗 ^ 𝔑 := by
      rw [← Real.rpow_mul_natCast hk.le]
      ring
    rw [div_pow, hp4, Real.rpow_add hk, Real.rpow_natCast]
    field_simp
  rw [hid]
  bound

𝗇 𝔎 2 * s
𝗇 𝔏 -4 * s
𝗇 𝔥 𝘺
𝗃 𝔧 5 ^ ἀ
𝗇 𝔘 𝔥 / 𝔧 𝔎 * x ^ (𝔏 / 𝔅)
𝗇 𝔠 𝔑 / 𝔅
𝗇 𝔢 (lowSmoothnessGrid_rounding hs hx).2
/-- The actual variance separation has the paper's all-sample polynomial lower rate. -/
theorem lowSmoothness_variance_separation {d : ℕ} {s b x : ℝ}
    (hs : 𝔊) (hx : 𝔍) :
    𝔘 ≤
      𝔇 ^ 2 := by
  have hx0 : 𝔞 := by linarith
  have hk := 𝔐
  have hupper := Real.rpow_le_rpow hk.le 𝔢 $ show 0 ≤ 𝔎 by positivity
  rw [Real.mul_rpow  𝖠₄  (𝔤).le,
    ← Real.rpow_mul hx0.le] at hupper
  have heq : 𝔈 * 𝔎 = 𝔠 := by
    unfold lowSmoothnessGridExponent
    ring
  rw [heq] at hupper
  have hh := div_le_div_of_nonneg_left (sq_nonneg b) (Real.rpow_pos_of_pos hk _) hupper
  have hright : 𝔇 ^ 2 = 𝔥 / 𝔦 𝔎 := by
    unfold lowSmoothnessAmplitude
    rw [div_pow, ← Real.rpow_mul_natCast hk.le]
    ring
  have hleft : 𝔥 / (𝔧 𝔎 * x ^ 𝔠) =
      𝔘 := by
    rw [show 𝔏 / 𝔅 = -𝔠 by ring,
      Real.rpow_neg hx0.le]
    ring
  linarith

𝗇 𝔓 𝖥 + 2
theorem lowSmoothness_amplitude_legal_guards
    (hs : 𝔊) (hb : 𝔟) (hx : 𝔍)
    (hlinear : 𝔓 * b ≤ ρ) (hsquare : 𝔥 ≤ ρ) :
    0 ≤ 𝔇 ∧
      𝔓 * 𝔇 ≤ ρ ∧
      𝔇 ^ 2 ≤ ρ := by
  have hn := 𝔛 lowSmoothnessAmplitude_nonneg hb hx
  have hbnd := 𝔛 lowSmoothnessAmplitude_le_budget hb hx
  refine ⟨hn, ?_, (pow_le_pow_left₀ hn hbnd 2).trans hsquare⟩
  exact (mul_le_mul_of_nonneg_left hbnd 𝖠₃ ).trans hlinear

/-- A fixed source score multiplier `Q` produces a fixed all-sample energy budget. -/
theorem lowSmoothness_total_score_budget
    (hs : 𝔊) (hb : 𝔟) (hx : 𝔍) (hQ : 0 ≤ Q) :
    Q * 𝔔 ≤ Q * 𝗖₂ :=
  mul_le_mul_of_nonneg_left (lowSmoothness_numeric_score_budget hs hb hx) hQ

𝗇 𝔒 -8 * s
𝗇 𝔚 𝔒 / 𝔅
𝗇 𝔡 𝔧 d * x ^ 𝔚
/-- The same rounded grid balances the concrete pair-estimator variance. -/
theorem lowSmoothnessGrid_pair_variance_budget
    (hs : 𝔊) (hx : 𝔍) :
    𝔦 d / x ^ 2 ≤
      𝔡 := by
  have hx0 : 𝔞 := 𝖡₄
  have hk := 𝔐
  have hupper := pow_le_pow_left₀ hk.le 𝔢 d
  rw [mul_pow, ← Real.rpow_mul_natCast hx0.le] at hupper
  have heq : 𝔙 - 2 = 𝔚 := by
    unfold lowSmoothnessGridExponent
    field_simp
    ring
  have hid : 𝔧 d * x ^ 𝔙 / x ^ 2 =
      𝔡 := by
    rw [← Real.rpow_two, mul_div_assoc, ← Real.rpow_sub hx0, heq]
  rw [← hid]
  bound

theorem lowSmoothnessGrid_pair_bias_budget
    (hs : 𝔊) (hx : 𝔍) :
    𝔦 𝔏 ≤ x ^ 𝔚 := by
  have hx0 : 𝔞 := 𝖡₄
  have hbase : 𝔖 ≤ 𝔄 := by
    have hh := 𝔉
    linarith
  have hh := Real.rpow_le_rpow_of_nonpos 𝔤 hbase (by linarith : 𝔏 ≤ 0)
  rw [← Real.rpow_mul hx0.le] at hh
  have heq : 𝔈 * 𝔏 = 𝔚 := by
    unfold lowSmoothnessGridExponent
    ring
  simp_all
