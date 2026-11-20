module

public import Mathlib

@[expose] public section

/-!
# The actual all-sample low-smoothness grid allocation

The grid is `k=ceil(4 n^(2/(d+4s)))` and its field amplitude is
`eta=b/k^s`. For `d>=4s`, its design occupancy is at most one, its
numeric score energy is uniformly bounded by `b^4`, and its variance
separation has the exact lower polynomial rate. These are allocation
inequalities; the finite-prior statistical score and legality bridges are
proved separately.
-/

noncomputable section
namespace NearlyMinimax

section
variable (d : ℕ) (s b x : ℝ)

def lowSmoothnessGridExponent : ℝ := 2 / (d + 4 * s)

def lowSmoothnessGrid : ℕ := Nat.ceil (4 * x ^ lowSmoothnessGridExponent d s)

def lowSmoothnessAmplitude : ℝ := b / (lowSmoothnessGrid d s x) ^ s

end

variable {d : ℕ} {s b x ρ Q : ℝ} (hs : 0 < s) (hb : 0 ≤ b) (hd : 4 * s ≤ (d : ℝ)) (_hb : 0 ≤ b)
    (hx : 1 ≤ x)
include hs hx

theorem lowSmoothnessGrid_rounding :
    4 * x ^ lowSmoothnessGridExponent d s ≤ (lowSmoothnessGrid d s x) ∧
      (lowSmoothnessGrid d s x) ≤ 5 * x ^ lowSmoothnessGridExponent d s := by
  have hbase : 1 ≤ x ^ lowSmoothnessGridExponent d s :=
    Real.one_le_rpow hx ((by unfold lowSmoothnessGridExponent; positivity : 0 < lowSmoothnessGridExponent d s)).le
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 4 * x ^ lowSmoothnessGridExponent d s by positivity)
  refine ⟨Nat.le_ceil _, ?_⟩
  change (lowSmoothnessGrid d s x) < 4 * x ^ lowSmoothnessGridExponent d s + 1 at hc
  linarith

theorem lowSmoothnessGrid_ge_four :
    4 ≤ lowSmoothnessGrid d s x := by
  have hbase : 1 ≤ x ^ lowSmoothnessGridExponent d s :=
    Real.one_le_rpow hx ((by unfold lowSmoothnessGridExponent; positivity : 0 < lowSmoothnessGridExponent d s)).le
  have hh := (lowSmoothnessGrid_rounding (d := d) hs hx).1
  exact_mod_cast (show 4 ≤ (lowSmoothnessGrid d s x : ℝ) by linarith)

theorem lowSmoothnessGrid_positive :
    0 < (lowSmoothnessGrid d s x : ℝ) := by
  positivity [lowSmoothnessGrid_ge_four (d := d) hs hx]

include hd in
theorem lowSmoothness_design_occupancy :
    x * (2 / (lowSmoothnessGrid d s x)) ^ d ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hpd : 1 ≤ lowSmoothnessGridExponent d s * d := by
    unfold lowSmoothnessGridExponent
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by positivity)).2 (by linarith)
  have hxp : x ≤ x ^ (lowSmoothnessGridExponent d s * d) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx hpd
  have hgrid := pow_le_pow_left₀ (by positivity) (lowSmoothnessGrid_rounding (d := d) hs hx).1 d
  rw [mul_pow, ← Real.rpow_mul_natCast hx0.le] at hgrid
  have hpow : 2 ^ d ≤ (4 : ℝ) ^ d := by gcongr; norm_num
  have hbudget : x * 2 ^ d ≤ (lowSmoothnessGrid d s x) ^ d := by
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hx0.le
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hxp (by positivity : 0 ≤ (4 : ℝ) ^ d)
      _ ≤ _ := hgrid
  rw [div_pow, ← mul_div_assoc]
  bound

include hb in
theorem lowSmoothnessAmplitude_le_budget : lowSmoothnessAmplitude d s b x ≤ b := by
  exact div_le_self hb (Real.one_le_rpow (by
    have hh := lowSmoothnessGrid_ge_four (d := d) hs hx
    bound) hs.le)

theorem lowSmoothness_grid_power_budget :
    x ^ 2 ≤ (lowSmoothnessGrid d s x) ^ (d + 4 * s) := by
  have hx0 : 0 < x := by linarith
  have hden : 0 < d + 4 * s := by positivity
  have hbase : x ^ lowSmoothnessGridExponent d s ≤ (lowSmoothnessGrid d s x) := by
    bound [(lowSmoothnessGrid_rounding (d := d) hs hx).1]
  have hh := Real.rpow_le_rpow (Real.rpow_pos_of_pos hx0 _).le hbase hden.le
  rw [← Real.rpow_mul hx0.le] at hh
  have heq : lowSmoothnessGridExponent d s * (d + 4 * s) = 2 := div_mul_cancel₀ _ hden.ne'
  simp_all

include _hb in
/-- The full source factor `n² eta⁴/k^d` is bounded uniformly for every `n>=1`. -/
theorem lowSmoothness_numeric_score_budget :
    x ^ 2 * (lowSmoothnessAmplitude d s b x) ^ 4 / (lowSmoothnessGrid d s x) ^ d ≤ b ^ 4 := by
  have hk := lowSmoothnessGrid_positive (d := d) hs hx
  have hbudget := lowSmoothness_grid_power_budget (d := d) hs hx
  have hid : x ^ 2 * (lowSmoothnessAmplitude d s b x) ^ 4 / (lowSmoothnessGrid d s x) ^ d =
      b ^ 4 * (x ^ 2 / (lowSmoothnessGrid d s x) ^ (d + 4 * s)) := by
    unfold lowSmoothnessAmplitude
    have hp4 : ((lowSmoothnessGrid d s x) ^ s) ^ 4 =
        (lowSmoothnessGrid d s x : ℝ) ^ (4 * s) := by
      rw [← Real.rpow_mul_natCast hk.le]
      ring
    rw [div_pow, hp4, Real.rpow_add hk, Real.rpow_natCast]
    field_simp
  rw [hid]
  bound

/-- The actual variance separation has the paper's all-sample polynomial lower rate. -/
theorem lowSmoothness_variance_separation :
    b ^ 2 / 5 ^ (2 * s) * x ^ (-4 * s / (d + 4 * s)) ≤
      (lowSmoothnessAmplitude d s b x) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hk := lowSmoothnessGrid_positive (d := d) hs hx
  have hupper := Real.rpow_le_rpow hk.le ((lowSmoothnessGrid_rounding (d := d) hs hx).2) (show 0 ≤ 2 * s by positivity)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_pos_of_pos hx0 _).le,
    ← Real.rpow_mul hx0.le] at hupper
  have heq : lowSmoothnessGridExponent d s * (2 * s) = 4 * s / (d + 4 * s) := by
    unfold lowSmoothnessGridExponent
    ring
  rw [heq] at hupper
  have hh := div_le_div_of_nonneg_left (sq_nonneg b) (Real.rpow_pos_of_pos hk _) hupper
  have hright : (lowSmoothnessAmplitude d s b x) ^ 2 = b ^ 2 / (lowSmoothnessGrid d s x) ^ (2 * s) := by
    unfold lowSmoothnessAmplitude
    rw [div_pow, ← Real.rpow_mul_natCast hk.le]
    ring
  have hleft : b ^ 2 / (5 ^ (2 * s) * x ^ (4 * s / (d + 4 * s))) =
      b ^ 2 / 5 ^ (2 * s) * x ^ (-4 * s / (d + 4 * s)) := by
    rw [show -4 * s / (d + 4 * s) = -(4 * s / (d + 4 * s)) by ring,
      Real.rpow_neg hx0.le]
    ring
  bound

include hb in
theorem lowSmoothness_amplitude_legal_guards
    (hlinear : (2 ^ d + 2) * b ≤ ρ) (hsquare : b ^ 2 ≤ ρ) :
    0 ≤ lowSmoothnessAmplitude d s b x ∧
      (2 ^ d + 2) * lowSmoothnessAmplitude d s b x ≤ ρ ∧
      (lowSmoothnessAmplitude d s b x) ^ 2 ≤ ρ := by
  have hn := div_nonneg hb (Real.rpow_pos_of_pos (lowSmoothnessGrid_positive (d := d) hs hx) s).le
  have hbnd := lowSmoothnessAmplitude_le_budget (d := d) hs hb hx
  refine ⟨hn, ?_, (pow_le_pow_left₀ hn hbnd 2).trans hsquare⟩
  exact (mul_le_mul_of_nonneg_left hbnd (by positivity)).trans hlinear

/-- The same rounded grid balances the concrete pair-estimator variance. -/
theorem lowSmoothnessGrid_pair_variance_budget :
    let ratio := 5 ^ d * x ^ (-8 * s / (d + 4 * s))
    (lowSmoothnessGrid d s x) ^ d / x ^ 2 ≤
      ratio := by
  intro ratio
  have hx0 : 0 < x := by linarith
  have hupper := pow_le_pow_left₀ (lowSmoothnessGrid_positive (d := d) hs hx).le (lowSmoothnessGrid_rounding hs hx).2 d
  rw [mul_pow, ← Real.rpow_mul_natCast hx0.le] at hupper
  have heq : lowSmoothnessGridExponent d s * d - 2 = -8 * s / (d + 4 * s) := by
    unfold lowSmoothnessGridExponent
    field_simp
    ring
  have hid : 5 ^ d * x ^ (lowSmoothnessGridExponent d s * d) / x ^ 2 =
      ratio := by
    rw [← Real.rpow_two, mul_div_assoc, ← Real.rpow_sub hx0, heq]
  rw [← hid]
  bound

theorem lowSmoothnessGrid_pair_bias_budget :
    (lowSmoothnessGrid d s x) ^ (-4 * s) ≤ x ^ (-8 * s / (d + 4 * s)) := by
  have hx0 : 0 < x := by linarith
  have hbase : x ^ lowSmoothnessGridExponent d s ≤ (lowSmoothnessGrid d s x) := by
    bound [(lowSmoothnessGrid_rounding (d := d) hs hx).1]
  have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hx0 _) hbase (by linarith : -4 * s ≤ 0)
  rw [← Real.rpow_mul hx0.le] at hh
  grind [lowSmoothnessGridExponent]

end NearlyMinimax
