module
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic
@[expose] public section
namespace DensityStrip
open Real

/-- Compare two positive monomials by comparing their exponents in base `T`. -/
macro "exponents" ht:term : tactic => `(tactic|
  (first | apply (logb_le_logb $ht (by positivity) (by positivity)).mp
         | apply (logb_lt_logb_iff $ht (by positivity) (by positivity)).mp) <;>
  simp (disch := positivity) only [logb_mul, logb_div, logb_pow,
    logb_rpow_eq_mul_logb_of_pos, logb_self_eq_one $ht, logb_one, mul_one])

noncomputable abbrev tiny : ℝ := 1/100000
noncomputable abbrev length (s : ℝ) : ℝ := 1/(10*s-7)
noncomputable abbrev exponent (s : ℝ) : ℝ := 3*length s*(1-s)
noncomputable abbrev localLength (s x : ℝ) : ℝ := 1-exponent s+(2-2*s)*x

variable {s x : ℝ} (hl : 17/19 ≤ s) (hr : s ≤ 1)
include hl hr

theorem length_spec : 1/3 ≤ length s ∧ length s ≤ 13/25 ∧ length s*(10*s-7)=1 := by
  have hd : 0 < 10*s-7 := by linarith
  exact ⟨(le_div_iff₀ hd).mpr (by linarith), (div_le_iff₀ hd).mpr (by linarith),
    div_mul_cancel₀ _ hd.ne'⟩

theorem long_margin : 13/194 + 8*tiny < (3*length s/4-2*tiny)*(s-139/194) := by
  obtain ⟨h,h',he⟩ := length_spec hl hr
  have := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr h)
  norm_num [tiny] at *; nlinarith

theorem kernel_margin (hx : length s ≤ x) (hx' : x ≤ 1) :
    0 ≤ localLength s x ∧ (13/84+tiny)*localLength s x + 3/2*x + 4*tiny ≤ 2*s*x := by
  obtain ⟨h,h',he⟩ := length_spec hl hr
  have hpos : 0 ≤ 2-2*s := by linarith
  have hax := mul_nonneg hpos (sub_nonneg.mpr hx)
  have hp := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hx)
  unfold localLength exponent
  norm_num [tiny] at *
  constructor <;> nlinarith

end DensityStrip
