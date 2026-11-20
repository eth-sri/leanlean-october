module
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic

@[expose] public section

open Real Set Filter
open scoped BigOperators Topology ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace MathCollab.Density.Stronger

/-- A smooth decreasing step, equal to one below 5/4 and zero above 3/2. -/
def dyadicStep (x : ℝ) : ℝ := 1-Real.smoothTransition (4*x-5)

theorem dyadicStep_contDiff : ContDiff ℝ ∞ dyadicStep := by
  unfold dyadicStep
  fun_prop

theorem dyadicStep_bounds (x : ℝ) : 0 ≤ dyadicStep x ∧ dyadicStep x ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (4*x-5)
  have h1 := Real.smoothTransition.le_one (4*x-5)
  dsimp [dyadicStep]
  constructor <;> linarith

theorem dyadicStep_antitone : Antitone dyadicStep := by
  intro x y hxy
  have hh := Real.smoothTransition.monotone (show 4*x-5 ≤ 4*y-5 by linarith)
  dsimp [dyadicStep]
  linarith

theorem dyadicStep_one {x : ℝ} (hx : x ≤ 5/4) : dyadicStep x = 1 := by
  rw [dyadicStep, Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

theorem dyadicStep_zero {x : ℝ} (hx : 3/2 ≤ x) : dyadicStep x = 0 := by
  rw [dyadicStep, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

/-- Fixed, smooth dyadic partition weight. Its support is strictly inside
the interval (1/2,2), so splitting at the centre introduces no endpoint mass. -/
def smoothDyadicWeight (x : ℝ) : ℝ := dyadicStep x-dyadicStep (2*x)

theorem smoothDyadicWeight_contDiff : ContDiff ℝ ∞ smoothDyadicWeight := by
  unfold smoothDyadicWeight
  exact dyadicStep_contDiff.sub (dyadicStep_contDiff.comp (contDiff_const.mul contDiff_id))

theorem smoothDyadicWeight_zero_of_le {x : ℝ} (hx : x ≤ 5/8) :
    smoothDyadicWeight x = 0 := by
  rw [smoothDyadicWeight, dyadicStep_one (by linarith), dyadicStep_one (by linarith)]
  ring

theorem smoothDyadicWeight_zero_of_ge {x : ℝ} (hx : 3/2 ≤ x) :
    smoothDyadicWeight x = 0 := by
  rw [smoothDyadicWeight, dyadicStep_zero hx, dyadicStep_zero (by linarith)]
  ring

theorem smoothDyadicWeight_bounds (x : ℝ) :
    0 ≤ smoothDyadicWeight x ∧ smoothDyadicWeight x ≤ 1 := by
  by_cases hx : x ≤ 0
  · rw [smoothDyadicWeight_zero_of_le (by linarith)]
    norm_num
  · have h0 := (dyadicStep_bounds x).2
    have h1 := (dyadicStep_bounds (2*x)).1
    have hmono := dyadicStep_antitone (show x ≤ 2*x by linarith)
    dsimp [smoothDyadicWeight]
    constructor <;> linarith

theorem smoothDyadicWeight_tsupport :
    tsupport smoothDyadicWeight ⊆ Icc (5/8 : ℝ) (3/2) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  change smoothDyadicWeight x ≠ 0 at hx
  constructor
  · by_contra h
    exact hx (smoothDyadicWeight_zero_of_le (by linarith))
  · by_contra h
    exact hx (smoothDyadicWeight_zero_of_ge (by linarith))

theorem smoothDyadicWeight_div_pow_succ (x : ℝ) (n : ℕ) :
    smoothDyadicWeight (x/(2 : ℝ)^(n+1)) =
      dyadicStep (x/(2 : ℝ)^(n+1))-dyadicStep (x/(2 : ℝ)^n) := by
  rw [smoothDyadicWeight]
  congr 1
  rw [pow_succ]
  field_simp

theorem dyadicStep_div_pow_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => dyadicStep (x/(2 : ℝ)^n)) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => x/(2 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, inv_pow, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).const_mul x
  simpa only [Function.comp_def, dyadicStep_one (by norm_num : (0 : ℝ) ≤ 5/4)] using
    dyadicStep_contDiff.continuous.continuousAt.tendsto.comp ht

theorem hasSum_smoothDyadicWeight_nonneg_scales (x : ℝ) :
    HasSum (fun n : ℕ => smoothDyadicWeight (x/(2 : ℝ)^n)) (1-dyadicStep (2*x)) := by
  have hs : HasSum (fun n : ℕ => smoothDyadicWeight (x/(2 : ℝ)^(n+1))) (1-dyadicStep x) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg
      (fun n => (smoothDyadicWeight_bounds _).1) _).mpr
    simp_rw [smoothDyadicWeight_div_pow_succ,
      Finset.sum_range_sub (fun n : ℕ => dyadicStep (x/(2 : ℝ)^n)), pow_zero, div_one]
    exact (dyadicStep_div_pow_tendsto x).sub_const _
  have hh : HasSum (fun n : ℕ => smoothDyadicWeight (x/(2 : ℝ)^n))
      (smoothDyadicWeight (x/(2 : ℝ)^0)+(1-dyadicStep x)) := hs.zero_add
  convert hh using 1
  simp only [pow_zero, div_one, smoothDyadicWeight]
  ring

theorem dyadicStep_mul_pow_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => dyadicStep (x*(2 : ℝ)^n)) atTop (𝓝 0) := by
  have he : ∀ᶠ n : ℕ in atTop, dyadicStep (x*(2 : ℝ)^n) = 0 := by
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop ((3/2)/x)] with n hn
    apply dyadicStep_zero
    have hh := (div_le_iff₀ hx).mp hn
    nlinarith
  exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem hasSum_smoothDyadicWeight_neg_scales {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => smoothDyadicWeight (x*(2 : ℝ)^(n+1))) (dyadicStep (2*x)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => (smoothDyadicWeight_bounds _).1) _).mpr
  have he (n : ℕ) : smoothDyadicWeight (x*(2 : ℝ)^(n+1)) =
      dyadicStep ((2*x)*(2 : ℝ)^n)-dyadicStep ((2*x)*(2 : ℝ)^(n+1)) := by
    rw [smoothDyadicWeight, pow_succ]
    congr 1 <;> congr 1 <;> ring
  simp_rw [he, Finset.sum_range_sub' (fun n : ℕ => dyadicStep ((2*x)*(2 : ℝ)^n)),
    pow_zero, mul_one]
  simpa only [sub_zero] using
    (dyadicStep_mul_pow_tendsto (show 0 < 2*x by positivity)).const_sub (dyadicStep (2*x))

/-- Genuine absolute summation over every integer dyadic scale. -/
theorem hasSum_smoothDyadicWeight {x : ℝ} (hx : 0 < x) :
    HasSum (fun j : ℤ => smoothDyadicWeight (x/(2 : ℝ)^j)) 1 := by
  have hpos : HasSum (fun n : ℕ => smoothDyadicWeight (x/(2 : ℝ)^(n : ℤ)))
      (1-dyadicStep (2*x)) := by
    simpa only [zpow_natCast] using hasSum_smoothDyadicWeight_nonneg_scales x
  have hneg : HasSum (fun n : ℕ => smoothDyadicWeight (x/(2 : ℝ)^(-((n : ℤ)+1))))
      (dyadicStep (2*x)) := by
    simpa only [zpow_neg, div_inv_eq_mul, ← Int.natCast_add_one, zpow_natCast] using
      hasSum_smoothDyadicWeight_neg_scales hx
  simpa only [sub_add_cancel] using
    HasSum.of_nat_of_neg_add_one (f := fun j : ℤ => smoothDyadicWeight (x/(2 : ℝ)^j)) hpos hneg

end MathCollab.Density.Stronger
