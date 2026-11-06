module

public import Mathlib
public import PottsDiscontinuity.Infra.Lambda

/-!
# The asymptotics (1.3) of the hyperbolic series

For `lam(q) = arcosh (√q / 2)` and `T(lam) = ∑_{k ≥ 0} 4 / ((2k+1) sinh (π² (2k+1) / (2 lam)))`
we prove `T(lam(q)) ~ 8 exp (-(π² / √(q - 4)))` as `q → 4⁺` (`asymptotic13`).

With `c = π² / (2 lam)` the series is `H(c) = ∑_k 4 / ((2k+1) sinh ((2k+1) c))`, and Tannery's
theorem shows `exp c * H c → 8` as `c → ∞` (`tendsto_exp_mul_hyperbolic_series`).  The exact
identity `2 sinh (arcosh (√q / 2)) = √(q - 4)` (`two_mul_sinh_arcosh_sqrt_div_two`) turns the
exponent `π² / √(q-4)` into `π² / (2 sinh lam)`, which differs from `c` by `o(1)`
(`tendsto_inv_sinh_sub_inv`).
-/

@[expose] public section

open Filter Topology Real

namespace PottsDiscontinuity

/-! ### Elementary hyperbolic estimates -/

theorem exp_div_four_le_sinh {y : ℝ} (hy : 1 ≤ y) : Real.exp y / 4 ≤ Real.sinh y := by
  rw [Real.sinh_eq, Real.exp_neg]
  have h2 : (2 : ℝ) ≤ Real.exp y * Real.exp y := by
    rw [← Real.exp_add, ← two_mul]; linarith [Real.add_one_le_exp (2 * y)]
  have h3 : (Real.exp y)⁻¹ ≤ Real.exp y / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos y) two_pos]; nlinarith
  linarith

/-- The `k`-th term of the series `H(c)`, multiplied by `exp c`, is at most `16 exp (-2 k c)`
for `c ≥ 1`. -/
theorem term_le {c : ℝ} (hc : 1 ≤ c) (k : ℕ) :
    Real.exp c * (4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))) ≤
      16 * Real.exp (-(2 * (k : ℝ) * c)) := by
  have hk1 : (1 : ℝ) ≤ 2 * (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hs := exp_div_four_le_sinh (by nlinarith : 1 ≤ (2 * (k : ℝ) + 1) * c)
  have hepos := Real.exp_pos ((2 * (k : ℝ) + 1) * c)
  have h1 : 4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c)) ≤
      16 * Real.exp (-((2 * (k : ℝ) + 1) * c)) := by
    refine (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith : Real.exp ((2 * (k : ℝ) + 1) * c) / 4 ≤
        (2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))).trans_eq ?_
    rw [Real.exp_neg]; field_simp; norm_num
  refine (mul_le_mul_of_nonneg_left h1 (Real.exp_pos c).le).trans_eq ?_
  rw [← mul_assoc, mul_comm (Real.exp c) 16, mul_assoc, ← Real.exp_add]
  congr 2; ring

theorem term_nonneg {c : ℝ} (hc : 0 < c) (k : ℕ) :
    0 ≤ Real.exp c * (4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))) := by
  have : 0 < Real.sinh ((2 * (k : ℝ) + 1) * c) := Real.sinh_pos_iff.2 (by positivity)
  positivity

theorem tendsto_term_zero :
    Tendsto (fun c : ℝ => Real.exp c * (4 / ((2 * ((0 : ℕ) : ℝ) + 1) *
      Real.sinh ((2 * ((0 : ℕ) : ℝ) + 1) * c)))) atTop (𝓝 8) := by
  have h1 : Tendsto (fun c : ℝ => Real.exp (-(2 * c))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop two_pos)
  have h2 := (tendsto_const_nhds (x := (8 : ℝ))).div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub h1) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  rw [sub_zero, show (8 : ℝ) / 1 = 8 by norm_num] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  have hpos := Real.exp_pos c
  have h0 : (Real.exp c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_exp_iff.2 hc)
  have hne : Real.exp c - (Real.exp c)⁻¹ ≠ 0 := by linarith [Real.one_lt_exp_iff.2 hc]
  have hne2 : 1 - (Real.exp c)⁻¹ * (Real.exp c)⁻¹ ≠ 0 := by nlinarith [inv_pos.2 hpos]
  simp only [Pi.div_apply, Nat.cast_zero, mul_zero, zero_add, one_mul]
  rw [show Real.exp (-(2 * c)) = (Real.exp c)⁻¹ * (Real.exp c)⁻¹ by
      rw [show -(2 * c) = -c + -c by ring, Real.exp_add, Real.exp_neg],
    Real.sinh_eq, Real.exp_neg]
  field_simp; ring

theorem tendsto_term_zero_of_pos {k : ℕ} (hk : 0 < k) :
    Tendsto (fun c : ℝ => Real.exp c * (4 / ((2 * (k : ℝ) + 1) *
      Real.sinh ((2 * (k : ℝ) + 1) * c)))) atTop (𝓝 0) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine squeeze_zero' (g := fun c => 16 * Real.exp (-(2 * c)))
    (by filter_upwards [eventually_gt_atTop 0] with c hc using term_nonneg hc k)
    (by filter_upwards [eventually_ge_atTop 1] with c hc
        exact (term_le hc k).trans (by gcongr; nlinarith))
    (by simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (two_pos : (0 : ℝ) < 2))).const_mul 16)

/-- **Tannery limit**: `exp c * ∑_k 4 / ((2k+1) sinh ((2k+1) c)) → 8` as `c → ∞`. -/
theorem tendsto_exp_mul_hyperbolic_series :
    Tendsto (fun c : ℝ => Real.exp c *
      ∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))) atTop (𝓝 8) := by
  have hsum : Summable (fun k : ℕ => 16 * (Real.exp (-2)) ^ k) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le (by rw [Real.exp_lt_one_iff]; norm_num)).mul_left 16
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℝ))
    (f := fun (c : ℝ) (k : ℕ) =>
      Real.exp c * (4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))))
    (g := fun k : ℕ => if k = 0 then (8 : ℝ) else 0) hsum
    (fun k => by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa using tendsto_term_zero
      · simpa [Nat.pos_iff_ne_zero.1 hk] using tendsto_term_zero_of_pos hk)
    (by
      filter_upwards [eventually_ge_atTop 1] with c hc k
      rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg (lt_of_lt_of_le one_pos hc) k)]
      refine (term_le hc k).trans ?_
      rw [← Real.exp_nat_mul]
      have : Real.exp (-(2 * (k : ℝ) * c)) ≤ Real.exp ((k : ℝ) * -2) :=
        Real.exp_le_exp.2 (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
      linarith)
  rw [tsum_eq_single 0 (fun b hb => by simp [hb]), ite_eq_left rfl] at hT
  exact hT.congr fun c => tsum_mul_left

/-! ### Comparison of `1 / sinh` and `1 / x` near zero -/

theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  have hd (y : ℝ) : HasDerivAt (fun x : ℝ => x * Real.cosh x - Real.sinh x) (y * Real.sinh y) y := by
    convert ((hasDerivAt_id' y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y) using 1
    ring
  have hmono : MonotoneOn (fun x : ℝ => x * Real.cosh x - Real.sinh x) (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [interior_Ici] at hy; rw [(hd y).deriv]
        exact mul_nonneg hy.le (Real.sinh_nonneg_iff.2 hy.le))
  simpa using hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx

theorem inv_sub_inv_sinh_le {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 / x - 1 / Real.sinh x ∧ 1 / x - 1 / Real.sinh x ≤ (Real.cosh x - 1) / x := by
  have hs : x ≤ Real.sinh x := Real.self_le_sinh_iff.2 hx.le
  have hspos : 0 < Real.sinh x := lt_of_lt_of_le hx hs
  have hc1 : 1 ≤ Real.cosh x := Real.one_le_cosh x
  have hsc := sinh_le_mul_cosh hx.le
  rw [show 1 / x - 1 / Real.sinh x = (Real.sinh x - x) / (x * Real.sinh x) by field_simp]
  exact ⟨by apply div_nonneg <;> nlinarith,
    by rw [div_le_div_iff₀ (by positivity) hx]
       nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hs)]⟩

theorem tendsto_cosh_sub_one_div :
    Tendsto (fun x : ℝ => (Real.cosh x - 1) / x) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.hasDerivAt_cosh 0).tendsto_slope_zero_right
  simp only [Real.sinh_zero, zero_add, Real.cosh_zero, smul_eq_mul] at h
  exact h.congr fun _ => inv_mul_eq_div _ _

theorem tendsto_inv_sinh_sub_inv :
    Tendsto (fun x : ℝ => 1 / Real.sinh x - 1 / x) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => 1 / x - 1 / Real.sinh x) (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero' (by filter_upwards [self_mem_nhdsWithin] with x hx using (inv_sub_inv_sinh_le hx).1)
      (by filter_upwards [self_mem_nhdsWithin] with x hx using (inv_sub_inv_sinh_le hx).2)
      tendsto_cosh_sub_one_div
  simpa using h.neg.congr fun x => by ring

/-! ### The parameter `lam(q) = arcosh (√q / 2)` -/

theorem two_mul_sinh_arcosh_sqrt_div_two {q : ℝ} (hq : 4 < q) :
    2 * Real.sinh (Real.arcosh (Real.sqrt q / 2)) = Real.sqrt (q - 4) := by
  have h2 : (2 : ℝ) < Real.sqrt q := by
    rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]; exact Real.sqrt_lt_sqrt (by norm_num) hq
  rw [Real.sinh_arcosh (by linarith), show (Real.sqrt q / 2) ^ 2 - 1 = (q - 4) / 2 ^ 2 by
      rw [div_pow, Real.sq_sqrt (by linarith)]; ring,
    Real.sqrt_div (by linarith), Real.sqrt_sq (by norm_num)]
  ring

theorem tendsto_arcosh_sqrt_div_two :
    Tendsto (fun q : ℝ => Real.arcosh (Real.sqrt q / 2)) (𝓝[>] 4) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, by filter_upwards [self_mem_nhdsWithin] with q hq using (arcosh_pos_of_gt4 q hq).1⟩
  have h1 : Tendsto (fun q : ℝ => q - 4) (𝓝[>] 4) (𝓝 0) := by
    simpa using tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (4 : ℝ))
      ((by fun_prop : Continuous fun q : ℝ => q - 4).tendsto 4)
  have h3 := (Real.continuous_arsinh.tendsto 0).comp
    (by simpa using ((Real.continuous_sqrt.tendsto 0).comp h1).div_const 2 :
      Tendsto (fun q : ℝ => Real.sqrt (q - 4) / 2) (𝓝[>] 4) (𝓝 0))
  rw [Real.arsinh_zero] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [Function.comp, ← two_mul_sinh_arcosh_sqrt_div_two hq,
    mul_div_cancel_left₀ _ (two_ne_zero' ℝ), Real.arsinh_sinh]

/-! ### The asymptotic equivalence -/

theorem asymptotic13 :
    Asymptotics.IsEquivalent (𝓝[>] (4 : ℝ))
      (fun q => ∑' k : ℕ, 4 / ((2 * k + 1) *
        Real.sinh (π ^ 2 * (2 * k + 1) / (2 * Real.arcosh (Real.sqrt q / 2)))))
      (fun q => 8 * Real.exp (-(π ^ 2 / Real.sqrt (q - 4)))) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  set L : ℝ → ℝ := fun q => Real.arcosh (Real.sqrt q / 2) with hL
  have hLt : Tendsto L (𝓝[>] 4) (𝓝[>] 0) := tendsto_arcosh_sqrt_div_two
  have hc : Tendsto (fun q => π ^ 2 / 2 * (L q)⁻¹) (𝓝[>] 4) atTop :=
    Tendsto.const_mul_atTop (by positivity) (tendsto_inv_nhdsGT_zero.comp hLt)
  have hd : Tendsto (fun q => π ^ 2 / Real.sqrt (q - 4) - π ^ 2 / 2 * (L q)⁻¹) (𝓝[>] 4) (𝓝 0) := by
    have h1 := (tendsto_inv_sinh_sub_inv.comp hLt).const_mul (π ^ 2 / 2)
    simp only [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [Function.comp, ← two_mul_sinh_arcosh_sqrt_div_two hq]
    have hpos : 0 < Real.sinh (L q) := Real.sinh_pos_iff.2 (arcosh_pos_of_gt4 q hq).1
    simp only [hL] at hpos ⊢; field_simp
  have hlim := ((tendsto_exp_mul_hyperbolic_series.comp hc).div_const 8).mul hd.rexp
  simp only [Real.exp_zero, mul_one, show (8 : ℝ) / 8 = 1 by norm_num] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q (hq : 4 < q)
  have hLpos : 0 < L q := (arcosh_pos_of_gt4 q hq).1
  have hsq : 0 < Real.sqrt (q - 4) := Real.sqrt_pos.2 (by linarith)
  simp only [Function.comp, Pi.div_apply]
  set c := π ^ 2 / 2 * (L q)⁻¹ with hcdef
  set s := π ^ 2 / Real.sqrt (q - 4)
  rw [show (∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) *
        Real.sinh (π ^ 2 * (2 * k + 1) / (2 * Real.arcosh (Real.sqrt q / 2))))) =
      ∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c)) from
    tsum_congr fun k => by congr 3; simp only [hcdef, hL]; field_simp]
  generalize (∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))) = H
  rw [Real.exp_sub, Real.exp_neg]
  have h1 := Real.exp_pos c
  have h2 := Real.exp_pos s
  field_simp

end PottsDiscontinuity
