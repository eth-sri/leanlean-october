module

public import Mathlib
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.Infra.Lambda

/-! # Proof of Theorem 1.2, positivity and (1.3) (`rc_theorem_1_2_positivity_eq_1_3`) -/

@[expose] public section

namespace PottsDiscontinuity.Provider

open MeasureTheory Filter Topology Real

private theorem asymptotic13 :
    Asymptotics.IsEquivalent (𝓝[>] (4 : ℝ))
      (fun q => ∑' k : ℕ, 4 / ((2 * k + 1) *
        Real.sinh (π ^ 2 * (2 * k + 1) / (2 * Real.arcosh (Real.sqrt q / 2)))))
      (fun q => 8 * Real.exp (-(π ^ 2 / Real.sqrt (q - 4)))) := by
  have hterm_le {c : ℝ} (hc : 1 ≤ c) (k : ℕ) :
      Real.exp c * (4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))) ≤
        16 * Real.exp (-(2 * (k : ℝ) * c)) := by
    let y := (2 * (k : ℝ) + 1) * c
    have hy : 1 ≤ y := by dsimp [y]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hexp_sinh : Real.exp y / 4 ≤ Real.sinh y := by
      rw [Real.sinh_eq, Real.exp_neg]
      have hpos := Real.exp_pos y
      have h2 : (2 : ℝ) ≤ Real.exp y * Real.exp y := by
        rw [← Real.exp_add, ← two_mul]; linarith [Real.add_one_le_exp (2 * y)]
      have h3 : (Real.exp y)⁻¹ ≤ Real.exp y / 2 := by
        rw [inv_eq_one_div, div_le_div_iff₀ hpos two_pos]; nlinarith
      linarith
    have h1 : 4 / ((2 * (k : ℝ) + 1) * Real.sinh y) ≤ 16 * Real.exp (-y) := by
      calc 4 / ((2 * (k : ℝ) + 1) * Real.sinh y) ≤ 4 / (Real.exp y / 4) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (by nlinarith [hexp_sinh, Nat.cast_nonneg (α := ℝ) k, Real.sinh_nonneg_iff.2 (show 0 ≤ y by linarith)])
        _ = 16 * Real.exp (-y) := by rw [Real.exp_neg]; field_simp; norm_num
    calc Real.exp c * (4 / ((2 * (k : ℝ) + 1) * Real.sinh y))
        ≤ Real.exp c * (16 * Real.exp (-y)) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos c).le
      _ = 16 * Real.exp (-(2 * (k : ℝ) * c)) := by
          rw [← mul_assoc, mul_comm (Real.exp c) 16, mul_assoc, ← Real.exp_add]; congr 2; dsimp [y]; ring
  have hterm_nn {c : ℝ} (hc : 0 < c) (k : ℕ) :
      0 ≤ Real.exp c * (4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))) := by
    have : 0 < Real.sinh ((2 * (k : ℝ) + 1) * c) := Real.sinh_pos_iff.2 (by positivity)
    positivity
  have hTannery : Tendsto (fun c : ℝ => Real.exp c *
      ∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))) atTop (𝓝 8) := by
    have hsum : Summable (fun k : ℕ => 16 * (Real.exp (-2)) ^ k) :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le (by rw [Real.exp_lt_one_iff]; norm_num)).mul_left 16
    have ht0 : Tendsto (fun c : ℝ => Real.exp c * (4 / ((2 * ((0 : ℕ) : ℝ) + 1) *
        Real.sinh ((2 * ((0 : ℕ) : ℝ) + 1) * c)))) atTop (𝓝 8) := by
      have h1 : Tendsto (fun c : ℝ => Real.exp (-(2 * c))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop two_pos)
      have h2 : Tendsto (fun c : ℝ => 8 / (1 - Real.exp (-(2 * c)))) atTop (𝓝 8) := by
        simpa [Pi.div_def] using (tendsto_const_nhds (x := (8 : ℝ))).div
          ((tendsto_const_nhds (x := (1 : ℝ))).sub h1) (by norm_num : (1 : ℝ) - 0 ≠ 0)
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with c hc
      have hgt : 1 < Real.exp c := Real.one_lt_exp_iff.2 hc
      have hinv1 : (Real.exp c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
      have hinv0 : 0 < (Real.exp c)⁻¹ := inv_pos.2 (Real.exp_pos c)
      have hne : Real.exp c - (Real.exp c)⁻¹ ≠ 0 := by linarith
      have hne2 : 1 - (Real.exp c)⁻¹ * (Real.exp c)⁻¹ ≠ 0 := by nlinarith
      simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]
      rw [show Real.exp (-(2 * c)) = (Real.exp c)⁻¹ * (Real.exp c)⁻¹ by
        rw [show -(2 * c) = -c + -c by ring, Real.exp_add, Real.exp_neg], Real.sinh_eq, Real.exp_neg]
      field_simp; ring
    have htk {k : ℕ} (hk : 0 < k) : Tendsto (fun c : ℝ => Real.exp c * (4 / ((2 * (k : ℝ) + 1) *
        Real.sinh ((2 * (k : ℝ) + 1) * c)))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun c : ℝ => 16 * Real.exp (-(2 * c))) atTop (𝓝 0) := by
        simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop two_pos)).const_mul 16
      refine squeeze_zero' (by filter_upwards [eventually_gt_atTop 0] with c hc using hterm_nn hc k) ?_ h1
      filter_upwards [eventually_ge_atTop 1] with c hc
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      refine (hterm_le hc k).trans ?_
      gcongr; nlinarith
    have hT := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℝ))
      (f := fun (c : ℝ) (k : ℕ) => Real.exp c * (4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))))
      (g := fun k : ℕ => if k = 0 then (8 : ℝ) else 0) hsum
      (fun k => by
        by_cases hk : k = 0
        · subst hk; simpa using ht0
        · simpa [hk] using htk (Nat.pos_of_ne_zero hk))
      (by filter_upwards [eventually_ge_atTop 1] with c hc k
          rw [Real.norm_eq_abs, abs_of_nonneg (hterm_nn (lt_of_lt_of_le one_pos hc) k)]
          refine (hterm_le hc k).trans ?_
          rw [← Real.exp_nat_mul]
          have : Real.exp (-(2 * (k : ℝ) * c)) ≤ Real.exp ((k : ℝ) * -2) :=
            Real.exp_le_exp.2 (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
          linarith)
    rw [tsum_eq_single 0 (fun b hb => by simp [hb]), if_pos rfl] at hT
    exact hT.congr fun _ => tsum_mul_left
  have hinv_diff : Tendsto (fun x : ℝ => 1 / Real.sinh x - 1 / x) (𝓝[>] 0) (𝓝 0) := by
    have hsc {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
      have hd (y : ℝ) : HasDerivAt (fun t : ℝ => t * Real.cosh t - Real.sinh t) (y * Real.sinh y) y := by
        convert ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y) using 1
        · rfl
        · simp only [id]; ring
      have hm := monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun y _ => (hd y).continuousAt.continuousWithinAt)
        (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
        (fun y hy => by rw [interior_Ici] at hy; rw [(hd y).deriv]; exact mul_nonneg hy.le (Real.sinh_nonneg_iff.2 hy.le))
        (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
      simpa using hm
    have hslope : Tendsto (fun x : ℝ => (Real.cosh x - 1) / x) (𝓝[>] 0) (𝓝 0) := by
      have h := (Real.hasDerivAt_cosh 0).tendsto_slope_zero_right
      simp only [Real.sinh_zero, zero_add, Real.cosh_zero, smul_eq_mul] at h
      exact h.congr fun _ => inv_mul_eq_div _ _
    have hpos : Tendsto (fun x : ℝ => 1 / x - 1 / Real.sinh x) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ hslope <;> filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      · have hs := Real.self_le_sinh_iff.2 hx.le
        have : 0 < Real.sinh x := lt_of_lt_of_le hx hs
        rw [show 1 / x - 1 / Real.sinh x = (Real.sinh x - x) / (x * Real.sinh x) by field_simp]
        exact div_nonneg (by linarith) (by positivity)
      · have hs := Real.self_le_sinh_iff.2 hx.le
        have : 0 < Real.sinh x := lt_of_lt_of_le hx hs
        have hc1 := Real.one_le_cosh x
        have := hsc hx.le
        rw [show 1 / x - 1 / Real.sinh x = (Real.sinh x - x) / (x * Real.sinh x) by field_simp, div_le_div_iff₀ (by positivity) hx]
        nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hs)]
    simpa only [neg_zero] using hpos.neg.congr fun _ => by ring
  have hsinh_arc {q : ℝ} (hq : 4 < q) : 2 * Real.sinh (Real.arcosh (Real.sqrt q / 2)) = Real.sqrt (q - 4) := by
    have h2 : (2 : ℝ) < Real.sqrt q := by
      rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]; exact Real.sqrt_lt_sqrt (by norm_num) hq
    rw [Real.sinh_arcosh (by linarith), show (Real.sqrt q / 2) ^ 2 - 1 = (q - 4) / 2 ^ 2 by
      rw [div_pow, Real.sq_sqrt (by linarith)]; ring, Real.sqrt_div (by linarith), Real.sqrt_sq (by norm_num)]; ring
  let L : ℝ → ℝ := fun q => Real.arcosh (Real.sqrt q / 2)
  have hLt : Tendsto L (𝓝[>] 4) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, by filter_upwards [self_mem_nhdsWithin] with q hq using (arcosh_pos_of_gt4 q hq).1⟩
    have hsub : Tendsto (fun q : ℝ => q - 4) (𝓝[>] 4) (𝓝 0) := by
      simpa using tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (4 : ℝ)) ((by fun_prop : Continuous fun q : ℝ => q - 4).tendsto 4)
    have hs : Tendsto (fun q : ℝ => Real.sqrt (q - 4) / 2) (𝓝[>] 4) (𝓝 0) := by
      simpa using ((Real.continuous_sqrt.tendsto 0).comp hsub).div_const 2
    have h3 := (Real.continuous_arsinh.tendsto 0).comp hs
    rw [Real.arsinh_zero] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q (hq : 4 < q)
    simp only [Function.comp_def, ← hsinh_arc hq]
    rw [show 2 * Real.sinh (Real.arcosh (Real.sqrt q / 2)) / 2 = Real.sinh (L q) by dsimp [L]; ring, Real.arsinh_sinh]
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hc : Tendsto (fun q => π ^ 2 / 2 * (L q)⁻¹) (𝓝[>] 4) atTop :=
    Tendsto.const_mul_atTop (by positivity) (tendsto_inv_nhdsGT_zero.comp hLt)
  have hd : Tendsto (fun q => π ^ 2 / Real.sqrt (q - 4) - π ^ 2 / 2 * (L q)⁻¹) (𝓝[>] 4) (𝓝 0) := by
    have h1 := (hinv_diff.comp hLt).const_mul (π ^ 2 / 2)
    simp only [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q (hq : 4 < q)
    have hpos : 0 < Real.sinh (L q) := Real.sinh_pos_iff.2 (arcosh_pos_of_gt4 q hq).1
    simp only [Function.comp_def, ← hsinh_arc hq]; dsimp only [L] at hpos ⊢; field_simp
  have hlim := ((hTannery.comp hc).div_const 8).mul hd.rexp
  rw [Real.exp_zero, mul_one, show (8 : ℝ) / 8 = 1 by norm_num] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q (hq : 4 < q)
  have hLpos : 0 < L q := (arcosh_pos_of_gt4 q hq).1
  simp only [Function.comp_def, Pi.div_apply]
  let c := π ^ 2 / 2 * (L q)⁻¹
  have hu : (∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * k + 1) / (2 * L q)))) =
      ∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c)) :=
    tsum_congr fun k => by congr 3; dsimp [c]; field_simp
  dsimp only [L] at hLpos hu ⊢; rw [hu]
  generalize (∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh ((2 * (k : ℝ) + 1) * c))) = H
  rw [Real.exp_sub, Real.exp_neg]
  have := Real.exp_pos c; have := Real.exp_pos (π ^ 2 / Real.sqrt (q - 4))
  field_simp

/-- The proof of `rc_theorem_1_2_positivity_eq_1_3`: positivity of (1.2) and asymptotics (1.3). -/
theorem rc_theorem_1_2_positivity_eq_1_3 :
    (∀ q : ℝ, 4 < q → ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
      ∃ S T : ℝ,
        Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
        HasSum (fun k : ℕ => 4 / ((2 * k + 1) * Real.sinh (π ^ 2 * (2 * k + 1) / (2 * lam)))) T ∧
        0 < lam + 2 * S ∧ lam + 2 * S = T) ∧
    Asymptotics.IsEquivalent (𝓝[>] (4 : ℝ))
      (fun q => ∑' k : ℕ, 4 / ((2 * k + 1) *
        Real.sinh (π ^ 2 * (2 * k + 1) / (2 * Real.arcosh (Real.sqrt q / 2)))))
      (fun q => 8 * Real.exp (-(π ^ 2 / Real.sqrt (q - 4)))) :=
  ⟨fun _ _ lam hlam _ => identity44 lam hlam, asymptotic13⟩

end PottsDiscontinuity.Provider
