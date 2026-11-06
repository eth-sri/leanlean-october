module
public import MathCollab.Density.Stronger.Fourth.DigammaSeries

@[expose] public section

open Filter Topology Finset Nat

namespace Complex
export MathCollab.Density.Stronger.Fourth.Digamma (norm_natCast_add_one
  sum_inv_natCast_add_one inv_add_one_sub_inv_eq norm_inv_add_one_sub_inv_le
  summable_one_div_natCast_add_one_sq logGammaSeq logGammaSeq_succ_sub
  cauchySeq_logGammaSeq exp_logGammaSeq hasSum_digamma_of_re_pos)

lemma sum_inv_natCast_add_one_real (n : ℕ) :
    ∑ m ∈ Finset.range n, ((m : ℝ) + 1)⁻¹ = ((harmonic n : ℚ) : ℝ) := by
  rw [harmonic]; push_cast; rfl

lemma hasSum_sub_succ_of_tendsto_zero {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E] {a : ℕ → E} (h0 : Tendsto a atTop (𝓝 0))
    (hs : Summable fun n => a n - a (n + 1)) :
    HasSum (fun n => a n - a (n + 1)) (a 0) := by
  have h1 : Tendsto (fun n => ∑ i ∈ Finset.range n, (a i - a (i + 1))) atTop (𝓝 (a 0)) := by
    simp only [Finset.sum_range_sub']
    simpa using tendsto_const_nhds.sub h0
  have h2 := hs.hasSum
  rwa [tendsto_nhds_unique h2.tendsto_sum_nat h1] at h2

theorem hasSum_digamma {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))
      (digamma z + Real.eulerMascheroniConstant) := by
  suffices h : HasSum (fun m : ℕ => ((m : ℂ) + 1)⁻¹ - (z + m)⁻¹)
      (digamma z + Real.eulerMascheroniConstant) by
    convert h using 1; funext m; rw [one_div, one_div, add_comm (m : ℂ) z]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, -(N : ℝ) < z.re :=
    ⟨⌈-z.re⌉₊ + 1, by have := Nat.le_ceil (-z.re); push_cast; linarith⟩
  induction N generalizing z with
  | zero => exact hasSum_digamma_of_re_pos (by simpa using hN)
  | succ N ih =>
    by_cases hcase : -(N : ℝ) < z.re
    · exact ih hz hcase
    · have hz1 : ∀ n : ℕ, z + 1 ≠ -(n : ℂ) := fun n hcon =>
        hz (n + 1) (by push_cast; linear_combination hcon)
      have hre1 : -(N : ℝ) < (z + 1).re := by rw [add_re, one_re]; push_cast at hN; linarith
      have hih := ih hz1 hre1
      rw [digamma_apply_add_one z hz] at hih
      have hzm : ∀ n : ℕ, z + (n : ℂ) ≠ 0 := fun n hcon => hz n (by linear_combination hcon)
      have hnorm_lb : ∀ n : ℕ, (n : ℝ) - ‖z‖ ≤ ‖z + n‖ := fun n => by
        simpa [sub_neg_eq_add, add_comm] using norm_sub_norm_le (n : ℂ) (-z)
      have ha0 : Tendsto (fun n : ℕ => (z + (n : ℂ))⁻¹) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simp only [norm_inv]
        apply Filter.Tendsto.inv_tendsto_atTop (tendsto_atTop_mono hnorm_lb ?_)
        exact (tendsto_atTop_add_const_right atTop (-‖z‖) tendsto_natCast_atTop_atTop).congr
          fun n => by ring
      have hts : Summable (fun n : ℕ => (z + (n : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹) := by
        apply Summable.of_norm_bounded_eventually_nat
          (g := fun n : ℕ => 4 * (1 / ((n : ℝ) + 1) ^ 2))
          (summable_one_div_natCast_add_one_sq.mul_left _)
        filter_upwards [eventually_ge_atTop ⌈2 * ‖z‖ + 1⌉₊] with n hn
        have hnR : 2 * ‖z‖ + 1 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
        have hb1 : ((n : ℝ) + 1) / 2 ≤ ‖z + n‖ := le_trans (by linarith) (hnorm_lb n)
        have hb2 : ((n : ℝ) + 1) / 2 ≤ ‖z + ((n + 1 : ℕ) : ℂ)‖ :=
          le_trans (by push_cast; linarith) (hnorm_lb (n + 1))
        have hid : (z + (n : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹
            = ((z + n) * (z + ((n + 1 : ℕ) : ℂ)))⁻¹ := by
          have := hzm n; have := hzm (n + 1); field_simp; push_cast; ring
        rw [hid, norm_inv, norm_mul,
          show (4 : ℝ) * (1 / ((n : ℝ) + 1) ^ 2)
            = ((((n : ℝ) + 1) / 2) * (((n : ℝ) + 1) / 2))⁻¹ by field_simp; ring]
        gcongr
      have htel := hasSum_sub_succ_of_tendsto_zero ha0 hts
      simp only [Nat.cast_zero, add_zero] at htel
      have hfin := hih.sub htel
      have e2 : (fun n : ℕ => (((n : ℂ) + 1)⁻¹ - (z + 1 + n)⁻¹)
            - ((z + (n : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹))
          = fun n : ℕ => ((n : ℂ) + 1)⁻¹ - (z + n)⁻¹ := by
        funext n; push_cast; ring
      rw [e2] at hfin
      convert hfin using 1; ring

