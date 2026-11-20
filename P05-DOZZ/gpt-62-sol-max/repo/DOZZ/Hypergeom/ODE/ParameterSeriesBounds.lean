/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesTerms

/-! Uniform tail estimates for the parameter-dependent ordinary Gauss series. -/

@[expose] public section

namespace DOZZ.Proofs

theorem gauss_norm_natCast_add_le {a : ℂ} {R : ℝ} (n : ℕ) (h : ‖a‖ ≤ R) :
    ‖(n : ℂ) + a‖ ≤ (n : ℝ) + R := by
  simpa only [Complex.norm_natCast] using (norm_add_le (n : ℂ) a).trans (add_le_add_right h _)

theorem gauss_sub_le_norm_natCast_add {a : ℂ} {R : ℝ} (n : ℕ) (h : ‖a‖ ≤ R) :
    (n : ℝ) - R ≤ ‖(n : ℂ) + a‖ := by
  have h' := norm_sub_norm_le (n : ℂ) ((n : ℂ) + a)
  simp only [Complex.norm_natCast, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg] at h'
  linarith

/-- The scalar term multiplier contracts uniformly once the index dominates a compact parameter
bound and the point lies strictly inside the unit disk. -/
theorem gaussParameterSeriesRatio_norm_le
    (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ) (R q : ℝ) (hR : 0 ≤ R) (hRn : R < (n : ℝ))
    (hA : ‖p.1‖ ≤ R) (hB : ‖p.2.1‖ ≤ R) (hC : ‖p.2.2‖ ≤ R)
    (hRatio : ‖z‖ * ((n : ℝ) + R) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) - R)) ≤ q) :
    ‖gaussParameterSeriesRatio p z n‖ ≤ q := by
  have ha := gauss_norm_natCast_add_le n hA
  have hb := gauss_norm_natCast_add_le n hB
  have hc := gauss_sub_le_norm_natCast_add n hC
  have hpos : 0 < (n : ℝ) - R := sub_pos.mpr hRn
  refine le_trans ?_ hRatio
  simp only [gaussParameterSeriesRatio, norm_div, norm_mul]
  rw [show ‖(n + 1 : ℂ)‖ = (n : ℝ) + 1 by norm_cast, mul_comm ‖z‖, pow_two]
  gcongr

/-- Once the denominator index dominates all three parameter norms, successive ordinary-series
terms contract at a rate controlled by the elementary hypergeometric coefficient ratio. -/
theorem gaussParameterSeriesTerm_norm_succ_le
    (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ) (R q : ℝ)
    (hR : 0 ≤ R) (hRn : R < n)
    (hA : ‖p.1‖ ≤ R) (hB : ‖p.2.1‖ ≤ R) (hC : ‖p.2.2‖ ≤ R)
    (hRatio : ‖z‖ * ((n : ℝ) + R) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) - R)) ≤ q)
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) :
    ‖gaussParameterSeriesTerm p z (n + 1)‖ ≤
      q * ‖gaussParameterSeriesTerm p z n‖ := by
  rw [gaussParameterSeriesTerm_recurrence p z n (hc n), norm_mul]
  exact mul_le_mul_of_nonneg_right (gaussParameterSeriesRatio_norm_le p z n R q hR hRn hA hB hC hRatio)
    (norm_nonneg _)

/-- A uniform tail threshold for the elementary term-ratio bound on a disk strictly inside the
unit circle. -/
theorem exists_nat_uniform_gaussParameterSeries_ratio_bound
    (z : ℂ) (hz : ‖z‖ < 1) (R : ℝ) (hR : 0 ≤ R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R < (n : ℝ) ∧
      ‖z‖ * ((n : ℝ) + R) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) - R)) ≤ (1 + ‖z‖) / 2 := by
  let q : ℝ := (1 + ‖z‖) / 2
  let g : ℝ → ℝ := fun t => ‖z‖ * (1 + t) ^ 2 / (1 - t)
  have hq : ‖z‖ < q := by dsimp [q]; linarith
  have hg0 : g 0 = ‖z‖ := by simp [g]
  have hgcont : ContinuousAt g 0 := by
    dsimp [g]
    fun_prop (disch := norm_num)
  obtain ⟨ε, hε, hnear⟩ :=
    (Metric.continuousAt_iff.mp hgcont) ((q - ‖z‖) / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (R / ε) R)
  refine ⟨N, ?_⟩
  intro n hNn
  have hNreal : max (R / ε) R < (N : ℝ) := by exact_mod_cast hN
  have hnreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hnR : R < (n : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hNreal) hnreal
  have hnpos : 0 < (n : ℝ) := by linarith
  have hRat : R / ε < (n : ℝ) :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hNreal) hnreal
  have hRlt : R < ε * (n : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hRat
  have ht : 0 ≤ R / (n : ℝ) := div_nonneg hR hnpos.le
  have htn : R / (n : ℝ) < ε := (div_lt_iff₀ hnpos).2 hRlt
  have hnear' := hnear (x := R / (n : ℝ)) (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht]
    exact htn)
  have hgBound : g (R / (n : ℝ)) < q := by
    rw [Real.dist_eq, hg0, abs_sub_lt_iff] at hnear'
    dsimp [q] at hnear' hq ⊢
    linarith
  have htnlt1 : R / (n : ℝ) < 1 := by
    apply (div_lt_iff₀ hnpos).2
    simpa using hnR
  have hdenpos : 0 < 1 - R / (n : ℝ) := by linarith
  have hdenlarger : 1 - R / (n : ℝ) ≤
      (1 + 1 / (n : ℝ)) * (1 - R / (n : ℝ)) := by
    have hInv : 0 ≤ 1 / (n : ℝ) := by positivity
    nlinarith [mul_nonneg hInv (le_of_lt hdenpos)]
  have hnumNonneg : 0 ≤ ‖z‖ * (1 + R / (n : ℝ)) ^ 2 :=
    mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hquot :
      ‖z‖ * (1 + R / (n : ℝ)) ^ 2 /
          ((1 + 1 / (n : ℝ)) * (1 - R / (n : ℝ))) ≤
        g (R / (n : ℝ)) := by
    dsimp [g]
    exact div_le_div_of_nonneg_left hnumNonneg hdenpos hdenlarger
  have hratioEq :
      ‖z‖ * ((n : ℝ) + R) ^ 2 /
          (((n : ℝ) + 1) * ((n : ℝ) - R)) =
        ‖z‖ * (1 + R / (n : ℝ)) ^ 2 /
          ((1 + 1 / (n : ℝ)) * (1 - R / (n : ℝ))) := by
    field_simp [hnpos.ne']
  refine ⟨hnR, ?_⟩
  rw [hratioEq]
  exact hquot.trans hgBound.le


/-- Compactness bounds every fixed finite prefix of the parameterized Gauss series uniformly. -/
theorem exists_finite_prefix_uniform_gaussParameterSeriesTerm_bound
    {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K)
    (hc : ∀ p ∈ K, ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) (z : ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ K,
      ‖gaussParameterSeriesTerm p z n‖ ≤ C := by
  have hb : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ K,
      ‖gaussParameterSeriesTerm p z n‖ ≤ B := by
    intro n
    let f : ℂ × ℂ × ℂ → ℝ := fun p => ‖gaussParameterSeriesTerm p z n‖
    have hf : ContinuousOn f K := by
      exact (gaussParameterSeriesTerm_differentiableOn hc z n).continuousOn.norm
    obtain ⟨B, hB⟩ := bddAbove_def.mp (hK.bddAbove_image hf)
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro p hp
    have hle := hB (f p) ⟨p, hp, rfl⟩
    exact le_trans hle (le_max_left _ _)
  choose B hBnonneg hB using hb
  let C : ℝ := ∑ n ∈ Finset.range (N + 1), B n
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun k hk => hBnonneg k
  refine ⟨C, hC, ?_⟩
  intro n hn p hp
  have hnmem : n ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
  calc
    ‖gaussParameterSeriesTerm p z n‖ ≤ B n := hB n p hp
    _ ≤ ∑ k ∈ Finset.range (N + 1), B k := by
      apply Finset.single_le_sum <;> solve_by_elim

end DOZZ.Proofs
