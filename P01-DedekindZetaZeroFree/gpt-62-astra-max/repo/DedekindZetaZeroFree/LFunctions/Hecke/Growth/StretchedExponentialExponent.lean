module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

theorem stretchedExp_envelope_exponent_le (a p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 ≤ R →
      (R / p) * Real.log (2 + 2 * R / (a * p)) ≤
        K * (1 + R) * Real.log (2 + R) := by
  have hap := mul_pos ha hp
  have h2ap : 0 ≤ 2 / (a * p) := div_nonneg (by norm_num) hap.le
  set c : ℝ := 2 + 2 / (a * p) with hc_def
  have hc1 : 1 < c := by
    have : 0 < 2 / (a * p) := by positivity
    simp only [hc_def]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogc := Real.log_pos hc1
  have hB : 0 ≤ 1 + Real.log c / Real.log 2 := by
    have := div_nonneg hlogc.le hlog2.le
    linarith
  refine ⟨(1 / p) * (1 + Real.log c / Real.log 2), ?_, ?_⟩
  · positivity
  · intro R hR
    have hR2 : 0 < 2 + R := by linarith
    have hbase_pos : 0 < 2 + 2 * R / (a * p) := by
      have : 0 ≤ 2 * R / (a * p) := div_nonneg (by nlinarith) hap.le
      linarith

    have hle : 2 + 2 * R / (a * p) ≤ c * (2 + R) := by
      have h1 : 2 * R / (a * p) = (2 / (a * p)) * R := by ring
      rw [hc_def, h1]
      nlinarith [hR, h2ap, div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hap.le,
        div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hap.le, mul_nonneg h2ap hR]

    have hD : Real.log c ≤ (Real.log c / Real.log 2) * Real.log (2 + R) := by
      have h1 : Real.log 2 ≤ Real.log (2 + R) :=
        Real.log_le_log (by norm_num) (by linarith)
      have h2 : (Real.log c / Real.log 2) * Real.log 2 ≤
          (Real.log c / Real.log 2) * Real.log (2 + R) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hlogc.le hlog2.le)
      rwa [div_mul_cancel₀ (Real.log c) (ne_of_gt hlog2)] at h2
    have hmain : Real.log (2 + 2 * R / (a * p)) ≤
        (1 + Real.log c / Real.log 2) * Real.log (2 + R) := by
      have hC : Real.log (2 + 2 * R / (a * p)) ≤ Real.log (c * (2 + R)) :=
        Real.log_le_log hbase_pos hle
      rw [Real.log_mul (ne_of_gt (lt_trans zero_lt_one hc1)) (ne_of_gt hR2)] at hC
      nlinarith [hC, hD]
    refine (mul_le_mul_of_nonneg_left hmain (by positivity)).trans ?_
    have hEq1 : (R / p) * ((1 + Real.log c / Real.log 2) * Real.log (2 + R))
        = R * ((1 / p) * (1 + Real.log c / Real.log 2) * Real.log (2 + R)) := by ring
    have hEq2 : ((1 / p) * (1 + Real.log c / Real.log 2)) * (1 + R) * Real.log (2 + R)
        = (1 + R) * ((1 / p) * (1 + Real.log c / Real.log 2) * Real.log (2 + R)) := by
      ring
    rw [hEq1, hEq2]
    exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (mul_nonneg (by positivity) hB) (Real.log_nonneg (by linarith)))

end DedekindZetaZeroFree.Hecke
