module

public import Mathlib.Tactic

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

theorem rlogr_le_rpow_add_const (K : ℝ) (hK : 0 ≤ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 0 ≤ R →
      K * (1 + R) * Real.log (2 + R) ≤ Real.rpow R (1 + ε) + B := by
  have hc : 0 < 1 / (4 * (K + 1)) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((isLittleO_log_rpow_atTop hε).bound hc)
  let M := max 3 N
  have hM : 3 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := by linarith
  have hB : 0 ≤ K * (1 + M) * Real.log (2 + M) :=
    mul_nonneg (mul_nonneg hK (by linarith)) (Real.log_nonneg (by linarith))
  refine ⟨K * (1 + M) * Real.log (2 + M), hB, ?_⟩
  intro R hR
  by_cases hRM : R ≤ M
  · exact le_trans (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hK) (Real.log_le_log (by linarith) (by linarith))
      (Real.log_nonneg (by linarith)) (mul_nonneg hK (by linarith))) (le_add_of_nonneg_left (Real.rpow_nonneg hR _))
  let log₀ := Real.log (2 + R)
  · have hMR := le_of_lt (lt_of_not_ge hRM)
    have h3 := le_trans hM hMR
    have hRpos : 0 < R := by linarith
    have hbound' : Real.log R ≤ (1 / (4 * (K + 1))) * R ^ ε := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)), abs_of_nonneg (Real.rpow_nonneg hR ε)] using (hN R (le_trans (le_max_right _ _) hMR))
    have hlog : log₀ ≤ 2 * Real.log R := by
      calc
        log₀ ≤ Real.log (3 * R) :=
          Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 3 + Real.log R := Real.log_mul (by norm_num) (ne_of_gt hRpos)
        _ ≤ 2 * Real.log R := by
          have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) h3
          linarith
    have hprod : K * (1 + R) * log₀ ≤
        (4 * K * (1 / (4 * (K + 1)))) * (R * R ^ ε) := by
      calc
        K * (1 + R) * log₀ ≤ (K * (2 * R)) * (2 * Real.log R) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hK) hlog
            (Real.log_nonneg (by linarith)) (by positivity)
        _ = (4 * K * R) * Real.log R := by ring
        _ ≤ (4 * K * R) * ((1 / (4 * (K + 1))) * R ^ ε) :=
          mul_le_mul_of_nonneg_left hbound' (by positivity)
        _ = _ := by ring
    have hcoef : 4 * K * (1 / (4 * (K + 1))) ≤ 1 := by
      have hden : 0 < 4 * (K + 1) := by positivity
      rw [mul_one_div]
      apply (div_le_iff₀ hden).2
      nlinarith
    refine le_trans ?_ (le_add_of_nonneg_right hB)
    calc
    _ ≤ (4 * K * (1 / (4 * (K + 1)))) * (R * R ^ ε) := hprod
    _ ≤ 1 * (R * R ^ ε) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = R ^ (1 + ε) := by simp_all [Real.rpow_add]

theorem orderOneBound_of_rlogr (H : ℂ → ℂ) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hH : ∀ s : ℂ, ‖H s‖ ≤
      C * Real.exp (K * (1 + ‖s‖) * Real.log (2 + ‖s‖))) :
    ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ s : ℂ,
      ‖H s‖ ≤ Cε * Real.exp (‖s‖ ^ (1 + ε)) := by
  intro ε hε
  obtain ⟨B, _, hB⟩ := rlogr_le_rpow_add_const K hK ε hε
  refine ⟨C * Real.exp B, ?_⟩
  intro s
  calc
    _ ≤ C * Real.exp (K * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := hH s
    _ ≤ C * Real.exp (‖s‖ ^ (1 + ε) + B) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hB ‖s‖ (norm_nonneg s))) hC
    _ = (C * Real.exp B) * Real.exp (‖s‖ ^ (1 + ε)) := by
      rw [Real.exp_add]
      ring

end DedekindZetaZeroFree.Hecke
