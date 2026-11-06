module
public import GuthMaynard.Improvement.ShortDensityHeight
import WeylPort.Analytic.RealLaplace

public section

namespace GuthMaynard.Improvement

/-- Four exact exponent comparisons for the padded upper window. -/
theorem upper_window_exponents {σ : ℝ} (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) :
    (9/4)*(1-σ) ≤ (39/17)*(1-σ) ∧
    39/14-3*σ ≤ (39/17)*(1-σ) ∧
    63/20-7*σ/2 ≤ (39/17)*(1-σ) ∧
    15/8-7*σ/4 ≤ (39/17)*(1-σ) := by grind

/-- Length losses and the first large-value term in the fixed powered window. -/
theorem upper_window_length_budgets {σ H N δ : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H) (hN : 0 ≤ N)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/100) (hhi : N ≤ H^(9/8+δ)) :
    N^δ ≤ H^(2*δ) ∧
    N^(2-2*σ) ≤ H^((39/17)*(1-σ)+2*δ) := by pm_4580 upper_window_exponents

section
variable {σ H N : ℝ} (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H)
include σ H N hσ hσ' hH
/-- Padding the time interval preserves the exact middle-range hypotheses and
bounds the second term up to length H^(7/8). No sampling assumption is added. -/
theorem upper_window_padded_time (hN : 2 ≤ N)
    (hlo : H^(3/4:ℝ) ≤ N) (hhi : N ≤ H^(7/8:ℝ)) :
    ∃ S : ℝ, N^(6/5:ℝ) ≤ S ∧ S ≤ N^(5/3:ℝ) ∧ H ≤ S ∧
      N^(18/7-4*σ)*S^(6/7:ℝ) ≤ H^((39/17)*(1-σ)) := by
  pm_4583
  have he := upper_window_exponents hσ hσ'
  pm_4581
  · refine ⟨N^(6/5:ℝ),le_rfl,?_,?_,?_⟩
    pm_4582
    · calc
        _ = N^(18/5-4*σ) := by
          pm_694
        _ ≤ (H^(7/8:ℝ))^(18/5-4*σ) :=
          Real.rpow_le_rpow hN0.le hhi (by linarith)
        _ = H^(63/20-7*σ/2) := by rw [← Real.rpow_mul hH0.le]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH he.2.2.1

/-- Ordinary mean value closes lengths above the second split. -/
theorem upper_window_mean_budget
    (hlo : H^(7/8:ℝ) ≤ N) :
    H*N^(1-2*σ) ≤ H^((39/17)*(1-σ)) := by
  have hH0 : 0 < H := by linarith
  calc
    _ ≤ H*(H^(7/8:ℝ))^(1-2*σ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by linarith)) hH0.le
    _ = H^(15/8-7*σ/4) := by
      pm_4535
      pm_4975 Real.rpow_add hH0
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH (upper_window_exponents hσ hσ').2.2.2
end

/-- Threshold algebra retains the original H even when the time is padded. -/
theorem upper_window_padded_denominator {H N : ℝ} (hH : 0 < H) (hN : 0 < N)
    (S σ δ : ℝ) :
    N^(18/7:ℝ)*S^(6/7:ℝ)/(N^σ*H^(-2*δ))^4 =
      (N^(18/7-4*σ)*S^(6/7:ℝ))*H^(8*δ) := by
  pm_4594
  have hn4 : N^(18/7-4*σ) = N^(18/7:ℝ)/(N^σ)^4 := by
    rw [Real.rpow_sub hN,show 4*σ = σ*4 by ring,
      Real.rpow_mul hN.le σ 4,Real.rpow_ofNat]
  have hh8 : H^(8*δ) = (H^δ)^8 := by
    rw [show 8*δ = δ*8 by ring,Real.rpow_mul hH.le δ 8,Real.rpow_ofNat]
  rw [hV,hn4,hh8]
  field_simp

end GuthMaynard.Improvement
