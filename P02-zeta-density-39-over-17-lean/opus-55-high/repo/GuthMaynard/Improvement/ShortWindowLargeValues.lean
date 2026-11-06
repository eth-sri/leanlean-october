module
public import GuthMaynard.Improvement.ShortDensityHeight
import WeylPort.Analytic.RealLaplace

public section

open Finset
namespace GuthMaynard.Improvement

/-- Actual large values throughout the powered detector window. Constants are
uniform in sigma; the upper length buffer and normalized height loss are
charged explicitly. The middle theorem is used only in its exact range. -/
theorem short_window_large_values {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ H N t₀ : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
      9/13 ≤ σ → σ ≤ 5/7 → 2 ≤ H → 2 ≤ N →
      H^(shortDensityA σ) ≤ N → N ≤ H^(shortDensityB σ+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+H) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*H^(-2*δ) ≤ ‖boundedPolynomial N a t‖) →
      (W.card:ℝ) ≤ C*H^(shortDensityExponent σ+10*δ) := by
  pm_4528
  have hsmall := short_density_small_power hσ hσ' hH1 hN0.le hδ.le hδ' hhi
  have hpos := short_density_positive_budget hσ hσ' hH1 hN0.le hδ.le hhi
  pm_97 hdiv2 hdiv4 hdivM short_density_height_budgets hH0 hN0 σ δ
  pm_6287
  pm_7256
  · obtain ⟨htlo,hthi⟩ := short_density_middle_time hσ hσ' hH1 hN0 hlo hm
    have hc := hmid N H (N^σ*H^(-2*δ)) t₀ a W hN htlo hthi hV ha hloc hsep hlarge
    rw [hdiv2,hdiv4] at hc
    pm_4529
    have hb4 : (N^(18/7-4*σ)*H^(6/7:ℝ))*H^(8*δ) ≤
        H^(shortDensityExponent σ+8*δ) := by
      calc
        _ ≤ H^(shortDensityExponent σ)*H^(8*δ) :=
          mul_le_mul_of_nonneg_right (short_density_middle_budget hσ hH0 hlo) (by positivity)
        _ = _ := (Real.rpow_add hH0 _ _).symm
    have hsum : N^(2-2*σ)*H^(4*δ)+(N^(18/7-4*σ)*H^(6/7:ℝ))*H^(8*δ) ≤
        2*H^(shortDensityExponent σ+8*δ) := by linarith
    have hbudget : C*N^δ*(N^(2-2*σ)*H^(4*δ)+(N^(18/7-4*σ)*H^(6/7:ℝ))*H^(8*δ)) ≤
        (2*C)*H^(shortDensityExponent σ+10*δ) := by
      pm_4530
    pm_4531
  · have hmean := separated_second_moment hN hH0.le a ha W hloc hsep
    pm_4527
    have hmean1 := short_density_mean_budget hσ hσ' hH1 (le_of_not_ge hm)
    pm_4526

end GuthMaynard.Improvement
