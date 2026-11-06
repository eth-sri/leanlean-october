module
public import AdjacentAbsorption
public import AdjacentMonomialBudgets
public import AdjacentUpperValues
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1600000
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

section
variable {σ a p α δ : ℝ} (hw : AdjacentWindow σ a p α) (hδ : 0 < δ)
include σ a p α δ hw hδ
theorem adjacent_lower_large_values :
    ∃ C : ℝ, 0 < C ∧ ∀ (T N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → T^a ≤ N → N ≤ T^α →
      (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(p+18*δ) := by
  pm_5342 finite_cubic_large_value_bound discrete_additive_energy_adjacent
  refine ⟨1+A*(4+4*B),by positivity,?_⟩
  pm_2765
  pm_5422 adjacent_amplifier_budgets
  pm_2764
  · calc
      _ ≤ T^p := hr
      _ ≤ (1+A*(4+4*B))*(T^(18*δ)*T^p) := by
        have hh : 1 ≤ 1+A*(4+4*B) := by nlinarith [mul_nonneg hA.le (show 0 ≤ 4+4*B by linarith)]
        nlinarith only [mul_le_mul_of_nonneg_right hpow hp.le,mul_nonneg (by positivity : 0 ≤ A*(4+4*B)) (by positivity : 0 ≤ T^(18*δ)*T^p)]
      _ = _ := by rw [← Real.rpow_add htp]; congr 2; ring
  · have hrs : T^p ≤ (W.card:ℝ) := (lt_of_not_ge hr).le
    have hrange : T^(((4:ℝ)+1)/(2*4+1)) ≤ (W.card:ℝ) := by
      norm_num
      exact hs.trans hrs
    have hnlow : T^((2:ℝ)/3) ≤ N :=
      (Real.rpow_le_rpow_of_exponent_le ht (by linarith [hw.a_low])).trans hlo
    have henergy := he T t₀ N (by linarith) hnlow hnt b W (N^σ*T^(-2*δ))
      (hs.trans hrs) hb hv hlarge hloc hsep
    have hlen : (T/L)^4 ≤ (W.card:ℝ) := hen.trans hrs
    pm_2767
    obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := adjacent_monomial_budgets hw hδ.le ht hn hlo hhi
    have hh := adjacent_scalar_absorption hn hlp htp hv hp hrs
      (Real.one_le_rpow ht (show 0 ≤ 16*δ by positivity))
      (Real.one_le_rpow ht hδ.le) hA.le hB.le
      (Nat.cast_nonneg (discreteAdditiveEnergy W)) henergy hcubic h1 h2 h3 h4 h5 h6 h7
    pm_2766
    calc
      _ ≤ A*(4+4*B)*(T^δ)^2*T^(16*δ)*T^p := hh
      _ = A*(4+4*B)*T^(p+18*δ) := by rw [← heq]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)



theorem adjacent_full_window_large_values (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → 2 ≤ N → T^a ≤ N → N ≤ T^(3*a/2+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(p+18*δ) := by pm_2769 adjacent_lower_large_values adjacent_upper_large_values
end

end Montgomery.RationalMoment
