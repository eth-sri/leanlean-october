module
public import DensityEnergyGM.SharpCountScale
public import DensityEnergyGM.SharpCountTargetWindows
public import TraceAlternatives.CubePolynomialCount

public section

set_option maxHeartbeats 2400000
open Finset GuthMaynard.Improvement GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

theorem gmTraceExpression_eq_sum (T N L R E : ℝ) :
    N^3*T/L*E^(1/2:ℝ)+N^3*T^(4/5:ℝ)*L^(-4/5:ℝ)*R*E^(1/4:ℝ)+
      N^3*T^(9/20:ℝ)*L^(-1/5:ℝ)*R*E^(1/4:ℝ) =
    ∑ j : Fin 3, N^3*T^(gmTraceA j)*L^(gmTraceB j)*R^(gmTraceG j)*E^(gmTraceD j) := by
  norm_num [Fin.sum_univ_succ,gmTraceA,gmTraceB,gmTraceG,gmTraceD]
  rw [Real.rpow_neg_one]
  ring

/-- Actual general-polynomial count from the proved sharp trace and full
five-term energy. The only extra premises are explicit real exponent budgets.
The detector length and amplitude losses are tracked as72delta. -/
theorem sharp_polynomial_count_loss {σ a δ : ℝ}
    (hσ : 4/5 ≤ σ) (hσ1 : σ < 1) (ha : 1/2 ≤ a) (ha1 : a < 2/3)
    (hδ : 0 < δ) (hδa : δ ≤ (1-3*a/2)/2)
    (hm : ∀ x : ℝ, a ≤ x → ∀ j : Fin 3, ∀ i : Fin 5,
      0 ≤ gmTraceEnergyMargin σ a x j i) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 2 ≤ T →
      T^a ≤ N → N ≤ T^(3*a/2+δ) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*a*(1-σ)+72*δ) := by pf_7 finite_quadratic_large_value_sharp_native 15 gmTraceEnergy_common_bound 3 gmTraceA gmTraceB gmTraceG gmTraceD gmTraceExpression_eq_sum

end Montgomery.RationalMoment
