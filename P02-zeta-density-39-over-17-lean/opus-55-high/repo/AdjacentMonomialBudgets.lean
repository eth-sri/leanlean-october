module
public import AdjacentWindow
import WeylPort.Analytic.RealLaplace

public section

open Real
namespace Montgomery.RationalMoment

/-- All five monomial inequalities hold for every real detecting length
in the lower window. The normalized detector height loses exactly T^(-2δ),
and Q=T^(16δ) pays that loss explicitly. -/
theorem adjacent_monomial_budgets {σ a p α δ T N : ℝ}
    (hw : AdjacentWindow σ a p α) (hδ : 0 ≤ δ) (hT : 1 ≤ T) (hN : 0 < N)
    (hlo : T^a ≤ N) (hhi : N ≤ T^α) :
    let L := twoTermAmplifier T N σ p
    let S := T^p
    let Q := T^(16*δ)
    let V := N^σ*T^(-2*δ)
    (N*L)^3 ≤ Q*S^3*V^6 ∧
    (N^4*T^2/L)^2 ≤ Q^2*S^3*V^12 ∧
    N^12*T^2 ≤ Q^2*S^4*V^16 ∧
    N^9*T^2 ≤ Q^2*S^2*V^14 ∧
    N^4*L ≤ Q*S*V^6 ∧
    N^8*T^3 ≤ Q^2*S^((5:ℝ)/2)*V^14 ∧
    N^9*T^((9:ℝ)/4) ≤ Q^2*S^((29:ℝ)/12)*V^14 := by
  pm_134
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  pm_80
  · nlinarith only [hd]
  · have hh := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 14*σ-8 by linarith [hw.sigma_low])
    have hb := mul_nonneg (show 0 ≤ (5/2)*p+a*(14*σ-8)-3 by linarith [hw.energy_adjacent_third]) ht
    nlinarith only [hh,hb,hd]
  · have hh := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 14*σ-9 by linarith [hw.sigma_low])
    have hb := mul_nonneg (show 0 ≤ (29/12)*p+a*(14*σ-9)-9/4 by linarith [hw.energy_adjacent_fourth]) ht
    nlinarith only [hh,hb,hd]

end Montgomery.RationalMoment
