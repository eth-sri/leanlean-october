module
public import DensityWindowBudgets
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Real
namespace Montgomery.RationalMoment

/-- All five monomial inequalities hold for every real detecting length
in the lower window. The normalized detector height loses exactly T^(-2δ),
and Q=T^(16δ) pays that loss explicitly. -/
theorem two_term_monomial_budgets {σ a p α δ T N : ℝ}
    (hw : TwoTermWindow σ a p α) (hδ : 0 ≤ δ) (hT : 1 ≤ T) (hN : 0 < N)
    (hlo : T^a ≤ N) (hhi : N ≤ T^α) :
    let L := twoTermAmplifier T N σ p
    let S := T^p
    let Q := T^(16*δ)
    let V := N^σ*T^(-2*δ)
    (N*L)^3 ≤ Q*S^3*V^6 ∧
    (N^4*T^2/L)^2 ≤ Q^2*S^3*V^12 ∧
    N^12*T^2 ≤ Q^2*S^4*V^16 ∧
    N^9*T^2 ≤ Q^2*S^2*V^14 ∧
    N^4*L ≤ Q*S*V^6 := by
  pm_134
  pm_5435
  pm_80
  grind

end Montgomery.RationalMoment
