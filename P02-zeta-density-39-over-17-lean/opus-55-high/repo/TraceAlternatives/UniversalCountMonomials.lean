module
public import TraceAlternatives.UniversalCountBudgets
public import DensityEnergyGM.SharpCountMonomials
public import TraceAlternatives.CubeCountMonomials
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

/-- A nonnegative exact zero-loss margin controls the perturbed amplitude;
the explicit cost is at most T^(16delta). -/
theorem universalExpandedTerm_budget {T R σ a x δ ell : ℝ}
    (hT : 1 ≤ T) (hR : 0 < R) (hδ : 0 ≤ δ)
    (j : Fin 3) (i : Fin 5)
    (hell : 3*a*(1-σ)+(2*σ-1)*x ≤ ell)
    (hm : 0 ≤ universalTraceEnergyMargin σ a x j i) :
    (T^x)^3*T^(universalTraceA j)*(T^ell)^(universalTraceB j)*R^(universalTraceG j)*
      (gmEnergyTerm T (T^x) (T^(σ*x-2*δ)) R i)^(universalTraceD j) ≤
      T^(16*δ)*(T^(3*a*(1-σ)))^(2-universalTraceG j-universalTraceD j*gmEnergyR i)*
        (T^(σ*x-2*δ))^4*R^(universalTraceG j+universalTraceD j*gmEnergyR i) := by pm_2727 universalTraceB universalTraceD universalTraceA universalTraceG universalTraceEnergyMargin

end Montgomery.RationalMoment
