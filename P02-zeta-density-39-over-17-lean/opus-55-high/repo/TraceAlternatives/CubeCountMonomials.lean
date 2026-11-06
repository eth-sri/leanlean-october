module
public import TraceAlternatives.CubeCountBudgets
public import DensityEnergyGM.SharpCountMonomials
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

/-- A nonnegative exact zero-loss margin controls the perturbed amplitude;
the explicit cost is at most T^(16delta). -/
theorem cubeExpandedTerm_budget {T R σ a x δ ell : ℝ}
    (hT : 1 ≤ T) (hR : 0 < R) (hδ : 0 ≤ δ)
    (j : Fin 2) (i : Fin 5)
    (hell : 3*a*(1-σ)+(2*σ-1)*x ≤ ell)
    (hm : 0 ≤ cubeTraceEnergyMargin σ a x j i) :
    (T^x)^3*T^(cubeTraceA j)*(T^ell)^(cubeTraceB j)*R^(cubeTraceG j)*
      (gmEnergyTerm T (T^x) (T^(σ*x-2*δ)) R i)^(cubeTraceD j) ≤
      T^(16*δ)*(T^(3*a*(1-σ)))^(2-cubeTraceG j-cubeTraceD j*gmEnergyR i)*
        (T^(σ*x-2*δ))^4*R^(cubeTraceG j+cubeTraceD j*gmEnergyR i) := by pm_2727 cubeTraceB cubeTraceD cubeTraceA cubeTraceG cubeTraceEnergyMargin

end Montgomery.RationalMoment
