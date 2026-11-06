module
public import TraceAlternatives.CubeCountMonomials
public import DensityEnergyGM.SharpCountTraceExpansion

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- All ten actual trace/energy terms are retained and normalized to
one common positive count gap, including the full amplitude perturbation. -/
theorem cubeTraceEnergy_common_bound {T R E C σ a x δ ell η : ℝ}
    (hT : 1 ≤ T) (hC : 0 ≤ C) (hE : 0 ≤ E) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hSR : T^(3*a*(1-σ)) ≤ R)
    (hell : 3*a*(1-σ)+(2*σ-1)*x ≤ ell)
    (hm : ∀ j : Fin 2, ∀ i : Fin 5, 0 ≤ cubeTraceEnergyMargin σ a x j i)
    (hEnergy : E ≤ C*T^η*fiveTermEnergyExpression T (T^x) (T^(σ*x-2*δ)) R) :
    (∑ j : Fin 2, (T^x)^3*T^(cubeTraceA j)*(T^ell)^(cubeTraceB j)*
      R^(cubeTraceG j)*E^(cubeTraceD j)) ≤
      10*(1+C)*T^η*(T^(16*δ)*(T^(3*a*(1-σ)))^(1/4:ℝ)*
        R^(7/4:ℝ)*(T^(σ*x-2*δ))^4) := by pf_23 2 cubeTraceA cubeTraceB cubeTraceG cubeTraceD cubeExpandedTerm_budget cubeTraceEnergy_sublinearity

end Montgomery.RationalMoment
