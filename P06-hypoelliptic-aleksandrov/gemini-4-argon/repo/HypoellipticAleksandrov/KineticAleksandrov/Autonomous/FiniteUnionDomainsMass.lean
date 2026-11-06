module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite

/-! # Uniform finite mass of actual Green mixtures on finite interval unions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/- A finite union's mass constant depends only on its interval lengths and ellipticity. -/
def finiteUnionGreenMassBound (lam : ℝ) (H : FiniteIntervalUnion) : ℝ≥0∞ :=
  ∑ i : Fin H.count, ENNReal.ofReal (((H.component i).hi - (H.component i).lo) ^ 2 /
    (2 * lam))

/- The geometric finite-union mass constant is finite. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
