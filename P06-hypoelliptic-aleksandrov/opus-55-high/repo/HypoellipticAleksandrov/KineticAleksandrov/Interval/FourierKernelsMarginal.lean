module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernels

/-! # Interval Fourier measure support and domination by the parabolic marginal -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- The ambient velocity marginal is exactly the derived scalar parabolic measure. -/
theorem interval_firstMarginal_eq_parabolic {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (B : CoefficientField 1)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    K.firstMarginal (movingQuery σ τ hστ v z hv) =
      P K hJ (scalarQuery σ τ hστ v hv) := by
  obtain ⟨Q, hfirst, _⟩ := hp (fun _ _ _ _ => rfl)
  have hmap := K.map_fiberFirstMarginal_eq_firstMarginal hJ σ τ hστ
    (evolutionStateOfPosition _ stationary σ ⟨v, hv⟩ z)
  rw [← hfirst] at hmap
  exact hmap.symm

end HypoellipticAleksandrov.KineticAleksandrov.Interval
