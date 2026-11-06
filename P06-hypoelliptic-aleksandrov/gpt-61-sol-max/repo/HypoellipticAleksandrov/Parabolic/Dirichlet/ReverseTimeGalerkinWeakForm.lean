module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCoordinatesBase
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinEnergy

open private HypoellipticAleksandrov.Parabolic.Dirichlet.map_galerkinReconstruct_sum from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinEnergy


/-!
# Reverse-time finite Galerkin weak form

This module extends an exact finite Galerkin basis-row equation to every test
vector in that same finite Galerkin space.  It makes no limiting or time-
integrated assertion.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise

variable {d : ℕ} {Ω : PDE.VelocityRegion d}




/-- Exact finite Galerkin basis rows hold against every finite Galerkin test. -/
theorem reverseTimeGalerkin_basisRows_forall

    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (hrows : ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i)
    (v : galerkinSpace hΩ N) :
    inner ℝ
        (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
        (valueCLM hΩ (v : H10HilbertGraph hΩ)) +
      reverseTimeSpatialForm hΩ r₁ τ.1 a b c
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (v : H10HilbertGraph hΩ) =
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ.1
        (v : H10HilbertGraph hΩ) := by
  let q  :=
    (galerkinSpaceBasis hΩ N).equivFun v
  let u : H10HilbertGraph hΩ := galerkinReconstruct hΩ N x
  let udot : PDE.ScalarLp Ω (2 ) :=
    valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ)
  let e : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → H10HilbertGraph hΩ :=
    fun i => galerkinSpaceBasis hΩ N i
  let B : H10HilbertGraph hΩ →L[ℝ] ℝ :=
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth τ u
  let A : H10HilbertGraph hΩ →L[ℝ] ℝ :=
    (innerSL ℝ udot).comp (valueCLM hΩ)
  let T  := A + B
  let S  :=
    reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ.1
  have hu : (galerkinReconstruct hΩ N q : H10HilbertGraph hΩ) = v := by
    exact congrArg (fun w : galerkinSpace hΩ N => (w : H10HilbertGraph hΩ))
      (galerkinReconstruct_equivFun hΩ N v)




  have hresult : T (galerkinReconstruct hΩ N q : H10HilbertGraph hΩ) =
      S (galerkinReconstruct hΩ N q : H10HilbertGraph hΩ) :=
    (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.map_galerkinReconstruct_sum hΩ N T q).trans ((show ∑ i, q i • T (e i) = ∑ i, q i • S (e i) by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun z => q i • z) ((show ∀ i, T (e i) = S (e i) by
            intro i
            simpa only [T, A, B, S, e, udot, u, ContinuousLinearMap.add_apply,
              ContinuousLinearMap.comp_apply, innerSL_apply_apply,
              reverseTimeSpatialFormOperator_apply, reverseTimeGalerkinSource] using hrows i) i)).trans (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.map_galerkinReconstruct_sum hΩ N S q).symm)
  rw [hu] at hresult
  simpa only [T, A, B, S, udot, u, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, reverseTimeSpatialFormOperator_apply]
    using hresult

end HypoellipticAleksandrov.Parabolic.Dirichlet
