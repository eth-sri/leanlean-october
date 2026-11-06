module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GlobalLinearODE
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCoordinates

/-!
# Reverse-time finite Galerkin ODE solutions

This module lifts the finite-coordinate ODE to the Galerkin space and
records its exact basis-row weak equation.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped ENNReal Matrix Matrix.Norms.Elementwise

/-- A reverse-time finite Galerkin coordinate solution and its reconstruction exist. -/
theorem exists_reverseTimeGalerkin_solution
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 )) :
    ∃ x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ,
      ∃ u : ℝ → galerkinSpace hΩ N,
        x 0 = (galerkinSpaceBasis hΩ N).equivFun
          (galerkinInitialProjection hΩ N initial) ∧
        u = (fun τ => galerkinReconstruct hΩ N (x τ)) ∧
        ContinuousOn x (Set.Icc 0 (r₁ - r₀)) ∧
        ContinuousOn u (Set.Icc 0 (r₁ - r₀)) ∧
        (∀ τ : Set.Icc 0 (r₁ - r₀),
          HasDerivWithinAt x
            (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth N τ (x τ) +
            reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)
            (Set.Icc 0 (r₁ - r₀)) τ ∧
          ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
            inner ℝ
                (valueCLM hΩ (galerkinReconstruct hΩ N
                  (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
                    haSmooth hbSmooth hcSmooth N τ (x τ) +
                  reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) :
                    H10HilbertGraph hΩ))
                (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
              reverseTimeSpatialForm hΩ r₁ τ.1 a b c
                (u τ : H10HilbertGraph hΩ)
                (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
              reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) := by
  let sharedTerm_bc602d0921 := ((Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ))
  let T := r₁ - r₀
  have hT : 0 ≤ T := sub_nonneg.mpr h₀₁.le

  let A : ℝ → sharedTerm_bc602d0921 →L[ℝ]
      sharedTerm_bc602d0921 :=
    fun τ => reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N (Set.projIcc 0 T hT τ)
  let f : ℝ → sharedTerm_bc602d0921 :=
    fun τ => reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N
      (Set.projIcc 0 T hT τ)


  have hode := exists_linear_ode_on_Icc hT A f (((continuous_reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth N).comp continuous_projIcc).continuousOn) (((continuous_reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N).comp
        continuous_projIcc).continuousOn) ((galerkinSpaceBasis hΩ N).equivFun (galerkinInitialProjection hΩ N initial))
  let x := hode.choose

  have hxcont : ContinuousOn x (Set.Icc 0 T) := hode.choose_spec.2.1

  let u  := fun τ => galerkinReconstruct hΩ N (x τ)

  refine ⟨x, u, ?_, rfl, hxcont, ((LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N)).continuous.continuousOn
        |>.comp hxcont (fun _ _ => Set.mem_univ _)), ?_⟩
  · exact hode.choose_spec.1
  intro τ

  constructor
  · simpa only [A, f, (Set.projIcc_of_mem hT τ.2)] using hode.choose_spec.2.2 τ τ.2
  · simpa only [u] using
      (reverseTimeGalerkin_coordinateEquation_iff r₀ r₁ h₀₁ hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth N τ (x τ)
        (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ (x τ) +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)).mpr rfl

end HypoellipticAleksandrov.Parabolic.Dirichlet
