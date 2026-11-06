module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCompactTime

/-!
# Raw reverse-time Galerkin primal selector

This module fixes the uniform constants supplied by the finite-dimensional
energy theorem and reconstructs its selected coordinate curves directly into
the raw `H10HilbertGraph` carrier.  It deliberately stops before introducing
any quotient, trace, compactness, or weak-solution interface.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

variable {d : ℕ} {Ω : PDE.VelocityRegion d}
variable
  (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (a : CoefficientField d)
  (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d)
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
  (hLower : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- The existence witness used to select the uniform Galerkin curves and constants. -/
def reverseTimeGalerkinPrimalWitness :=
  exists_reverseTimeGalerkin_uniform_energy_solution r₀ r₁ lam h₀₁ hlam
    hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos

/-- The first globally uniform energy constant selected from the finite
Galerkin energy existence theorem. -/
def reverseTimeGalerkinPrimalK : ℝ :=
  (reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose

/-- The second globally uniform energy constant from the same selected
existence witness as `reverseTimeGalerkinPrimalK`. -/
def reverseTimeGalerkinPrimalM : ℝ :=
  ((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose

variable (N : ℕ) (initial : PDE.ScalarLp Ω (2 ))

/-- The selected finite-coordinate reverse-time Galerkin curve. -/
def reverseTimeGalerkinPrimalCoordinate
      :=
  (((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial).choose

/-- The raw Sobolev curve reconstructed directly from the selected coordinates.
This curve is not quotient-valued. -/
def reverseTimeGalerkinPrimalRaw
     :
    ℝ → H10HilbertGraph hΩ :=
  fun τ => (galerkinReconstruct hΩ N
    (reverseTimeGalerkinPrimalCoordinate r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ) :
      H10HilbertGraph hΩ)

/-- The globally selected first energy constant is nonnegative. -/
theorem reverseTimeGalerkinPrimalK_nonneg :
    0 ≤ reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos := (reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.1

variable (N : ℕ) (initial : PDE.ScalarLp Ω (2 ))

/-- The selected raw Galerkin reconstruction is continuous on the closed
reverse-time interval. -/
theorem continuousOn_reverseTimeGalerkinPrimalRaw
     :
    ContinuousOn
      (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
      (Set.Icc 0 (r₁ - r₀)) := by
  let selected :=
    ((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial

  have hspec := selected.choose_spec.choose_spec

  let R : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      H10HilbertGraph hΩ :=
    (galerkinSpace hΩ N).subtypeL.comp
      (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))

  unfold reverseTimeGalerkinPrimalRaw reverseTimeGalerkinPrimalCoordinate
  simpa only [R, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
    Submodule.subtypeL_apply] using (show ContinuousOn (fun τ => R (selected.choose τ)) (Set.Icc 0 (r₁ - r₀)) from R.continuous.continuousOn.comp hspec.2.2.1 fun _ _ => Set.mem_univ _)

/-- At reverse time zero, the selected raw curve is the finite Galerkin
projection of the prescribed initial datum. -/
theorem reverseTimeGalerkinPrimalRaw_zero
     :
    reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial 0 =
      (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ) := by
  let selected :=
    ((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial


  have hx0  := selected.choose_spec.choose_spec.1
  calc
    reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial 0 =
        (galerkinReconstruct hΩ N (selected.choose 0) : H10HilbertGraph hΩ) := rfl
    _ = (galerkinReconstruct hΩ N ((galerkinSpaceBasis hΩ N).equivFun
        (galerkinInitialProjection hΩ N initial)) : H10HilbertGraph hΩ) := by
      solve_by_elim (maxDepth := 4) [galerkinReconstruct, H10HilbertGraph]
    _ = (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ) := congrArg (fun z : galerkinSpace hΩ N => (z : H10HilbertGraph hΩ))
        (galerkinReconstruct_equivFun hΩ N _)

/-- The selected raw curve obeys the sharp pointwise value-energy estimate. -/
theorem reverseTimeGalerkinPrimal_value_energy

    (t : ℝ) (ht : t ∈ Set.Icc 0 (r₁ - r₀)) :
    ‖valueCLM hΩ
      (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial t)‖ ^ 2 ≤
      gronwallBound (‖initial‖ ^ 2)
        (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1)
        (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2) t := by
  let selected :=
    ((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial

  have hspec := selected.choose_spec.choose_spec


  simpa only [reverseTimeGalerkinPrimalRaw, reverseTimeGalerkinPrimalCoordinate,
    reverseTimeGalerkinPrimalK, reverseTimeGalerkinPrimalM, hspec.2.1] using hspec.2.2.2.2.2.1 t ht

/-- The selected raw curve obeys the sharp integrated gradient-energy estimate. -/
theorem reverseTimeGalerkinPrimal_gradient_energy

    (t : ℝ) (ht : t ∈ Set.Icc 0 (r₁ - r₀)) :
    lam * ∫ τ in Set.Ioc 0 t,
      ‖gradientCLM hΩ
        (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)‖ ^ 2 ≤
      ‖initial‖ ^ 2 +
        (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1) * t *
          gronwallBound (‖initial‖ ^ 2)
            (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1)
            (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2)
            (r₁ - r₀) +
        (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2) * t := by
  let selected :=
    ((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial

  have hspec := selected.choose_spec.choose_spec


  simpa only [reverseTimeGalerkinPrimalRaw, reverseTimeGalerkinPrimalCoordinate,
    reverseTimeGalerkinPrimalK, reverseTimeGalerkinPrimalM, hspec.2.1] using hspec.2.2.2.2.2.2 t ht

/-- The selected finite Galerkin curve satisfies the compactly supported
reverse-time scalar identity against every finite-space test vector. -/
theorem reverseTimeGalerkinPrimal_compactTime

    (v : galerkinSpace hΩ N) (eta : ReverseTimeScalarTest (r₁ - r₀)) :
    MeasureTheory.Integrable
      (fun τ =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)) *
          eta.deriv τ)
      (reverseTimeVolume (r₁ - r₀)) ∧
    MeasureTheory.Integrable
      (fun τ =>
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
            (v : H10HilbertGraph hΩ) -
          reverseTimeSpatialForm hΩ r₁ τ a b c
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)
            (v : H10HilbertGraph hΩ)) * eta τ)
      (reverseTimeVolume (r₁ - r₀)) ∧
    (∫ τ,
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ
          (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)) *
        eta.deriv τ ∂reverseTimeVolume (r₁ - r₀)) =
      -(∫ τ,
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
            (v : H10HilbertGraph hΩ) -
          reverseTimeSpatialForm hΩ r₁ τ a b c
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)
            (v : H10HilbertGraph hΩ)) * eta τ
        ∂reverseTimeVolume (r₁ - r₀)) := by
  let sharedTerm_394fab5027 := ((Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ))
  let selected :=
    ((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial

  have hspec := selected.choose_spec.choose_spec
  let x := reverseTimeGalerkinPrimalCoordinate r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  let T : ℝ := r₁ - r₀
  have hT  := sub_nonneg.mpr h₀₁.le
  let A : ℝ → sharedTerm_394fab5027 →L[ℝ]
      sharedTerm_394fab5027 := fun τ =>
    reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N (Set.projIcc 0 T hT τ)
  let f : ℝ → sharedTerm_394fab5027 := fun τ =>
    reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N
      (Set.projIcc 0 T hT τ)
  let xdot : ℝ → sharedTerm_394fab5027 := fun τ =>
    A τ (x τ) + f τ



  simpa only [reverseTimeGalerkinPrimalRaw, x] using
    (reverseTimeGalerkin_compactTime_identity_of_basisRows r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth N x xdot (by
          simpa only [x, T, reverseTimeGalerkinPrimalCoordinate] using
            hspec.2.2.1) (by
          intro τ hτ


          simpa only [x, xdot, A, f, T, (Set.projIcc_of_mem hT hτ),
            reverseTimeGalerkinPrimalCoordinate] using (hspec.2.2.2.2.1 (⟨τ, hτ⟩)).1) (by
          intro τ i



          simpa only [x, xdot, A, f, T, (Set.projIcc_of_mem hT τ.2),
            reverseTimeGalerkinPrimalCoordinate, hspec.2.1] using
            (hspec.2.2.2.2.1 (⟨τ.1, τ.2⟩)).2 i) v eta)

end HypoellipticAleksandrov.Parabolic.Dirichlet
