module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GalerkinMass
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Reverse-time finite Galerkin coordinates

This module forms the exact finite-coordinate reverse-time Galerkin equation.
It does not assert existence, uniqueness, differentiability, or an energy estimate.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise RealInnerProductSpace

/- Reconstruct a finite Galerkin vector from its real coordinates. -/
noncomputable def galerkinReconstruct
    {d } {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ) :
    (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →ₗ[ℝ] galerkinSpace hΩ N :=
  (galerkinSpaceBasis hΩ N).equivFun.symm.toLinearMap

/- Reconstruction is the finite basis expansion. -/
theorem galerkinReconstruct_apply
    {d } {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    galerkinReconstruct hΩ N x = ∑ i, x i • galerkinSpaceBasis hΩ N i := by
  change (galerkinSpaceBasis hΩ N).equivFun.symm x = _
  simpa only [LinearEquiv.apply_symm_apply] using
    ((galerkinSpaceBasis hΩ N).sum_equivFun
      ((galerkinSpaceBasis hΩ N).equivFun.symm x)).symm

/- Reconstruction inverts the finite coordinate equivalence. -/
@[simp] theorem galerkinReconstruct_equivFun
    {d } {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ) (u : galerkinSpace hΩ N) :
    galerkinReconstruct hΩ N ((galerkinSpaceBasis hΩ N).equivFun u) = u :=  (galerkinSpaceBasis hΩ N).equivFun.symm_apply_apply u

/- `K i j` tests coordinate basis column `j` against row `i`. -/
noncomputable def reverseTimeGalerkinStiffness
    {d Ω}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) :
    Matrix (Fin (Module.finrank ℝ (galerkinSpace hΩ N)))
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N))) ℝ :=
  fun i j =>
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
      (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)
      (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)

/- The finite stiffness matrix is continuous on the closed reverse-time interval. -/
theorem continuous_reverseTimeGalerkinStiffness
    {d Ω}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) :
    Continuous (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N) := by
  apply continuous_matrix
  intro i j
  simpa only [reverseTimeGalerkinStiffness] using
    (((continuous_reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth).clm_apply continuous_const).clm_apply continuous_const)

/- The already-negative reverse-time source in finite Galerkin coordinates. -/
noncomputable def reverseTimeGalerkinSource
    {d Ω}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) :
    Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ :=
  fun i =>
    reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
      (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)

/- The finite negative-source coordinate vector is continuous. -/
noncomputable def reverseTimeGalerkinLinearPart
    {d Ω}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) :
    (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :=
  - LinearMap.toContinuousLinearMap
    (Matrix.mulVecLin ((galerkinMassGram hΩ N)⁻¹ *
      reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ))

/- The mass-inverted negative source contribution to the coordinate equation. -/
noncomputable def reverseTimeGalerkinForcing
    {d Ω}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) :
    Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ :=
  (galerkinMassGram hΩ N)⁻¹ *ᵥ
    reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ

private noncomputable def matrixToContinuousMulVec
    (I : Type) [Fintype I] [DecidableEq I] :
    Matrix I I ℝ →ₗ[ℝ] ((I → ℝ) →L[ℝ] (I → ℝ)) :=
  (LinearMap.toContinuousLinearMap.toLinearMap).comp (Matrix.mulVecBilin ℝ ℝ)

/- The mass-inverted stiffness coefficient is continuous on the closed interval. -/
theorem continuous_reverseTimeGalerkinLinearPart
    {d Ω}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) :
    Continuous (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N) := by
  let I := Fin (Module.finrank ℝ (galerkinSpace hΩ N))
  let M : Matrix I I ℝ := galerkinMassGram hΩ N
  let K := reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth N
  have hK : Continuous K := continuous_reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded
    a b c haSmooth hbSmooth hcSmooth N
  change Continuous fun τ => - LinearMap.toContinuousLinearMap (Matrix.mulVecLin (M⁻¹ * K τ))
  have hmul : Continuous fun τ => M⁻¹ * K τ := continuous_const.matrix_mul hK
  change Continuous fun τ => -(matrixToContinuousMulVec I (M⁻¹ * K τ))
  exact (matrixToContinuousMulVec I).continuous_of_finiteDimensional.neg.comp hmul

/- The mass-inverted source coefficient is continuous on the closed interval. -/
theorem continuous_reverseTimeGalerkinForcing
    {d Ω}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) :
    Continuous (reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N) := by
  have _h_inl_16 : Continuous (reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N) := by
    apply continuous_pi
    intro i
    simpa only [reverseTimeGalerkinSource, Function.comp_def] using
      ((continuous_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).clm_apply
        continuous_const).comp continuous_subtype_val
  simpa only [reverseTimeGalerkinForcing] using! continuous_const.matrix_mulVec
    _h_inl_16

end HypoellipticAleksandrov.Parabolic.Dirichlet
