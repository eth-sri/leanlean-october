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

/-- Reconstruct a finite Galerkin vector from its real coordinates. -/
noncomputable def galerkinReconstruct
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ) :
    GalerkinCoordinates hΩ N →ₗ[ℝ] galerkinSpace hΩ N :=
  (galerkinSpaceBasis hΩ N).equivFun.symm.toLinearMap

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ)

/-- Reconstruction is the finite basis expansion. -/
theorem galerkinReconstruct_apply
    (x : GalerkinCoordinates hΩ N) :
    galerkinReconstruct hΩ N x = ∑ i, x i • galerkinSpaceBasis hΩ N i := by
  change (galerkinSpaceBasis hΩ N).equivFun.symm x = _
  simpa only [LinearEquiv.apply_symm_apply] using
    ((galerkinSpaceBasis hΩ N).sum_equivFun
      ((galerkinSpaceBasis hΩ N).equivFun.symm x)).symm

/-- Reconstruction inverts the finite coordinate equivalence. -/
@[simp] theorem galerkinReconstruct_equivFun (u : galerkinSpace hΩ N) :
    galerkinReconstruct hΩ N ((galerkinSpaceBasis hΩ N).equivFun u) = u := (galerkinSpaceBasis hΩ N).equivFun.symm_apply_apply u

/-- Reconstruct in the ambient Sobolev space, as a continuous linear map. -/
noncomputable def galerkinReconstructCLM : GalerkinCoordinates hΩ N →L[ℝ] H10HilbertGraph hΩ :=
  (galerkinSpace hΩ N).subtypeL.comp (galerkinReconstruct hΩ N).toContinuousLinearMap

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

@[simp] theorem galerkinReconstructCLM_apply
    (hΩ : IsOpen Ω) (N : ℕ) (x : GalerkinCoordinates hΩ N) :
    galerkinReconstructCLM hΩ N x = (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) := rfl

/-- A continuous coordinate curve has a continuous ambient reconstruction. -/
theorem continuousOn_galerkinReconstruct
    {hΩ : IsOpen Ω} {N : ℕ} {x : ℝ → GalerkinCoordinates hΩ N} {s : Set ℝ}
    (hx : ContinuousOn x s) :
    ContinuousOn (fun t => (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)) s :=
  (galerkinReconstructCLM hΩ N).continuous.comp_continuousOn hx

/-- `K i j` tests coordinate basis column `j` against row `i`. -/
noncomputable def reverseTimeGalerkinStiffness
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) :
    Matrix (GalerkinIndex hΩ N)
      (GalerkinIndex hΩ N) ℝ :=
  fun i j =>
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
      (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)
      (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
  (hΩbounded : Bornology.IsBounded Ω)
include h₀₁ hΩbounded

/-- The finite stiffness matrix is continuous on the closed reverse-time interval. -/
theorem continuous_reverseTimeGalerkinStiffness
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (N : ℕ) :
    Continuous (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N) := by
  apply continuous_matrix
  intro i j
  simpa only [reverseTimeGalerkinStiffness] using
    (((continuous_reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth).clm_apply continuous_const).clm_apply continuous_const)

/-- The already-negative reverse-time source in finite Galerkin coordinates. -/
noncomputable def reverseTimeGalerkinSource
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) :
    GalerkinCoordinates hΩ N :=
  fun i =>
    reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
      (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
  (hΩbounded : Bornology.IsBounded Ω)
include h₀₁ hΩbounded

section
variable (F : ℝ → PDE.Vec d → ℝ) (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F) (N : ℕ)

/-- The finite negative-source coordinate vector is continuous. -/
theorem continuous_reverseTimeGalerkinSource :
    Continuous (reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N) := by
  apply continuous_pi
  intro i
  simpa only [reverseTimeGalerkinSource, Function.comp_def] using
    ((continuous_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).clm_apply
      continuous_const).comp continuous_subtype_val

end

/-- The mass-inverted stiffness contribution to the coordinate equation. -/
noncomputable def reverseTimeGalerkinLinearPart
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) :
    GalerkinCoordinates hΩ N →L[ℝ]
      (GalerkinCoordinates hΩ N) :=
  - LinearMap.toContinuousLinearMap
    (Matrix.mulVecLin ((galerkinMassGram hΩ N)⁻¹ *
      reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ))

/-- The mass-inverted negative source contribution to the coordinate equation. -/
noncomputable def reverseTimeGalerkinForcing
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) :
    GalerkinCoordinates hΩ N :=
  (galerkinMassGram hΩ N)⁻¹ *ᵥ
    reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ

end

private noncomputable def matrixToContinuousMulVec
    (I : Type) [Fintype I] [DecidableEq I] :
    Matrix I I ℝ →ₗ[ℝ] ((I → ℝ) →L[ℝ] (I → ℝ)) :=
  (LinearMap.toContinuousLinearMap.toLinearMap).comp (Matrix.mulVecBilin ℝ ℝ)

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
  (hΩbounded : Bornology.IsBounded Ω)

/-- The mass-inverted stiffness coefficient is continuous on the closed interval. -/
theorem continuous_reverseTimeGalerkinLinearPart
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (N : ℕ) :
    Continuous (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N) := by
  let I := GalerkinIndex hΩ N
  let M : Matrix I I ℝ := galerkinMassGram hΩ N
  let K := reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth N
  have hK : Continuous K := continuous_reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded
    a b c haSmooth hbSmooth hcSmooth N
  change Continuous fun τ => - LinearMap.toContinuousLinearMap (Matrix.mulVecLin (M⁻¹ * K τ))
  have hmul : Continuous fun τ => M⁻¹ * K τ := continuous_const.matrix_mul hK
  change Continuous fun τ => -(matrixToContinuousMulVec I (M⁻¹ * K τ))
  exact (matrixToContinuousMulVec I).continuous_of_finiteDimensional.neg.comp hmul

/-- The mass-inverted source coefficient is continuous on the closed interval. -/
theorem continuous_reverseTimeGalerkinForcing
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (N : ℕ) :
    Continuous (reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N) := by
  simpa only [reverseTimeGalerkinForcing] using! continuous_const.matrix_mulVec
    (continuous_reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N)

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
