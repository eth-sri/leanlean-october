module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GalerkinDense
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
section

open scoped ENNReal RealInnerProductSpace

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The `L²` image of the finite actual-test Galerkin space. -/
noncomputable def galerkinValueSpace
    (hΩ : IsOpen Ω) (N : ℕ) :
    Submodule ℝ (PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
  (galerkinSpace hΩ N).map (valueCLM hΩ).toLinearMap

/-- The finite Galerkin value space is finite dimensional. -/
noncomputable instance galerkinValueSpace_finiteDimensional
    (hΩ : IsOpen Ω) (N : ℕ) :
    FiniteDimensional ℝ (galerkinValueSpace hΩ N) := by
  unfold galerkinValueSpace
  infer_instance

/-- The finite Galerkin value space is complete. -/
noncomputable instance galerkinValueSpace_completeSpace
    (hΩ : IsOpen Ω) (N : ℕ) :
    CompleteSpace (galerkinValueSpace hΩ N) :=
  FiniteDimensional.complete ℝ (galerkinValueSpace hΩ N)

/-- The `L²` mass Gram matrix of the finite actual-test Galerkin basis. -/
noncomputable def galerkinMassGram
    (hΩ : IsOpen Ω) (N : ℕ) :
    Matrix
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N)))
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N))) ℝ :=
  Matrix.gram ℝ (fun i =>
    valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ))

/-- The finite `L²` mass Gram matrix is positive definite. -/
theorem galerkinMassGram_posDef
    (hΩ : IsOpen Ω) (N : ℕ) :
    (galerkinMassGram hΩ N).PosDef := by
  let E := galerkinSpace hΩ N
  let L :=
    (valueCLM hΩ).toLinearMap.comp E.subtype
  have hL : Function.Injective L := by
    intro u v huv
    apply Subtype.ext
    exact valueCLM_injective hΩ huv
  have hli :=
    (galerkinSpaceBasis hΩ N).linearIndependent.map' L
      (LinearMap.ker_eq_bot_of_injective hL)
  simpa only [galerkinMassGram, L, E, Function.comp_def, LinearMap.comp_apply, LinearMap.coe_comp,
    ContinuousLinearMap.coe_coe, Submodule.coe_subtype] using
    Matrix.posDef_gram_of_linearIndependent hli

/-- The finite `L²` mass Gram matrix is invertible, including at `N = 0`. -/
theorem isUnit_galerkinMassGram
    (hΩ : IsOpen Ω) (N : ℕ) :
    IsUnit (galerkinMassGram hΩ N) :=
  (galerkinMassGram_posDef hΩ N).isUnit

/-- A chosen preimage of the finite Galerkin value-space projection. -/
noncomputable def galerkinInitialProjectionPreimage
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    H10HilbertGraph hΩ :=
  Classical.choose <| Submodule.mem_map.mp
    (Submodule.starProjection_apply_mem (galerkinValueSpace hΩ N) initial)

/-- The chosen projection preimage lies in the finite Galerkin space. -/
theorem galerkinInitialProjectionPreimage_mem
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    galerkinInitialProjectionPreimage hΩ N initial ∈ galerkinSpace hΩ N := by
  exact (Classical.choose_spec <| Submodule.mem_map.mp
    (Submodule.starProjection_apply_mem (galerkinValueSpace hΩ N) initial)).1

private theorem value_galerkinInitialProjectionPreimage
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    valueCLM hΩ (galerkinInitialProjectionPreimage hΩ N initial) =
      (galerkinValueSpace hΩ N).starProjection initial := by
  exact (Classical.choose_spec <| Submodule.mem_map.mp
    (Submodule.starProjection_apply_mem (galerkinValueSpace hΩ N) initial)).2

/-- The lift to the finite Galerkin space of the `L²` orthogonal projection
of an initial datum. -/
noncomputable def galerkinInitialProjection
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    galerkinSpace hΩ N :=
  ⟨galerkinInitialProjectionPreimage hΩ N initial,
    galerkinInitialProjectionPreimage_mem hΩ N initial⟩

/-- Applying the spatial value map to the lifted initial datum recovers its
`L²` orthogonal projection onto the finite Galerkin value space. -/
theorem value_galerkinInitialProjection
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    valueCLM hΩ (galerkinInitialProjection hΩ N initial :
      H10HilbertGraph hΩ) =
    (galerkinValueSpace hΩ N).starProjection initial :=
  value_galerkinInitialProjectionPreimage hΩ N initial

/-- The finite Galerkin `L²` initial projection is contractive. -/
theorem norm_value_galerkinInitialProjection_le
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖valueCLM hΩ (galerkinInitialProjection hΩ N initial :
      H10HilbertGraph hΩ)‖ ≤ ‖initial‖ := by
  rw [value_galerkinInitialProjection]
  exact (galerkinValueSpace hΩ N).norm_starProjection_apply_le initial

end

open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise RealInnerProductSpace

/-- Reconstruct a finite Galerkin vector from its real coordinates. -/
noncomputable def galerkinReconstruct
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ) :
    (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →ₗ[ℝ] galerkinSpace hΩ N :=
  (galerkinSpaceBasis hΩ N).equivFun.symm.toLinearMap

/-- Reconstruction is the finite basis expansion. -/
theorem galerkinReconstruct_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    galerkinReconstruct hΩ N x = ∑ i, x i • galerkinSpaceBasis hΩ N i := by
  change (galerkinSpaceBasis hΩ N).equivFun.symm x = _
  simpa using
    ((galerkinSpaceBasis hΩ N).sum_equivFun
      ((galerkinSpaceBasis hΩ N).equivFun.symm x)).symm

/-- Reconstruction inverts the finite coordinate equivalence. -/
@[simp] theorem galerkinReconstruct_equivFun
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ) (u : galerkinSpace hΩ N) :
    galerkinReconstruct hΩ N ((galerkinSpaceBasis hΩ N).equivFun u) = u := by
  exact (galerkinSpaceBasis hΩ N).equivFun.symm_apply_apply u

/-- `K i j` tests coordinate basis column `j` against row `i`. -/
noncomputable def reverseTimeGalerkinStiffness
    {d : ℕ} {Ω : Set (PDE.Vec d)}
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

/-- The finite stiffness matrix is continuous on the closed reverse-time interval. -/
theorem continuous_reverseTimeGalerkinStiffness
    {d : ℕ} {Ω : Set (PDE.Vec d)}
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

/-- The already-negative reverse-time source in finite Galerkin coordinates. -/
noncomputable def reverseTimeGalerkinSource
    {d : ℕ} {Ω : Set (PDE.Vec d)}
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

/-- The finite negative-source coordinate vector is continuous. -/
theorem continuous_reverseTimeGalerkinSource
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) :
    Continuous (reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N) := by
  apply continuous_pi
  intro i
  simpa only [reverseTimeGalerkinSource, Function.comp_def] using
    ((continuous_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).clm_apply
      continuous_const).comp continuous_subtype_val

/-- On the true reverse-time interval, a source coordinate is the literal source functional. -/
theorem reverseTimeGalerkinSource_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N))) :
    reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i =
      reverseTimeSourceFunctional hΩ
        (reverseTimeSourceSlice r₁ τ.1 F
          (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
            τ.1 τ.2))
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
  simpa only [reverseTimeGalerkinSource] using congrArg
    (fun f => f (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ))
    (reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc r₀ r₁ h₀₁ hΩ hΩbounded F
      hFSmooth τ.1 τ.2)

/-- The mass-inverted stiffness contribution to the coordinate equation. -/
noncomputable def reverseTimeGalerkinLinearPart
    {d : ℕ} {Ω : Set (PDE.Vec d)}
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

/-- The mass-inverted negative source contribution to the coordinate equation. -/
noncomputable def reverseTimeGalerkinForcing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) :
    Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ :=
  (galerkinMassGram hΩ N)⁻¹ *ᵥ
    reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ


/-- The mass-inverted stiffness coefficient is continuous on the closed interval. -/
theorem continuous_reverseTimeGalerkinLinearPart
    {d : ℕ} {Ω : Set (PDE.Vec d)}
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
      haSmooth hbSmooth hcSmooth N)  := by
  let matrixToContinuousMulVec (I : Type) [Fintype I] [DecidableEq I] : Matrix I I ℝ →ₗ[ℝ] ((I → ℝ) →L[ℝ] (I → ℝ)) :=
    (LinearMap.toContinuousLinearMap.toLinearMap).comp (Matrix.mulVecBilin ℝ ℝ)
  have hmul : Continuous fun τ => (galerkinMassGram hΩ N)⁻¹ * (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N) τ := continuous_const.matrix_mul (continuous_reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N)
  exact (matrixToContinuousMulVec (Fin (Module.finrank ℝ (galerkinSpace hΩ N)))).continuous_of_finiteDimensional.neg.comp hmul

/-- The mass-inverted source coefficient is continuous on the closed interval. -/
theorem continuous_reverseTimeGalerkinForcing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) :
    Continuous (reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N) := by
  simpa using! continuous_const.matrix_mulVec
    (continuous_reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N)

end HypoellipticAleksandrov.Parabolic.Dirichlet

