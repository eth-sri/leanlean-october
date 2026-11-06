module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GalerkinDense
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Finite Galerkin mass spaces and initial data

This module provides the finite-dimensional `L²` mass space associated with
the actual-test Galerkin spaces, its Gram matrix, and the lifted orthogonal
projection of an initial `L²` datum.  It makes no time-dependent, derivative,
or PDE assertion.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped ENNReal RealInnerProductSpace

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/- The `L²` image of the finite actual-test Galerkin space. -/
noncomputable def galerkinValueSpace
    (hΩ : IsOpen Ω) (N : ℕ) :
    Submodule ℝ (PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
  (galerkinSpace hΩ N).map (valueCLM hΩ).toLinearMap

/- The finite Galerkin value space is finite dimensional. -/
noncomputable instance galerkinValueSpace_finiteDimensional
    (hΩ : IsOpen Ω) (N : ℕ) :
    FiniteDimensional ℝ (galerkinValueSpace hΩ N) := by
  unfold galerkinValueSpace
  infer_instance

/- The finite Galerkin value space is complete. -/
noncomputable instance galerkinValueSpace_completeSpace
    (hΩ : IsOpen Ω) (N : ℕ) :
    CompleteSpace (galerkinValueSpace hΩ N) :=
  FiniteDimensional.complete ℝ (galerkinValueSpace hΩ N)

/- The `L²` mass Gram matrix of the finite actual-test Galerkin basis. -/
noncomputable def galerkinMassGram
    (hΩ : IsOpen Ω) (N : ℕ) :
    Matrix
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N)))
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N))) ℝ :=
  Matrix.gram ℝ (fun i =>
    valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ))

/- The finite `L²` mass Gram matrix is positive definite. -/
noncomputable def galerkinInitialProjectionPreimage
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    H10HilbertGraph hΩ :=
  Classical.choose <| Submodule.mem_map.mp
    (Submodule.starProjection_apply_mem (galerkinValueSpace hΩ N) initial)

/- The chosen projection preimage lies in the finite Galerkin space. -/
theorem galerkinInitialProjectionPreimage_mem
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    galerkinInitialProjectionPreimage hΩ N initial ∈ galerkinSpace hΩ N := by
  exact (Classical.choose_spec <| Submodule.mem_map.mp
    (Submodule.starProjection_apply_mem (galerkinValueSpace hΩ N) initial)).1

noncomputable def galerkinInitialProjection
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    galerkinSpace hΩ N :=
  ⟨galerkinInitialProjectionPreimage hΩ N initial,
    galerkinInitialProjectionPreimage_mem hΩ N initial⟩

/- Applying the spatial value map to the lifted initial datum recovers its
`L²` orthogonal projection onto the finite Galerkin value space. -/
theorem value_galerkinInitialProjection
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    valueCLM hΩ (galerkinInitialProjection hΩ N initial :
      H10HilbertGraph hΩ) =
    (galerkinValueSpace hΩ N).starProjection initial := by
  exact (Classical.choose_spec <| Submodule.mem_map.mp
    (Submodule.starProjection_apply_mem (galerkinValueSpace hΩ N) initial)).2

/- The finite Galerkin `L²` initial projection is contractive. -/
end HypoellipticAleksandrov.Parabolic.Dirichlet
