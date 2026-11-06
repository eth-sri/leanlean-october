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

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

/-- The `L²` image of the finite actual-test Galerkin space. -/
def galerkinValueSpace
    (hΩ : IsOpen Ω) (N : ℕ) :
    Submodule ℝ (PDE.ScalarLp Ω (2 )) :=
  (galerkinSpace hΩ N).map (valueCLM hΩ).toLinearMap

/-- The finite Galerkin value space is finite dimensional. -/
instance galerkinValueSpace_finiteDimensional
    (hΩ : IsOpen Ω) (N : ℕ) :
    FiniteDimensional ℝ (galerkinValueSpace hΩ N) := by
  unfold galerkinValueSpace
  infer_instance

/-- The finite Galerkin value space is complete. -/
instance galerkinValueSpace_completeSpace
    (hΩ : IsOpen Ω) (N : ℕ) :
    CompleteSpace (galerkinValueSpace hΩ N) :=
  FiniteDimensional.complete ℝ _

variable (hΩ : IsOpen Ω) (N : ℕ)

/-- The `L²` mass Gram matrix of the finite actual-test Galerkin basis. -/
def galerkinMassGram
      :=
  Matrix.gram ℝ (fun i =>
    valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ))

/-- The finite `L²` mass Gram matrix is positive definite. -/
theorem galerkinMassGram_posDef
     :
    (galerkinMassGram hΩ N).PosDef := by
  let E := galerkinSpace hΩ N
  let L : E →ₗ[ℝ] PDE.ScalarLp Ω (2 ) :=
    (valueCLM hΩ).toLinearMap.comp E.subtype

  have hli : LinearIndependent ℝ (L ∘ galerkinSpaceBasis hΩ N) :=
    (galerkinSpaceBasis hΩ N).linearIndependent.map' L
      (LinearMap.ker_eq_bot_of_injective (by
          intro u v huv
          apply Subtype.ext
          exact valueCLM_injective hΩ huv))
  simpa only [L, E, galerkinMassGram, LinearMap.coe_comp, ContinuousLinearMap.coe_coe,
    Submodule.coe_subtype, Function.comp_def] using Matrix.posDef_gram_of_linearIndependent hli

/-- The finite `L²` mass Gram matrix is invertible, including at `N = 0`. -/
theorem isUnit_galerkinMassGram
     :
    IsUnit (galerkinMassGram hΩ N) :=
  (galerkinMassGram_posDef hΩ N).isUnit

variable (initial : PDE.ScalarLp Ω (2 ))

/-- A chosen preimage of the finite Galerkin value-space projection. -/
def galerkinInitialProjectionPreimage

     :
    H10HilbertGraph hΩ :=
  Classical.choose <| Submodule.mem_map.mp
    (Submodule.starProjection_apply_mem (galerkinValueSpace hΩ N) initial)

/-- The chosen projection preimage lies in the finite Galerkin space. -/
theorem galerkinInitialProjectionPreimage_mem

     :
    galerkinInitialProjectionPreimage hΩ N initial ∈ galerkinSpace hΩ N := (Classical.choose_spec <| Submodule.mem_map.mp
    (Submodule.starProjection_apply_mem (galerkinValueSpace hΩ N) initial)).1

private theorem value_galerkinInitialProjectionPreimage

     :
    valueCLM hΩ (galerkinInitialProjectionPreimage hΩ N initial) =
      (galerkinValueSpace hΩ N).starProjection initial := (Classical.choose_spec <| Submodule.mem_map.mp
    (Submodule.starProjection_apply_mem (galerkinValueSpace hΩ N) initial)).2

/-- The lift to the finite Galerkin space of the `L²` orthogonal projection
of an initial datum. -/
def galerkinInitialProjection

     :
    galerkinSpace hΩ N :=
  ⟨_,
    galerkinInitialProjectionPreimage_mem hΩ N initial⟩

/-- Applying the spatial value map to the lifted initial datum recovers its
`L²` orthogonal projection onto the finite Galerkin value space. -/
theorem value_galerkinInitialProjection

     :
    valueCLM hΩ (galerkinInitialProjection hΩ N initial :
      H10HilbertGraph hΩ) =
    (galerkinValueSpace hΩ N).starProjection initial :=
  value_galerkinInitialProjectionPreimage hΩ N initial

/-- The finite Galerkin `L²` initial projection is contractive. -/
theorem norm_value_galerkinInitialProjection_le

     :
    ‖valueCLM hΩ (galerkinInitialProjection hΩ N initial :
      H10HilbertGraph hΩ)‖ ≤ ‖initial‖ := by
  rw [value_galerkinInitialProjection]
  exact (galerkinValueSpace hΩ N).norm_starProjection_apply_le initial

end HypoellipticAleksandrov.Parabolic.Dirichlet
