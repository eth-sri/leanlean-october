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

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)

/-- The existence witness used to select the uniform Galerkin curves and constants. -/
noncomputable def reverseTimeGalerkinPrimalWitness :=
  exists_reverseTimeGalerkin_uniform_energy_solution P

local notation "primalWitness" => reverseTimeGalerkinPrimalWitness P

/-- The first globally uniform energy constant selected from the finite
Galerkin energy existence theorem. -/
noncomputable def reverseTimeGalerkinPrimalK : ℝ :=
  (primalWitness).choose

local notation "primalK" => reverseTimeGalerkinPrimalK P

/-- The second globally uniform energy constant from the same selected
existence witness as `reverseTimeGalerkinPrimalK`. -/
noncomputable def reverseTimeGalerkinPrimalM : ℝ :=
  ((primalWitness).choose_spec.2).choose

local notation "primalM" => reverseTimeGalerkinPrimalM P

/-- The selected finite-coordinate reverse-time Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimalCoordinate
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ℝ → GalerkinCoordinates P.hΩ N :=
  ((primalWitness).choose_spec.2.choose_spec.2
      N initial).choose

local notation "primalCoordinate" => reverseTimeGalerkinPrimalCoordinate P

section
variable (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
include N initial

/-- The selected coordinate curve solves the finite Galerkin equation. -/
theorem reverseTimeGalerkinPrimal_trajectory :
    IsGalerkinTrajectory P N initial (primalCoordinate N initial) :=
  ((primalWitness).choose_spec.2.choose_spec.2 N initial).choose_spec.1

/-- The raw Sobolev curve reconstructed directly from the selected coordinates.
This curve is not quotient-valued. -/
noncomputable def reverseTimeGalerkinPrimalRaw :
    ℝ → H10HilbertGraph P.hΩ :=
  fun τ => (galerkinReconstruct P.hΩ N
    (primalCoordinate N initial τ) :
      H10HilbertGraph P.hΩ)

end

local notation "primalRaw" => reverseTimeGalerkinPrimalRaw P

/-- The globally selected first energy constant is nonnegative. -/
theorem reverseTimeGalerkinPrimalK_nonneg :
    0 ≤ primalK := (primalWitness).choose_spec.1

section
variable (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
include N initial

/-- The selected raw Galerkin reconstruction is continuous on the closed
reverse-time interval. -/
theorem continuousOn_reverseTimeGalerkinPrimalRaw :
    ContinuousOn
      (primalRaw N initial)
      (Set.Icc 0 (r₁ - r₀)) := continuousOn_galerkinReconstruct
  (reverseTimeGalerkinPrimal_trajectory P N initial).continuousOn

/-- At reverse time zero, the selected raw curve is the finite Galerkin
projection of the prescribed initial datum. -/
theorem reverseTimeGalerkinPrimalRaw_zero :
    primalRaw N initial 0 =
      (galerkinInitialProjection P.hΩ N initial : H10HilbertGraph P.hΩ) := by
  have hx0 := (reverseTimeGalerkinPrimal_trajectory P N initial).initial_eq
  change (↑(galerkinReconstruct P.hΩ N (primalCoordinate N initial 0)) : H10HilbertGraph P.hΩ) = _
  rw [hx0, galerkinReconstruct_equivFun]

section
variable (t : ℝ) (ht : t ∈ Set.Icc 0 (r₁ - r₀))
include ht

/-- The selected raw curve obeys the sharp pointwise value-energy estimate. -/
theorem reverseTimeGalerkinPrimal_value_energy :
    ‖valueCLM P.hΩ
      (primalRaw N initial t)‖ ^ 2 ≤
      gronwallBound (‖initial‖ ^ 2)
        (2 * primalK + 1)
        (primalM ^ 2) t := ((primalWitness).choose_spec.2.choose_spec.2 N initial).choose_spec.2.1 t ht

/-- The selected raw curve obeys the sharp integrated gradient-energy estimate. -/
theorem reverseTimeGalerkinPrimal_gradient_energy :
    lam * ∫ τ in Set.Ioc 0 t,
      ‖gradientCLM P.hΩ
        (primalRaw N initial τ)‖ ^ 2 ≤
      ‖initial‖ ^ 2 +
        (2 * primalK + 1) * t *
          gronwallBound (‖initial‖ ^ 2)
            (2 * primalK + 1)
            (primalM ^ 2)
            (r₁ - r₀) +
        (primalM ^ 2) * t := ((primalWitness).choose_spec.2.choose_spec.2 N initial).choose_spec.2.2 t ht

end

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
