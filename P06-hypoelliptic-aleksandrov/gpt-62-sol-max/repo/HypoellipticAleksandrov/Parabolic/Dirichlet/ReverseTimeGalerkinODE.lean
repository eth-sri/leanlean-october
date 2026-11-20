module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GlobalLinearODE
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCoordinates

/-!
# Reverse-time finite Galerkin ODE solutions

This module lifts the finite-coordinate ODE to the Galerkin space and
records its exact basis-row weak equation.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise RealInnerProductSpace

/-- The data of a smooth reflected Dirichlet problem used by the Galerkin construction. -/
structure ReverseTimeGalerkinProblem {d : ℕ} (Ω : Set (PDE.Vec d)) (r₀ r₁ lam : ℝ) where
  h₀₁ : r₀ < r₁
  hlam : 0 < lam
  hΩ : IsOpen Ω
  hΩbounded : Bornology.IsBounded Ω
  a : CoefficientField d
  b : ℝ → PDE.Vec d → PDE.Vec d
  c : ℝ → PDE.Vec d → ℝ
  F : ℝ → PDE.Vec d → ℝ
  haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a
  hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b
  hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c
  hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F
  hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω)
  hcNonpos : ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω, c z.1 z.2 ≤ 0

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)

/-- The reflected spatial operator tested on a pair of Sobolev vectors. -/
noncomputable abbrev ReverseTimeGalerkinProblem.form := fun t => reverseTimeSpatialForm P.hΩ r₁ t P.a P.b P.c

/-- The reflected negative source as a spatial dual functional. -/
noncomputable abbrev ReverseTimeGalerkinProblem.sourceRaw :=
  reverseTimeNegativeSourceRaw r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.F P.hFSmooth

end

/-- The Galerkin ODE right-hand side on its closed time interval. -/
abbrev galerkinRate
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) (x : GalerkinCoordinates P.hΩ N) : GalerkinCoordinates P.hΩ N :=
  reverseTimeGalerkinLinearPart r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.a P.b P.c P.haSmooth P.hbSmooth P.hcSmooth N τ x +
    reverseTimeGalerkinForcing r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.F P.hFSmooth N τ

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam) (N : ℕ)

/-- Evaluating the time-clamped rate along P.a continuous coordinate curve is continuous. -/
theorem continuousOn_galerkinRate {x : ℝ → GalerkinCoordinates P.hΩ N} (hx : ContinuousOn x (Set.Icc 0 (r₁ - r₀))) :
    ContinuousOn (fun t => galerkinRate P N
      (Set.projIcc 0 (r₁ - r₀) (sub_nonneg.mpr P.h₀₁.le) t) (x t)) (Set.Icc 0 (r₁ - r₀)) := by
  have hA := (continuous_reverseTimeGalerkinLinearPart r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.a P.b P.c
    P.haSmooth P.hbSmooth P.hcSmooth N).comp (continuous_projIcc (h := sub_nonneg.mpr P.h₀₁.le))
  have hf := (continuous_reverseTimeGalerkinForcing r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.F
    P.hFSmooth N).comp (continuous_projIcc (h := sub_nonneg.mpr P.h₀₁.le))
  exact (hA.continuousOn.clm_apply hx).add hf.continuousOn

/-- The mass-inverted rate satisfies the weak equation on each basis row. -/
theorem galerkinRate_row (τ : Set.Icc 0 (r₁ - r₀)) (x : GalerkinCoordinates P.hΩ N) (i : GalerkinIndex P.hΩ N) :
    inner ℝ (valueCLM P.hΩ (galerkinReconstructCLM P.hΩ N (galerkinRate P N τ x)))
      (valueCLM P.hΩ (galerkinSpaceBasis P.hΩ N i : H10HilbertGraph P.hΩ)) +
    reverseTimeSpatialForm P.hΩ r₁ τ.1 P.a P.b P.c (galerkinReconstructCLM P.hΩ N x)
      (galerkinSpaceBasis P.hΩ N i : H10HilbertGraph P.hΩ) =
    reverseTimeGalerkinSource r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.F P.hFSmooth N τ i :=
  (reverseTimeGalerkin_coordinateEquation_iff_aux r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.a P.b P.c P.F P.haSmooth P.hbSmooth P.hcSmooth P.hFSmooth
    N τ x (galerkinRate P N τ x)).mpr rfl i

end

/-- A coordinate trajectory with its Galerkin initial condition and ODE. -/
structure IsGalerkinTrajectory
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (x : ℝ → GalerkinCoordinates P.hΩ N) : Prop where
  initial_eq : x 0 = (galerkinSpaceBasis P.hΩ N).equivFun (galerkinInitialProjection P.hΩ N initial)
  continuousOn : ContinuousOn x (Set.Icc 0 (r₁ - r₀))
  deriv (τ : Set.Icc 0 (r₁ - r₀)) : HasDerivWithinAt x
    (galerkinRate P N τ (x τ)) (Set.Icc 0 (r₁ - r₀)) τ

/-- A reverse-time finite Galerkin coordinate solution and its reconstruction exist. -/
theorem exists_reverseTimeGalerkin_solution
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ x, IsGalerkinTrajectory P N initial x := by
  let T := r₁ - r₀
  have hT : 0 ≤ T := sub_nonneg.mpr P.h₀₁.le
  let x0 : GalerkinCoordinates P.hΩ N :=
    (galerkinSpaceBasis P.hΩ N).equivFun (galerkinInitialProjection P.hΩ N initial)
  let A : ℝ → GalerkinCoordinates P.hΩ N →L[ℝ]
      (GalerkinCoordinates P.hΩ N) :=
    fun τ => reverseTimeGalerkinLinearPart r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.a P.b P.c
      P.haSmooth P.hbSmooth P.hcSmooth N (Set.projIcc 0 T hT τ)
  let f : ℝ → GalerkinCoordinates P.hΩ N :=
    fun τ => reverseTimeGalerkinForcing r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.F P.hFSmooth N
      (Set.projIcc 0 T hT τ)
  have hA : ContinuousOn A (Set.Icc 0 T) := by
    exact ((continuous_reverseTimeGalerkinLinearPart r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.a P.b P.c
      P.haSmooth P.hbSmooth P.hcSmooth N).comp continuous_projIcc).continuousOn
  have hf : ContinuousOn f (Set.Icc 0 T) := by
    exact ((continuous_reverseTimeGalerkinForcing r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.F P.hFSmooth N).comp
      continuous_projIcc).continuousOn
  obtain ⟨x, hx0, hxc, hxd⟩ := exists_linear_ode_on_Icc hT A f hA hf x0
  refine ⟨x, hx0, hxc, fun τ => ?_⟩
  simpa only [galerkinRate, A, f, Set.projIcc_of_mem hT τ.2] using hxd τ τ.2

end HypoellipticAleksandrov.Parabolic.Dirichlet
