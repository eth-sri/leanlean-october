module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevSeparable
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDistribution
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTimeDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.IntegralGronwall

/-!
# Reverse-time variational energy uniqueness

This file proves the literal difference-energy estimate and uniqueness for
reverse-time variational solutions of the homogeneous-lateral Dirichlet problem.
It does not construct solutions.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance instReverseTimeL2VStarModuleEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  MeasureTheory.Lp.instModule

/-- A literal common-event weak variational solution of the reversed,
homogeneous-lateral Dirichlet energy problem. -/
def IsReverseTimeVariationalEnergySolution
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g) : Prop :=
  reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu = initial ∧
  ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
    ∀ hτ : τ ∈ Set.Ioo 0 (r₁ - r₀),
    ∀ v : H10HilbertGraph hΩ,
      (g τ) v + reverseTimeSpatialForm hΩ r₁ τ a b c (u τ) v =
        reverseTimeSourceFunctional hΩ
          (reverseTimeSourceSlice r₁ τ F
            (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
              r₀ r₁ hΩ hΩbounded F hFSmooth τ
              ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩)) v

























