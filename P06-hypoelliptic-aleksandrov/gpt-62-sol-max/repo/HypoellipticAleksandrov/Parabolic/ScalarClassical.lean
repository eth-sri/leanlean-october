module

public import HypoellipticAleksandrov.Ambient.MatrixContraction
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import PDEFoundation.Sobolev.ClassicalGradient

/-!
# Scalar classical parabolic carrier

This module records the exact anisotropic `C^{1,2}` carrier and plus-sign
scalar parabolic operator used by the backward maximum principle.  It supplies only
the definitions and elementary accessors needed to state that principle; no
maximum theorem is proved here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

section
variable {n : ℕ} (r₀ r₁ : ℝ) (Ω : Set (PDE.Vec n))
include r₀ r₁ Ω

/-- The open scalar parabolic cylinder `(r₀, r₁) × Ω`. -/
def scalarParabolicOpenCylinder :
    Set (TimeVelocity n) :=
  Set.Ioo r₀ r₁ ×ˢ Ω

/-- The closed scalar parabolic cylinder `[r₀, r₁] × closure Ω`. -/
def scalarParabolicClosedCylinder :
    Set (TimeVelocity n) :=
  Set.Icc r₀ r₁ ×ˢ closure Ω

end

/-- The terminal face `{r₁} × closure Ω` of a scalar parabolic cylinder. -/
def scalarParabolicTerminalFace {n : ℕ} (r₁ : ℝ) (Ω : Set (PDE.Vec n)) :
    Set (TimeVelocity n) :=
  ({r₁} : Set ℝ) ×ˢ closure Ω

section
variable {n : ℕ} (r₀ r₁ : ℝ) (Ω : Set (PDE.Vec n))
include r₀ r₁ Ω

/-- The lateral face `[r₀, r₁] × frontier Ω` of a scalar parabolic cylinder. -/
def scalarParabolicLateralFace :
    Set (TimeVelocity n) :=
  Set.Icc r₀ r₁ ×ˢ frontier Ω

/-- The terminal-lateral boundary of a scalar parabolic cylinder. -/
def scalarParabolicTerminalLateralBoundary :
    Set (TimeVelocity n) :=
  scalarParabolicTerminalFace r₁ Ω ∪ scalarParabolicLateralFace r₀ r₁ Ω

end

section
variable {n : ℕ} {r₀ r₁ r : ℝ} {Ω : Set (PDE.Vec n)} {y : PDE.Vec n}

/-- Membership in an open scalar parabolic cylinder. -/
@[simp] theorem mem_scalarParabolicOpenCylinder_iff :
    (r, y) ∈ scalarParabolicOpenCylinder r₀ r₁ Ω ↔
      r₀ < r ∧ r < r₁ ∧ y ∈ Ω := by
  constructor
  · rintro ⟨⟨hr₀, hr₁⟩, hy⟩
    exact ⟨hr₀, hr₁, hy⟩
  · rintro ⟨hr₀, hr₁, hy⟩
    exact ⟨⟨hr₀, hr₁⟩, hy⟩

/-- Membership in a closed scalar parabolic cylinder. -/
@[simp] theorem mem_scalarParabolicClosedCylinder_iff :
    (r, y) ∈ scalarParabolicClosedCylinder r₀ r₁ Ω ↔
      r₀ ≤ r ∧ r ≤ r₁ ∧ y ∈ closure Ω := by
  constructor
  · rintro ⟨⟨hr₀, hr₁⟩, hy⟩
    exact ⟨hr₀, hr₁, hy⟩
  · rintro ⟨hr₀, hr₁, hy⟩
    exact ⟨⟨hr₀, hr₁⟩, hy⟩

end

/-- Membership in the terminal face of a scalar parabolic cylinder. -/
@[simp] theorem mem_scalarParabolicTerminalFace_iff {n : ℕ} {r₁ r : ℝ}
    {Ω : Set (PDE.Vec n)} {y : PDE.Vec n} :
    (r, y) ∈ scalarParabolicTerminalFace r₁ Ω ↔ r = r₁ ∧ y ∈ closure Ω := by
  simp [scalarParabolicTerminalFace]

section
variable {n : ℕ} {r₀ r₁ r : ℝ} {Ω : Set (PDE.Vec n)} {y : PDE.Vec n}

/-- Membership in the lateral face of a scalar parabolic cylinder. -/
@[simp] theorem mem_scalarParabolicLateralFace_iff :
    (r, y) ∈ scalarParabolicLateralFace r₀ r₁ Ω ↔
      r₀ ≤ r ∧ r ≤ r₁ ∧ y ∈ frontier Ω := by
  constructor
  · rintro ⟨⟨hr₀, hr₁⟩, hy⟩
    exact ⟨hr₀, hr₁, hy⟩
  · rintro ⟨hr₀, hr₁, hy⟩
    exact ⟨⟨hr₀, hr₁⟩, hy⟩

/-- Membership in the terminal-lateral boundary of a scalar parabolic cylinder. -/
@[simp] theorem mem_scalarParabolicTerminalLateralBoundary_iff :
    (r, y) ∈ scalarParabolicTerminalLateralBoundary r₀ r₁ Ω ↔
      (r = r₁ ∧ y ∈ closure Ω) ∨ (r₀ ≤ r ∧ r ≤ r₁ ∧ y ∈ frontier Ω) := by
  simp [scalarParabolicTerminalLateralBoundary]

end

section
variable {n : ℕ} (u : TimeVelocity n → ℝ) (z : TimeVelocity n)
include n u z

/-- The time derivative of `u`, with the velocity coordinate fixed. -/
def scalarTimeDerivative : ℝ :=
  deriv (fun r : ℝ => u (r, z.2)) z.1

/-- The spatial coordinate gradient of `u` at a fixed time. -/
def scalarSpatialGradient :
    PDE.Vec n :=
  PDE.classicalGradient (fun y : PDE.Vec n => u (z.1, y)) z.2

/-- The spatial Hessian of `u`, indexed as `D_i(D_j u)`. -/
def scalarSpatialHessian :
    PDE.Mat n :=
  fun i j =>
    (fderiv ℝ (fun y : PDE.Vec n =>
      PDE.classicalGradient (fun w : PDE.Vec n => u (z.1, w)) y) z.2
      (PDE.basisVec i)) j

end

/--
The anisotropic scalar `C^{1,2}` regularity required by the classical
parabolic maximum principle.  It demands no mixed or second time derivatives.
-/
def IsScalarC12On {n : ℕ} (u : TimeVelocity n → ℝ) (D : Set (TimeVelocity n)) : Prop :=
  ContinuousOn u D ∧
    (∀ z ∈ D, DifferentiableAt ℝ (fun r : ℝ => u (r, z.2)) z.1) ∧
    (∀ z ∈ D, ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2) ∧
    ContinuousOn (scalarTimeDerivative u) D ∧
    ContinuousOn (scalarSpatialGradient u) D ∧
    ContinuousOn (scalarSpatialHessian u) D

namespace IsScalarC12On

section
variable {n : ℕ} {u : TimeVelocity n → ℝ} {D : Set (TimeVelocity n)} (h : IsScalarC12On u D)
include h

/-- The function itself is continuous on the specified set. -/
theorem continuousOn :
    ContinuousOn u D :=
  h.1

section
variable {z : TimeVelocity n} (hz : z ∈ D)
include hz

/-- Each fixed-velocity time slice is differentiable at points of the set. -/
theorem timeSlice_differentiableAt :
    DifferentiableAt ℝ (fun r : ℝ => u (r, z.2)) z.1 :=
  h.2.1 z hz

/-- Each fixed-time spatial slice is `C²` at points of the set. -/
theorem spatialSlice_contDiffAt :
    ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2 :=
  h.2.2.1 z hz

end

/-- The scalar time derivative is continuous on the specified set. -/
theorem continuousOn_scalarTimeDerivative :
    ContinuousOn (scalarTimeDerivative u) D :=
  h.2.2.2.1

/-- The scalar spatial gradient is continuous on the specified set. -/
theorem continuousOn_scalarSpatialGradient :
    ContinuousOn (scalarSpatialGradient u) D :=
  h.2.2.2.2.1

/-- The scalar spatial Hessian is continuous on the specified set. -/
theorem continuousOn_scalarSpatialHessian :
    ContinuousOn (scalarSpatialHessian u) D :=
  h.2.2.2.2.2

end

/-- The fixed-velocity time slice has derivative `scalarTimeDerivative`. -/
theorem timeSlice_hasDerivAt {n : ℕ} {u : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (h : IsScalarC12On u D) {z : TimeVelocity n}
    (hz : z ∈ D) :
    HasDerivAt (fun r : ℝ => u (r, z.2)) (scalarTimeDerivative u z) z.1 := (h.timeSlice_differentiableAt hz).hasDerivAt

end IsScalarC12On

section
variable {n : ℕ} (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n) (u : TimeVelocity n → ℝ)
  (z : TimeVelocity n)
include n a b u z

/-- The scalar parabolic operator `∂_r + a : D²_y + b · D_y`. -/
def scalarParabolicOperator : ℝ :=
  scalarTimeDerivative u z +
    matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) +
    PDE.vecDot (b z.1 z.2) (scalarSpatialGradient u z)

/-- Evaluation of the scalar parabolic operator. -/
@[simp] theorem scalarParabolicOperator_apply :
    scalarParabolicOperator a b u z =
      scalarTimeDerivative u z +
        matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) +
        PDE.vecDot (b z.1 z.2) (scalarSpatialGradient u z) :=
  rfl

end

end HypoellipticAleksandrov.Parabolic
