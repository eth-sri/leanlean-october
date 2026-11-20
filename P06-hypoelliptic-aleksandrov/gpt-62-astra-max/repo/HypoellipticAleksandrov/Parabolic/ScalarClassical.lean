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

include r₀ r₁ Ω in
/-- The open scalar parabolic cylinder `(r₀, r₁) × Ω`. -/
def scalarParabolicOpenCylinder :
    Set (TimeVelocity n) :=
  Set.Ioo r₀ r₁ ×ˢ Ω

include r₀ r₁ Ω in
/-- The closed scalar parabolic cylinder `[r₀, r₁] × closure Ω`. -/
def scalarParabolicClosedCylinder :
    Set (TimeVelocity n) :=
  Set.Icc r₀ r₁ ×ˢ closure Ω

/-- The terminal face `{r₁} × closure Ω` of a scalar parabolic cylinder. -/
def scalarParabolicTerminalFace (r₁ : ℝ) (Ω : Set (PDE.Vec n)) :
    Set (TimeVelocity n) :=
  ({r₁} : Set ℝ) ×ˢ closure Ω

include r₀ r₁ Ω in
/-- The lateral face `[r₀, r₁] × frontier Ω` of a scalar parabolic cylinder. -/
def scalarParabolicLateralFace :
    Set (TimeVelocity n) :=
  Set.Icc r₀ r₁ ×ˢ frontier Ω

end

section
variable {n : ℕ} {r₀ r₁ r : ℝ} (u : TimeVelocity n → ℝ) {Ω : Set (PDE.Vec n)} (z : TimeVelocity n)
    {y : PDE.Vec n}

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

/-- Membership in the terminal face of a scalar parabolic cylinder. -/
@[simp] theorem mem_scalarParabolicTerminalFace_iff {r₁ r : ℝ}
    {Ω : Set (PDE.Vec n)} {y : PDE.Vec n} :
    (r, y) ∈ scalarParabolicTerminalFace r₁ Ω ↔ r = r₁ ∧ y ∈ closure Ω := by
  simp [scalarParabolicTerminalFace]

/-- Membership in the lateral face of a scalar parabolic cylinder. -/
@[simp] theorem mem_scalarParabolicLateralFace_iff :
    (r, y) ∈ scalarParabolicLateralFace r₀ r₁ Ω ↔
      r₀ ≤ r ∧ r ≤ r₁ ∧ y ∈ frontier Ω := by
  constructor
  · rintro ⟨⟨hr₀, hr₁⟩, hy⟩
    exact ⟨hr₀, hr₁, hy⟩
  · rintro ⟨hr₀, hr₁, hy⟩
    exact ⟨⟨hr₀, hr₁⟩, hy⟩

include u z in
/-- The time derivative of `u`, with the velocity coordinate fixed. -/
def scalarTimeDerivative : ℝ :=
  deriv (fun r : ℝ => u (r, z.2)) z.1

include u z in
/-- The spatial coordinate gradient of `u` at a fixed time. -/
def scalarSpatialGradient :
    PDE.Vec n :=
  PDE.classicalGradient (fun y : PDE.Vec n => u (z.1, y)) z.2

include u z in
/-- The spatial Hessian of `u`, indexed as `D_i(D_j u)`. -/
def scalarSpatialHessian :
    PDE.Mat n :=
  fun i j =>
    (fderiv ℝ (fun y : PDE.Vec n =>
      PDE.classicalGradient (fun w : PDE.Vec n => u (z.1, w)) y) z.2
      (PDE.basisVec i)) j

include u in
/--
The anisotropic scalar `C^{1,2}` regularity required by the classical
parabolic maximum principle.  It demands no mixed or second time derivatives.
-/
def IsScalarC12On (D : Set (TimeVelocity n)) : Prop :=
  ContinuousOn u D ∧
    (∀ z ∈ D, DifferentiableAt ℝ (fun r : ℝ => u (r, z.2)) z.1) ∧
    (∀ z ∈ D, ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2) ∧
    ContinuousOn (scalarTimeDerivative u) D ∧
    ContinuousOn (scalarSpatialGradient u) D ∧
    ContinuousOn (scalarSpatialHessian u) D

end

namespace IsScalarC12On

section
variable {n : ℕ} {u : TimeVelocity n → ℝ} {D : Set (TimeVelocity n)} (h : IsScalarC12On u D)
    {z : TimeVelocity n} (hz : z ∈ D)
include h

/-- The function itself is continuous on the specified set. -/
theorem continuousOn :
    ContinuousOn u D :=
  h.1

include hz in
/-- Each fixed-velocity time slice is differentiable at points of the set. -/
theorem timeSlice_differentiableAt :
    DifferentiableAt ℝ (fun r : ℝ => u (r, z.2)) z.1 :=
  h.2.1 z hz

include hz in
/-- Each fixed-time spatial slice is `C²` at points of the set. -/
theorem spatialSlice_contDiffAt :
    ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2 :=
  h.2.2.1 z hz

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

include hz in
/-- The fixed-velocity time slice has derivative `scalarTimeDerivative`. -/
theorem timeSlice_hasDerivAt :
    HasDerivAt (fun r : ℝ => u (r, z.2)) (scalarTimeDerivative u z) z.1 := (h.timeSlice_differentiableAt hz).hasDerivAt

end

end IsScalarC12On

variable {n : ℕ} (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n) (u : TimeVelocity n → ℝ)
    (z : TimeVelocity n)

include a b u z in
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

end HypoellipticAleksandrov.Parabolic
