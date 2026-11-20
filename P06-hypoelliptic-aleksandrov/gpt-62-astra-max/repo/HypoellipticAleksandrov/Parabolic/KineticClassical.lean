module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import HypoellipticAleksandrov.Ambient.MatrixContraction
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Geometry.KineticPoint
public import PDEFoundation.Sobolev.ClassicalGradient

/-!
# Classical kinetic product API

This module fixes the product-cylinder geometry, anisotropic classical
regularity, and plus-sign kinetic operator used in the time-velocity estimates.  The kinetic points
retain their explicit time, position, and velocity fields; product sets are transported only through
`KineticPoint.homeomorphProd`.

No maximum theorem is proved here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

section
variable {d : ℕ} (r₀ r₁ : ℝ) (Ωx Ωv : Set (PDE.Vec d))

end

section
variable {d : ℕ} {r₀ r₁ : ℝ} {Ωx Ωv : Set (PDE.Vec d)} {z : KineticPoint d}

end

section
variable {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d)
include u

include z in
/-- The time derivative with position and velocity held fixed. -/
def kineticTimeDerivative : ℝ :=
  deriv (fun r => u ⟨r, z.position, z.velocity⟩) z.time

include z in
/-- The position gradient with time and velocity held fixed. -/
def kineticPositionGradient :
    PDE.Vec d :=
  PDE.classicalGradient (fun x => u ⟨z.time, x, z.velocity⟩) z.position

include z in
/-- The velocity gradient with time and position held fixed. -/
def kineticVelocityGradient :
    PDE.Vec d :=
  PDE.classicalGradient (fun v => u ⟨z.time, z.position, v⟩) z.velocity

include z in
/-- The velocity Hessian indexed as `D_i(D_j u)`. -/
def kineticVelocityHessian :
    PDE.Mat d :=
  fun i j =>
    (fderiv ℝ (fun v : PDE.Vec d =>
      PDE.classicalGradient (fun w : PDE.Vec d => u ⟨z.time, z.position, w⟩) v)
      z.velocity (PDE.basisVec i)) j

/--
The anisotropic kinetic `C^{1,1,2}` regularity predicate. It asks only for
one time, one position, and two velocity derivatives on separate slices.
-/
def IsKineticC112On (D : Set (KineticPoint d)) : Prop :=
  ContinuousOn u D ∧
    (∀ z ∈ D, DifferentiableAt ℝ (fun r => u ⟨r, z.position, z.velocity⟩) z.time) ∧
    (∀ z ∈ D, ContDiffAt ℝ 1 (fun x => u ⟨z.time, x, z.velocity⟩) z.position) ∧
    (∀ z ∈ D, ContDiffAt ℝ 2 (fun v => u ⟨z.time, z.position, v⟩) z.velocity) ∧
    ContinuousOn (kineticTimeDerivative u) D ∧
    ContinuousOn (kineticPositionGradient u) D ∧
    ContinuousOn (kineticVelocityGradient u) D ∧
    ContinuousOn (kineticVelocityHessian u) D

end

namespace IsKineticC112On

section
variable {d : ℕ} {u : KineticPoint d → ℝ} {D : Set (KineticPoint d)} (h : IsKineticC112On u D)
    {z : KineticPoint d} (hz : z ∈ D)
include h

/-- The function itself is continuous on the specified set. -/
theorem continuousOn : ContinuousOn u D :=
  h.1

include hz in
/-- Each fixed-position-and-velocity time slice is differentiable on the set. -/
theorem timeSlice_differentiableAt :
    DifferentiableAt ℝ (fun r => u ⟨r, z.position, z.velocity⟩) z.time :=
  h.2.1 z hz

include hz in
/-- Each fixed-time-and-velocity position slice is `C¹` on the set. -/
theorem positionSlice_contDiffAt :
    ContDiffAt ℝ 1 (fun x => u ⟨z.time, x, z.velocity⟩) z.position :=
  h.2.2.1 z hz

include hz in
/-- Each fixed-time-and-position velocity slice is `C²` on the set. -/
theorem velocitySlice_contDiffAt :
    ContDiffAt ℝ 2 (fun v => u ⟨z.time, z.position, v⟩) z.velocity :=
  h.2.2.2.1 z hz

/-- The kinetic time derivative is continuous on the specified set. -/
theorem continuousOn_kineticTimeDerivative :
    ContinuousOn (kineticTimeDerivative u) D :=
  h.2.2.2.2.1

/-- The kinetic position gradient is continuous on the specified set. -/
theorem continuousOn_kineticPositionGradient :
    ContinuousOn (kineticPositionGradient u) D :=
  h.2.2.2.2.2.1

/-- The kinetic velocity gradient is continuous on the specified set. -/
theorem continuousOn_kineticVelocityGradient :
    ContinuousOn (kineticVelocityGradient u) D :=
  h.2.2.2.2.2.2.1

/-- The kinetic velocity Hessian is continuous on the specified set. -/
theorem continuousOn_kineticVelocityHessian :
    ContinuousOn (kineticVelocityHessian u) D :=
  h.2.2.2.2.2.2.2

include hz in
/-- The fixed-position-and-velocity time slice has its kinetic time derivative. -/
theorem timeSlice_hasDerivAt :
    HasDerivAt (fun r => u ⟨r, z.position, z.velocity⟩) (kineticTimeDerivative u z)
      z.time := (h.timeSlice_differentiableAt hz).hasDerivAt

end

end IsKineticC112On

variable {d : ℕ} (A : CoefficientField d) (u : KineticPoint d → ℝ) (z : KineticPoint d)

end HypoellipticAleksandrov.Parabolic
