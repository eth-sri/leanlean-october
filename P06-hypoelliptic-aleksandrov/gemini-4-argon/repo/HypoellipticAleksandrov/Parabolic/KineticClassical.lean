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

/- The open kinetic product cylinder `(r₀, r₁) × (Ωx × Ωv)`. -/
def kineticTimeDerivative {d } (u : KineticPoint d → ℝ) (z : KineticPoint d) : ℝ :=
  deriv (fun r => u ⟨r, z.position, z.velocity⟩) z.time

/- The position gradient with time and velocity held fixed. -/
def kineticPositionGradient {d } (u : KineticPoint d → ℝ) (z : KineticPoint d) :
    PDE.Vec d :=
  PDE.classicalGradient (fun x => u ⟨z.time, x, z.velocity⟩) z.position

/- The velocity gradient with time and position held fixed. -/
def kineticVelocityGradient {d } (u : KineticPoint d → ℝ) (z : KineticPoint d) :
    PDE.Vec d :=
  PDE.classicalGradient (fun v => u ⟨z.time, z.position, v⟩) z.velocity

/- The velocity Hessian indexed as `D_i(D_j u)`. -/
def kineticVelocityHessian {d } (u : KineticPoint d → ℝ) (z : KineticPoint d) :
    PDE.Mat d :=
  fun i j =>
    (fderiv ℝ (fun v : PDE.Vec d =>
      PDE.classicalGradient (fun w : PDE.Vec d => u ⟨z.time, z.position, w⟩) v)
      z.velocity (PDE.basisVec i)) j

/-
The anisotropic kinetic `C^{1,1,2}` regularity predicate. It asks only for
one time, one position, and two velocity derivatives on separate slices.
-/
def IsKineticC112On {d } (u : KineticPoint d → ℝ) (D : Set (KineticPoint d)) : Prop :=
  ContinuousOn u D ∧
    (∀ z ∈ D, DifferentiableAt ℝ (fun r => u ⟨r, z.position, z.velocity⟩) z.time) ∧
    (∀ z ∈ D, ContDiffAt ℝ 1 (fun x => u ⟨z.time, x, z.velocity⟩) z.position) ∧
    (∀ z ∈ D, ContDiffAt ℝ 2 (fun v => u ⟨z.time, z.position, v⟩) z.velocity) ∧
    ContinuousOn (kineticTimeDerivative u) D ∧
    ContinuousOn (kineticPositionGradient u) D ∧
    ContinuousOn (kineticVelocityGradient u) D ∧
    ContinuousOn (kineticVelocityHessian u) D

namespace IsKineticC112On

/- The function itself is continuous on the specified set. -/
theorem continuousOn {d u} {D : Set (KineticPoint d)}
    (h : IsKineticC112On u D) : ContinuousOn u D :=
  h.1

/- Each fixed-position-and-velocity time slice is differentiable on the set. -/
theorem timeSlice_differentiableAt {d u D} (h : IsKineticC112On u D) {z : KineticPoint d}
    (hz : z ∈ D) :
    DifferentiableAt ℝ (fun r => u ⟨r, z.position, z.velocity⟩) z.time :=
  h.2.1 z hz

/- Each fixed-time-and-velocity position slice is `C¹` on the set. -/
theorem positionSlice_contDiffAt {d u D} (h : IsKineticC112On u D) {z : KineticPoint d}
    (hz : z ∈ D) :
    ContDiffAt ℝ 1 (fun x => u ⟨z.time, x, z.velocity⟩) z.position :=
  h.2.2.1 z hz

/- Each fixed-time-and-position velocity slice is `C²` on the set. -/
theorem velocitySlice_contDiffAt {d u D} (h : IsKineticC112On u D) {z : KineticPoint d}
    (hz : z ∈ D) :
    ContDiffAt ℝ 2 (fun v => u ⟨z.time, z.position, v⟩) z.velocity :=
  h.2.2.2.1 z hz

/- The kinetic time derivative is continuous on the specified set. -/
theorem continuousOn_kineticTimeDerivative {d u}
    {D : Set (KineticPoint d)} (h : IsKineticC112On u D) :
    ContinuousOn (kineticTimeDerivative u) D :=
  h.2.2.2.2.1

/- The kinetic position gradient is continuous on the specified set. -/
theorem continuousOn_kineticPositionGradient {d u}
    {D : Set (KineticPoint d)} (h : IsKineticC112On u D) :
    ContinuousOn (kineticPositionGradient u) D :=
  h.2.2.2.2.2.1

/- The kinetic velocity gradient is continuous on the specified set. -/
theorem continuousOn_kineticVelocityGradient {d u}
    {D : Set (KineticPoint d)} (h : IsKineticC112On u D) :
    ContinuousOn (kineticVelocityGradient u) D :=
  h.2.2.2.2.2.2.1

/- The kinetic velocity Hessian is continuous on the specified set. -/
theorem continuousOn_kineticVelocityHessian {d u}
    {D : Set (KineticPoint d)} (h : IsKineticC112On u D) :
    ContinuousOn (kineticVelocityHessian u) D :=
  h.2.2.2.2.2.2.2

/- The fixed-position-and-velocity time slice has its kinetic time derivative. -/
theorem timeSlice_hasDerivAt {d u D} (h : IsKineticC112On u D) {z : KineticPoint d}
    (hz : z ∈ D) :
    HasDerivAt (fun r => u ⟨r, z.position, z.velocity⟩) (kineticTimeDerivative u z)
      z.time :=  (h.timeSlice_differentiableAt hz).hasDerivAt

end IsKineticC112On

/- The plus-sign kinetic product operator `∂ᵣ + v · ∇ₓ + A : D²ᵥ`. -/
end HypoellipticAleksandrov.Parabolic
