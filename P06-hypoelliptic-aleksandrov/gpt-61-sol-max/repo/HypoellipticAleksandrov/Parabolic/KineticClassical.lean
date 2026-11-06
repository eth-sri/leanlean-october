module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import HypoellipticAleksandrov.Ambient.MatrixContraction
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Geometry.KineticPoint
public import PDEFoundation.Sobolev.ClassicalGradient
import Aesop



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



variable {d : ℕ}



/-- The terminal face `{r₁} × (closure Ωx × closure Ωv)`. -/
def kineticProductTerminalFace  (r₁ : ℝ) (Ωx Ωv : PDE.VelocityRegion d) :
    Set (KineticPoint d) :=
  (KineticPoint.homeomorphProd d) ⁻¹'
    (({r₁} : Set ℝ) ×ˢ (closure Ωx ×ˢ closure Ωv))

variable (r₀ r₁ : ℝ) (Ωx Ωv : PDE.VelocityRegion d)

/-- The spatial lateral face `[r₀, r₁] × (frontier Ωx × closure Ωv)`. -/
def kineticProductSpatialLateralFace   :
    Set (KineticPoint d) :=
  (KineticPoint.homeomorphProd d) ⁻¹'
    (Set.Icc r₀ r₁ ×ˢ (frontier Ωx ×ˢ closure Ωv))

/-- The velocity lateral face `[r₀, r₁] × (closure Ωx × frontier Ωv)`. -/
def kineticProductVelocityLateralFace   :
    Set (KineticPoint d) :=
  (KineticPoint.homeomorphProd d) ⁻¹'
    (Set.Icc r₀ r₁ ×ˢ (closure Ωx ×ˢ frontier Ωv))



variable {r₀ r₁ : ℝ} {Ωx Ωv : PDE.VelocityRegion d} {z : KineticPoint d}





/-- Membership in the terminal face of a kinetic product cylinder. -/
@[simp] theorem mem_kineticProductTerminalFace_iff  {r₁ : ℝ}
    {Ωx Ωv : PDE.VelocityRegion d} {z : KineticPoint d} :
    z ∈ kineticProductTerminalFace r₁ Ωx Ωv ↔
      z.time = r₁ ∧ z.position ∈ closure Ωx ∧ z.velocity ∈ closure Ωv := by
  rfl

variable {r₀ r₁ : ℝ} {Ωx Ωv : PDE.VelocityRegion d} {z : KineticPoint d}

/-- Membership in the spatial lateral face of a kinetic product cylinder. -/
@[simp] theorem mem_kineticProductSpatialLateralFace_iff   :
    z ∈ kineticProductSpatialLateralFace r₀ r₁ Ωx Ωv ↔
      r₀ ≤ z.time ∧ z.time ≤ r₁ ∧ z.position ∈ frontier Ωx ∧ z.velocity ∈ closure Ωv := by
  change (z.time, (z.position, z.velocity)) ∈
    Set.Icc r₀ r₁ ×ˢ (frontier Ωx ×ˢ closure Ωv) ↔ _
  aesop

/-- Membership in the velocity lateral face of a kinetic product cylinder. -/
@[simp] theorem mem_kineticProductVelocityLateralFace_iff   :
    z ∈ kineticProductVelocityLateralFace r₀ r₁ Ωx Ωv ↔
      r₀ ≤ z.time ∧ z.time ≤ r₁ ∧ z.position ∈ closure Ωx ∧ z.velocity ∈ frontier Ωv := by
  change (z.time, (z.position, z.velocity)) ∈
    Set.Icc r₀ r₁ ×ˢ (closure Ωx ×ˢ frontier Ωv) ↔ _
  aesop



variable (u : HypoellipticAleksandrov.KineticScalarField d)

variable (z : KineticPoint d)

/-- The time derivative with position and velocity held fixed. -/
def kineticTimeDerivative    : ℝ :=
  deriv (fun r => u ⟨r, z.position, z.velocity⟩) z.time

/-- The position gradient with time and velocity held fixed. -/
def kineticPositionGradient    :
    PDE.Vec d :=
  PDE.classicalGradient (fun x => u ⟨z.time, x, z.velocity⟩) z.position

/-- The velocity gradient with time and position held fixed. -/
def kineticVelocityGradient    :
    PDE.Vec d :=
  PDE.classicalGradient (fun v => u ⟨z.time, z.position, v⟩) z.velocity

/-- The velocity Hessian indexed as `D_i(D_j u)`. -/
def kineticVelocityHessian    :
    PDE.Mat d :=
  fun i j =>
    (fderiv ℝ ((PDE.classicalGradient (fun w : PDE.Vec d => u ⟨z.time, z.position, w⟩)))
      z.velocity (PDE.basisVec i)) j

/--
The anisotropic kinetic `C^{1,1,2}` regularity predicate. It asks only for
one time, one position, and two velocity derivatives on separate slices.
-/
def IsKineticC112On   (D : Set (KineticPoint d)) : Prop :=
  ContinuousOn u D ∧
    (∀ z ∈ D, DifferentiableAt ℝ (fun r => u ⟨r, z.position, z.velocity⟩) z.time) ∧
    (∀ z ∈ D, ContDiffAt ℝ 1 (fun x => u ⟨z.time, x, z.velocity⟩) z.position) ∧
    (∀ z ∈ D, ContDiffAt ℝ 2 (fun v => u ⟨z.time, z.position, v⟩) z.velocity) ∧
    ContinuousOn (kineticTimeDerivative u) D ∧
    ContinuousOn (kineticPositionGradient u) D ∧
    ContinuousOn (kineticVelocityGradient u) D ∧
    ContinuousOn (kineticVelocityHessian u) D

namespace IsKineticC112On

/-- The function itself is continuous on the specified set. -/
theorem continuousOn {d : ℕ} {u : HypoellipticAleksandrov.KineticScalarField d} {D : Set (KineticPoint d)}
    (h : IsKineticC112On u D) : ContinuousOn u D :=
  h.1

variable {d : ℕ} {u : HypoellipticAleksandrov.KineticScalarField d} {D : Set (KineticPoint d)} (h : IsKineticC112On u D)

section
variable {z : KineticPoint d} (hz : z ∈ D)

include h hz
/-- Each fixed-position-and-velocity time slice is differentiable on the set. -/
theorem timeSlice_differentiableAt   : type_of% (h.2.1 z hz) :=
  h.2.1 z hz

/-- Each fixed-time-and-velocity position slice is `C¹` on the set. -/
theorem positionSlice_contDiffAt   : type_of% (h.2.2.1 z hz) :=
  h.2.2.1 z hz

/-- Each fixed-time-and-position velocity slice is `C²` on the set. -/
theorem velocitySlice_contDiffAt   :
    ContDiffAt ℝ 2 (fun v => u ⟨z.time, z.position, v⟩) z.velocity :=
  h.2.2.2.1 z hz
end


include h in
/-- The kinetic time derivative is continuous on the specified set. -/
theorem continuousOn_kineticTimeDerivative  :
    ContinuousOn (kineticTimeDerivative u) D :=
  h.2.2.2.2.1

include h in
/-- The kinetic position gradient is continuous on the specified set. -/
theorem continuousOn_kineticPositionGradient  :
    ContinuousOn (kineticPositionGradient u) D :=
  h.2.2.2.2.2.1

include h in
/-- The kinetic velocity gradient is continuous on the specified set. -/
theorem continuousOn_kineticVelocityGradient  :
    ContinuousOn (kineticVelocityGradient u) D :=
  h.2.2.2.2.2.2.1

include h in
/-- The kinetic velocity Hessian is continuous on the specified set. -/
theorem continuousOn_kineticVelocityHessian  :
    ContinuousOn (kineticVelocityHessian u) D :=
  h.2.2.2.2.2.2.2

include h in
/-- The fixed-position-and-velocity time slice has its kinetic time derivative. -/
theorem timeSlice_hasDerivAt  {z : KineticPoint d}
    (hz : z ∈ D) :
    HasDerivAt (fun r => u ⟨r, z.position, z.velocity⟩) (kineticTimeDerivative u z)
      z.time := (h.timeSlice_differentiableAt hz).hasDerivAt

end IsKineticC112On





end HypoellipticAleksandrov.Parabolic
