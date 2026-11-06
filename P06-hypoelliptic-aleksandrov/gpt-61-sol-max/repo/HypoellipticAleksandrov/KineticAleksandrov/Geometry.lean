module

public import HypoellipticAleksandrov.Geometry.KineticPoint
public import HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Basic
import Aesop



/-!
# Geometry for the kinetic Aleksandrov principle

This module records the source kinetic cylinders, their inflow boundary, the
kinetic affine map, the explicit Euclidean quasi-distance, and forward stacks.
The Euclidean geometry is supplied by `PDEFoundation`; the metric transported
to `KineticPoint` is used only for the topological closure in the boundary.
-/

@[expose] public section

set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set

variable {d : ℕ}

variable (P₀ P : KineticPoint d)

/-- Relative velocity of `P` with respect to the cylinder centre `P₀`. -/
def relativeVelocity   : PDE.Vec d :=
  P.velocity - P₀.velocity

/-- Relative position in free-transport coordinates based at `P₀`. -/
def relativePosition   : PDE.Vec d :=
  P.position - P₀.position - (P.time - P₀.time) • P₀.velocity

variable (P₀ : KineticPoint d)



@[simp] theorem relativePosition_self   :
    relativePosition P₀ P₀ = 0 := by
  simp [relativePosition]

/-- The open backward kinetic cylinder with time, velocity, and position
radii `R²`, `R`, and `R³`, respectively. -/
def backwardCylinder   (R : ℝ) :
    Set (KineticPoint d) :=
  {P | P₀.time - R ^ 2 < P.time ∧ P.time < P₀.time ∧
    P.velocity ∈ PDE.euclideanBall P₀.velocity R ∧
    relativePosition P₀ P ∈ PDE.euclideanBall (0 : PDE.Vec d) (R ^ 3)}

@[simp] theorem mem_backwardCylinder_iff
     {P₀ P : KineticPoint d} {R : ℝ} :
    P ∈ backwardCylinder P₀ R ↔
      P₀.time - R ^ 2 < P.time ∧ P.time < P₀.time ∧
        P.velocity ∈ PDE.euclideanBall P₀.velocity R ∧
        relativePosition P₀ P ∈ PDE.euclideanBall (0 : PDE.Vec d) (R ^ 3) := by
  rfl

/-- The source kinetic boundary: closure intersected with the bottom face,
velocity sphere, or the inflow part of the relative-position sphere. -/
def kineticBoundary  (P₀ : KineticPoint d) (R : ℝ) :
    Set (KineticPoint d) :=
  closure (backwardCylinder P₀ R) ∩
    ({P | P.time = P₀.time - R ^ 2} ∪
      {P | P.velocity ∈ PDE.euclideanSphere P₀.velocity R} ∪
      {P | relativePosition P₀ P ∈
          PDE.euclideanSphere (0 : PDE.Vec d) (R ^ 3) ∧
        PDE.vecDot (relativeVelocity P₀ P) (relativePosition P₀ P) ≤ 0})

@[simp] theorem mem_kineticBoundary_iff
     {P₀ P : KineticPoint d} {R : ℝ} :
    P ∈ kineticBoundary P₀ R ↔
      P ∈ closure (backwardCylinder P₀ R) ∧
        (P.time = P₀.time - R ^ 2 ∨
          P.velocity ∈ PDE.euclideanSphere P₀.velocity R ∨
          (relativePosition P₀ P ∈
              PDE.euclideanSphere (0 : PDE.Vec d) (R ^ 3) ∧
            PDE.vecDot (relativeVelocity P₀ P) (relativePosition P₀ P) ≤ 0)) := by
  simp_all [kineticBoundary] <;> aesop

variable (P₀ : KineticPoint d) (R : ℝ)

/-- Kinetic dilation of ratio `R` followed by Galilean translation by `P₀`. -/
def kineticAffine   :
    KineticPoint d → KineticPoint d :=
  fun P =>
    { time := P₀.time + R ^ 2 * P.time
      position := P₀.position + R ^ 3 • P.position +
        (R ^ 2 * P.time) • P₀.velocity
      velocity := P₀.velocity + R • P.velocity }

variable (P : KineticPoint d)

@[simp] theorem kineticAffine_time
       :
    (kineticAffine P₀ R P).time = P₀.time + R ^ 2 * P.time := by
  rfl

@[simp] theorem kineticAffine_position
       :
    (kineticAffine P₀ R P).position =
      P₀.position + R ^ 3 • P.position +
        (R ^ 2 * P.time) • P₀.velocity := by
  rfl

@[simp] theorem kineticAffine_velocity
       :
    (kineticAffine P₀ R P).velocity = P₀.velocity + R • P.velocity := by
  rfl



@[simp] theorem relativePosition_kineticAffine
       :
    relativePosition P₀ (kineticAffine P₀ R P) = R ^ 3 • P.position := by
  ext i
  simp [relativePosition, kineticAffine]
  ring

/-- The source kinetic quasi-distance, using explicit Euclidean vector norms. -/
noncomputable def quasiDistance  (P P' : KineticPoint d) : ℝ :=
  Real.sqrt |P.time - P'.time| +
    PDE.vecEuclideanNorm (P.velocity - P'.velocity) +
    Real.rpow
      (max
        (PDE.vecEuclideanNorm
          (P'.position - P.position - (P'.time - P.time) • P.velocity))
        (PDE.vecEuclideanNorm
          (P.position - P'.position - (P.time - P'.time) • P'.velocity)))
      (1 / 3 : ℝ)

/-- The forward stack of `backwardCylinder P₀ r` at natural height `m`. -/
def forwardStack  (P₀ : KineticPoint d) (r : ℝ) (m : ℕ) :
    Set (KineticPoint d) :=
  {P | 0 < P.time - P₀.time ∧
    P.time - P₀.time ≤ (m : ℝ) * r ^ 2 ∧
    P.velocity ∈ PDE.euclideanBall P₀.velocity r ∧
    relativePosition P₀ P ∈
      PDE.euclideanBall (0 : PDE.Vec d) (((m + 2 : ℕ) : ℝ) * r ^ 3)}

@[simp] theorem mem_forwardStack_iff
     {P₀ P : KineticPoint d} {r : ℝ} {m : ℕ} :
    P ∈ forwardStack P₀ r m ↔
      0 < P.time - P₀.time ∧
        P.time - P₀.time ≤ (m : ℝ) * r ^ 2 ∧
        P.velocity ∈ PDE.euclideanBall P₀.velocity r ∧
        relativePosition P₀ P ∈
          PDE.euclideanBall (0 : PDE.Vec d) (((m + 2 : ℕ) : ℝ) * r ^ 3) := by
  rfl

end HypoellipticAleksandrov.KineticAleksandrov
