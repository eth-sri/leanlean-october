module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import PDEFoundation.Ambient.Basis
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Ordinary multi-indices on time--velocity space

This module provides the finite coordinate and order arithmetic shared by the
later parabolic-weight and ordinary Sobolev derivative carriers.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators

variable {d : ℕ}

/-- The distinguished time coordinate followed by the velocity coordinates. -/
abbrev TimeVelocityCoord (d : ℕ) := Unit ⊕ Fin d

/-- The distinguished time coordinate. -/
def timeCoord (d : ℕ) : TimeVelocityCoord d :=
  Sum.inl ()

/-- The velocity coordinate associated to `i`. -/
def velocityCoord {d : ℕ} (i : Fin d) : TimeVelocityCoord d :=
  Sum.inr i

/-- The literal coordinate basis vector in `TimeVelocity d`. -/
def timeVelocityBasis {d : ℕ} : TimeVelocityCoord d → TimeVelocity d
  | Sum.inl _ => (1, 0)
  | Sum.inr i => (0, PDE.basisVec i)

/-- A velocity multi-index. -/
abbrev VelocityMultiIndex (d : ℕ) := Fin d → ℕ

/-- Total order of a velocity multi-index. -/
def VelocityMultiIndex.order (alpha : VelocityMultiIndex d) : ℕ :=
  ∑ i, alpha i

/-- An ordinary multi-index in all time--velocity coordinates. -/
abbrev TimeVelocityMultiIndex (d : ℕ) := TimeVelocityCoord d → ℕ

/-- Time order of an ordinary time--velocity multi-index. -/
def TimeVelocityMultiIndex.timeOrder
    (beta : TimeVelocityMultiIndex d) : ℕ :=
  beta (timeCoord d)

/-- Velocity restriction of an ordinary time--velocity multi-index. -/
def TimeVelocityMultiIndex.velocity
    (beta : TimeVelocityMultiIndex d) : VelocityMultiIndex d :=
  fun i => beta (velocityCoord i)

/-- Total ordinary order of a time--velocity multi-index. -/
def TimeVelocityMultiIndex.order
    (beta : TimeVelocityMultiIndex d) : ℕ :=
  beta.timeOrder + beta.velocity.order

@[simp] theorem timeVelocityBasis_time (d : ℕ) :
    timeVelocityBasis (timeCoord d) = ((1, 0) : TimeVelocity d) :=
  rfl

@[simp] theorem timeVelocityBasis_velocity {d : ℕ} (i : Fin d) :
    timeVelocityBasis (velocityCoord i) =
      ((0, PDE.basisVec i) : TimeVelocity d) :=
  rfl

section
variable (q : ℕ) (beta : TimeVelocityMultiIndex d) (alpha : VelocityMultiIndex d)

end

end HypoellipticAleksandrov.Parabolic
