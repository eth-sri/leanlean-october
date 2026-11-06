module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import PDEFoundation.Ambient.Basis
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega



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

variable {d : ℕ}

/-- The velocity coordinate associated to `i`. -/
def velocityCoord  (i : Fin d) : TimeVelocityCoord d :=
  Sum.inr i

/-- The literal coordinate basis vector in `TimeVelocity d`. -/
def timeVelocityBasis  : TimeVelocityCoord d → TimeVelocity d
  | Sum.inl _ => (1, 0)
  | Sum.inr i => (0, PDE.basisVec i)

/-- A velocity multi-index. -/
abbrev VelocityMultiIndex (d : ℕ) := Fin d → ℕ

/-- Total order of a velocity multi-index. -/
def VelocityMultiIndex.order (alpha : VelocityMultiIndex d) : ℕ :=
  ∑ i, alpha i

/-- An ordinary multi-index in all time--velocity coordinates. -/
abbrev TimeVelocityMultiIndex (d : ℕ) := TimeVelocityCoord d → ℕ

variable (beta : TimeVelocityMultiIndex d)

/-- Time order of an ordinary time--velocity multi-index. -/
def TimeVelocityMultiIndex.timeOrder
     : ℕ :=
  beta (timeCoord d)

/-- Velocity restriction of an ordinary time--velocity multi-index. -/
def TimeVelocityMultiIndex.velocity
     : VelocityMultiIndex d :=
  fun i => beta (velocityCoord i)

/-- Assemble an ordinary multi-index from its time and velocity orders. -/
def TimeVelocityMultiIndex.ofTimeVelocity
    (q : ℕ) (alpha : VelocityMultiIndex d) : TimeVelocityMultiIndex d
  | Sum.inl _ => q
  | Sum.inr i => alpha i

/-- Total ordinary order of a time--velocity multi-index. -/
def TimeVelocityMultiIndex.order
    (beta : TimeVelocityMultiIndex d) : ℕ :=
  beta.timeOrder + beta.velocity.order

/-- The numerical parabolic weight `2q + |alpha|`. -/
def VelocityMultiIndex.parabolicWeight
    (q : ℕ) (alpha : VelocityMultiIndex d) : ℕ :=
  2 * q + alpha.order

/-- Parabolic weight of an ordinary time--velocity multi-index. -/
def TimeVelocityMultiIndex.parabolicWeight
    (beta : TimeVelocityMultiIndex d) : ℕ :=
  beta.velocity.parabolicWeight beta.timeOrder

@[simp] theorem timeVelocityBasis_time (d : ℕ) :
    timeVelocityBasis (timeCoord d) = ((1, 0) : TimeVelocity d) :=
  rfl

@[simp] theorem timeVelocityBasis_velocity {d : ℕ} (i : Fin d) :
    timeVelocityBasis (velocityCoord i) =
      ((0, PDE.basisVec i) : TimeVelocity d) :=
  rfl

variable (q : ℕ) (alpha : VelocityMultiIndex d)

@[simp] theorem TimeVelocityMultiIndex.timeOrder_ofTimeVelocity
     :
    (ofTimeVelocity q alpha).timeOrder = q :=
  rfl

@[simp] theorem TimeVelocityMultiIndex.velocity_ofTimeVelocity
     :
    (ofTimeVelocity q alpha).velocity = alpha :=
  rfl

@[simp] theorem
    TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity
    (beta : TimeVelocityMultiIndex d) :
    ofTimeVelocity beta.timeOrder beta.velocity = beta := by
  funext i
  cases i <;> rfl

variable (q : ℕ) (alpha : VelocityMultiIndex d)



@[simp] theorem TimeVelocityMultiIndex.parabolicWeight_ofTimeVelocity
     :
    (ofTimeVelocity q alpha).parabolicWeight = alpha.parabolicWeight q :=
  rfl

theorem VelocityMultiIndex.parabolicWeight_le_two_mul_order
     :
    alpha.parabolicWeight q ≤ 2 * (q + alpha.order) := by
  unfold VelocityMultiIndex.parabolicWeight
  omega

theorem TimeVelocityMultiIndex.parabolicWeight_le_two_mul_order
    (beta : TimeVelocityMultiIndex d) :
    beta.parabolicWeight ≤ 2 * beta.order := VelocityMultiIndex.parabolicWeight_le_two_mul_order
    beta.timeOrder beta.velocity

theorem TimeVelocityMultiIndex.parabolicWeight_le_two_mul
    {beta : TimeVelocityMultiIndex d} {m : ℕ}
    (hbeta : beta.order ≤ m) :
    beta.parabolicWeight ≤ 2 * m :=
  beta.parabolicWeight_le_two_mul_order.trans (Nat.mul_le_mul_left 2 hbeta)

/-- Ordinary time--velocity multi-indices of total order at most `m`. -/
abbrev TimeVelocityDerivativeIndex (d m : ℕ) :=
  {beta : TimeVelocityMultiIndex d // beta.order ≤ m}

/-- The zero multi-index at any finite order bound. -/
def TimeVelocityDerivativeIndex.zero (d m : ℕ) :
    TimeVelocityDerivativeIndex d m :=
  ⟨0, by
    simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
      TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order]⟩

/-- Enlarge the order bound on an ordinary derivative index. -/
def TimeVelocityDerivativeIndex.castLE
    {d m n : ℕ} (hmn : m ≤ n)
    (beta : TimeVelocityDerivativeIndex d m) :
    TimeVelocityDerivativeIndex d n :=
  ⟨beta.1, beta.2.trans hmn⟩

end HypoellipticAleksandrov.Parabolic
