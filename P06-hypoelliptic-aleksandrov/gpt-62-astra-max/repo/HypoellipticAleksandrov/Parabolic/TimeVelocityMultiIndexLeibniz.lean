module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Data.Nat.Choose.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Time--velocity multi-index derivatives

This file evaluates finite iterated Fréchet derivatives in the time--velocity
coordinate directions and proves their exact coordinatewise Leibniz formula.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex

open scoped BigOperators

variable {d : ℕ}

/-- The coordinate multiset of a multi-index, represented by the fixed `Finset.univ.toList`
coordinate order and repeated according to multiplicity. -/
def coordinateList (beta : TimeVelocityMultiIndex d) : List (TimeVelocityCoord d) :=
  (Finset.univ.toList).flatMap fun c => List.replicate (beta c) c

/-- The classical coordinate derivative associated to `beta`, implemented by evaluating the
actual iterated Fréchet derivative on its fixed coordinate list. -/
def coordinateIteratedFDeriv (beta : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  iteratedFDeriv ℝ beta.coordinateList.length f z fun i =>
    timeVelocityBasis (beta.coordinateList.get i)

/-- The zero multi-index has no coordinate directions. -/
@[simp] theorem coordinateList_zero (d : ℕ) :
    coordinateList (0 : TimeVelocityMultiIndex d) = [] := by
  simp [coordinateList]

section
variable (beta : TimeVelocityMultiIndex d)

/-- The coordinate list has length equal to the total differential order. -/
@[simp] theorem length_coordinateList :
    beta.coordinateList.length = beta.order := by
  simp [coordinateList, TimeVelocityMultiIndex.order,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
    VelocityMultiIndex.order, timeCoord, velocityCoord]

end

/-- Total differential order is additive. -/
@[simp] theorem order_add (beta gamma : TimeVelocityMultiIndex d) :
    (beta + gamma).order = beta.order + gamma.order := by
  simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
    TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order,
    Finset.sum_add_distrib]
  omega

/-- A single coordinate derivative has total order one. -/
@[simp] theorem order_single (c : TimeVelocityCoord d) :
    TimeVelocityMultiIndex.order (Pi.single c 1 : TimeVelocityMultiIndex d) = 1 := by
  cases c with
  | inl u => cases u; simp [TimeVelocityMultiIndex.order,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
      VelocityMultiIndex.order, timeCoord, velocityCoord]
  | inr i =>
      change 0 + ∑ x,
        (Pi.single (Sum.inr i) 1 : TimeVelocityMultiIndex d) (Sum.inr x) = 1
      rw [zero_add, Finset.sum_eq_single i]
      · simp
      · grind
      · grind

section
variable (beta : TimeVelocityMultiIndex d) (c : TimeVelocityCoord d) (f : TimeVelocity d → ℝ)
    (z : TimeVelocity d)

/-- The coordinate derivative of order zero is evaluation of the function. -/
@[simp] theorem coordinateIteratedFDeriv_zero :
    coordinateIteratedFDeriv 0 f z = f z := by
  unfold coordinateIteratedFDeriv
  rw [coordinateList_zero]
  apply iteratedFDeriv_zero_apply

end

end HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex
