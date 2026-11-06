module
public import Mathlib.Tactic

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Darboux
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

namespace OAI
open Set

namespace Problem337

/-- Telescoping a two-sided bound for adjacent increments. -/
theorem discrete_increment_bounds (d : ℕ → ℝ) (a b : ℕ)  L U 
    (hab : a ≤ b)
    (hstep : ∀ j ∈ Finset.Ico a b, L ≤ d (j + 1) - d j ∧ d (j + 1) - d j ≤ U) :
    L * ((b : ℝ) - a) ≤ d b - d a ∧ d b - d a ≤ U * ((b : ℝ) - a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hprev : ∀ j ∈ Finset.Ico a b, L ≤ d (j + 1) - d j ∧ d (j + 1) - d j ≤ U := by
      grind
    grind

/-- Darboux's theorem makes the sign of a nonvanishing second derivative
constant. Absolute derivative bounds therefore give one uniform signed strip. -/
theorem second_derivative_signed_bounds (f' f'' : ℝ → ℝ) (s : Set ℝ)
    (hs : Convex ℝ s)  L U  (hL : 0 < L)
    (hf' : ∀ x ∈ s, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ s, L ≤ |f'' x| ∧ |f'' x| ≤ U) :
    (∀ x ∈ s, L ≤ f'' x ∧ f'' x ≤ U) ∨
      (∀ x ∈ s, -U ≤ f'' x ∧ f'' x ≤ -L) := by
  have hn : ∀ x ∈ s, f'' x ≠ 0 := by
    grind
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne hs
      (fun x hx => (hf' x hx).hasDerivWithinAt) hn with hneg | hpos
  · grind
  grind

end Problem337

end OAI
