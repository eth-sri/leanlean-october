module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeSpacetimeTest
public import HypoellipticAleksandrov.Parabolic.Derivatives

/-!
# Finite separated spacetime tests

This module packages finite sums of smooth separated time--space tests and
identifies their literal time derivative.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/- A finite sum of smooth separated time--space tests. -/
structure FiniteSeparatedSpacetimeTest
    {d : ℕ} (τ₁ τ₂ : ℝ) (O : Set (PDE.Vec d)) where
  termCount : ℕ
  timeFactor : Fin termCount → OriginalTimeScalarTest τ₁ τ₂
  spatialFactor : Fin termCount → PDE.WeakTestFunction O

/- The raw spacetime function represented by a finite separated test. -/
noncomputable def FiniteSeparatedSpacetimeTest.toFun
    {d : ℕ} {τ₁ τ₂ : ℝ} {O : Set (PDE.Vec d)}
    (q : FiniteSeparatedSpacetimeTest τ₁ τ₂ O) :
    TimeVelocity d → ℝ :=
  fun z => ∑ m : Fin q.termCount,
    q.timeFactor m z.1 * q.spatialFactor m z.2

/- The literal time derivative of a finite separated test. -/
noncomputable def FiniteSeparatedSpacetimeTest.timeDeriv
    {d : ℕ} {τ₁ τ₂ : ℝ} {O : Set (PDE.Vec d)}
    (q : FiniteSeparatedSpacetimeTest τ₁ τ₂ O) :
    TimeVelocity d → ℝ :=
  fun z => ∑ m : Fin q.termCount,
    (q.timeFactor m).deriv z.1 * q.spatialFactor m z.2

/- The time derivative of a finite separated test differentiates only its time factors. -/
end HypoellipticAleksandrov.Parabolic.Dirichlet
