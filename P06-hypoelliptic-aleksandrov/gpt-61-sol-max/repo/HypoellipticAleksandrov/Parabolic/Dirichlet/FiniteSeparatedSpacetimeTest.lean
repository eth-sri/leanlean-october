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

/-- A finite sum of smooth separated time--space tests. -/
structure FiniteSeparatedSpacetimeTest
    {d : ℕ} (τ₁ τ₂ : ℝ) (O : PDE.VelocityRegion d) where
  termCount : ℕ
  timeFactor : Fin termCount → OriginalTimeScalarTest τ₁ τ₂
  spatialFactor : Fin termCount → PDE.WeakTestFunction O

variable {d : ℕ} {τ₁ τ₂ : ℝ} {O : PDE.VelocityRegion d} (q : FiniteSeparatedSpacetimeTest τ₁ τ₂ O)

/-- The raw spacetime function represented by a finite separated test. -/
def FiniteSeparatedSpacetimeTest.toFun
     :
    HypoellipticAleksandrov.Parabolic.ScalarField d :=
  fun z => ∑ m : Fin q.termCount,
    q.timeFactor m z.1 * q.spatialFactor m z.2

/-- The literal time derivative of a finite separated test. -/
def FiniteSeparatedSpacetimeTest.timeDeriv
     :
    HypoellipticAleksandrov.Parabolic.ScalarField d :=
  fun z => ∑ m : Fin q.termCount,
    (q.timeFactor m).deriv z.1 * q.spatialFactor m z.2



end HypoellipticAleksandrov.Parabolic.Dirichlet
