module

public import Mathlib
public import RoughRegime.Rates

@[expose] public section

/-!
# The statistical model and main theorem statement

This module provides a model encoding on actual probability measures, with
Lebesgue random design, conditional expectations, coordinate derivatives,
and measurable randomized estimators. `PerModelUpperClaim`, `UniformUpperClaim`,
and `MainLowerClaim` record statements. `ModelUpper.lean` proves the uniform
upper bound with actual estimators. `ModelLower.lean` proves both lower
regimes from the original nondegeneracy condition, including the probability bound.

Coordinate derivatives are encoded by ordered lists of coordinate directions.
`MultiIndexHolder.lean` proves its exact equivalence to the paper's maximum
over classical multi-indices on the closed cube, using derivative symmetry
and boundary uniqueness. `KernelSeedBridge.lean` proves the representation of every real-output
randomized estimator by a uniform random seed, with equality of minimax risks.
`RiskBridge.lean` proves
the exact RMSE/squared-integral equivalence for the encoded experiment.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RoughRegime.Model

section
variable (d : ℕ)
include d

abbrev Covariate  := EuclideanSpace ℝ (Fin d)

def cube  : Set (Covariate d) := {x | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1}


end


def holderOrder (t : ℝ)  := Nat.ceil t - 1

def holderExponent t  := t - holderOrder t

section
variable {d : ℕ}

section
variable (f : Covariate d → ℝ)
include f

def coordinateDerivative   q
    (σ : Fin q → Fin d) x  :=
  iteratedFDerivWithin ℝ q f (cube d) x (fun j ↦ EuclideanSpace.single (σ j) 1)

def derivativeSup   k  :=
  ⨆ (q : ℕ) (_ : q ≤ k) (σ : Fin q → Fin d) (x : Covariate d) (_ : x ∈ cube d),
    ENNReal.ofReal |coordinateDerivative f q σ x|

def holderSeminorm   t  :=
  ⨆ (σ : Fin (holderOrder t) → Fin d) (x : Covariate d) (_ : x ∈ cube d)
    (y : Covariate d) (_ : y ∈ cube d) (_ : x ≠ y),
    ENNReal.ofReal (|coordinateDerivative f (holderOrder t) σ x -
      coordinateDerivative f (holderOrder t) σ y| / ‖x - y‖ ^ holderExponent t)

def holderNorm   (t : ℝ) : ℝ≥0∞ := by
  classical
  exact if 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) then
    derivativeSup f (holderOrder t) + holderSeminorm f t else ∞
end


def holderBall  (t H : ℝ) : Set (Covariate d → ℝ) :=
  {f | holderNorm f t ≤ ENNReal.ofReal H}
end








section
variable (A : Parameters) (Z : Type*)
include A Z




end




end RoughRegime.Model
