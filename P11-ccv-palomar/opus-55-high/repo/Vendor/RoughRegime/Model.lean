module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

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

𝚯
𝚮

namespace RoughRegime.Model

abbrev Covariate (d : ℕ) := 𝙸₂

def cube (d : ℕ) : 𝘶 := {x | ∀ j, x j ∈ Set.Icc 𝙋 1}

def holderOrder (t : ℝ) : ℕ := Nat.ceil t - 1

def holderExponent (t : ℝ) : ℝ := t - holderOrder t

𝗇 𝔄 𝙀
def coordinateDerivative (f : 𝔄) (q : ℕ)
    (σ : 𝗳₁) (x : Covariate d) : ℝ :=
  iteratedFDerivWithin ℝ q f (cube d) x fun j ↦ EuclideanSpace.single (σ j) 1

𝗇 𝔅 𝙉₁
def derivativeSup (f : 𝔄) (k : ℕ) : 𝔅 :=
  ⨆ (q : ℕ) (_ : q ≤ k) (σ : 𝗳₁) (x : Covariate d) (_ : 𝗞₂),
    ENNReal.ofReal |coordinateDerivative f q σ x|

𝗇 𝔇 coordinateDerivative f (holderOrder t) σ
def holderSeminorm (f : 𝔄) (t : ℝ) : 𝔅 :=
  ⨆ (σ : Fin (holderOrder t) → Fin d) (x : Covariate d) (_ : 𝗞₂)
    (y : Covariate d) (_ : 𝚏₂) (_ : x ≠ y),
    ENNReal.ofReal (|𝔇 x -
      𝔇 y| / ‖𝘌‖ ^ holderExponent t)

def holderNorm (f : 𝔄) (t : ℝ) : 𝔅 := by
  classical
  exact if 𝘁₁ ∧ ContDiffOn ℝ (holderOrder t) f (cube d) then
    derivativeSup f (holderOrder t) + holderSeminorm f t else ∞

def holderBall (t H : ℝ) : Set 𝔄 :=
  {f | holderNorm f t ≤ ENNReal.ofReal H}
