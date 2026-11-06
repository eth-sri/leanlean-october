module

public import Mathlib

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RoughRegime.Model

abbrev Covariate (d : ℕ) := EuclideanSpace ℝ (Fin d)

def cube (d ) : Set (Covariate d) := {x | ∀ j, x j ∈ Set.Icc 0 1}

def holderOrder (t : ℝ) : ℕ := Nat.ceil t - 1

def holderExponent (t : ℝ) : ℝ := t - holderOrder t

def coordinateDerivative  (f : Covariate d → ℝ) (q )
    (σ : Fin q → Fin d) (x : Covariate d) : ℝ :=
  iteratedFDerivWithin ℝ q f (cube d) x (fun j ↦ EuclideanSpace.single (σ j) 1)

def derivativeSup {d : ℕ} (f : Covariate d → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (q : ℕ) (_ : q ≤ k) (σ : Fin q → Fin d) (x : Covariate d) (_ : x ∈ cube d),
    ENNReal.ofReal |coordinateDerivative f q σ x|

def holderSeminorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (σ : Fin (holderOrder t) → Fin d) (x : Covariate d) (_ : x ∈ cube d)
    (y : Covariate d) (_ : y ∈ cube d) (_ : x ≠ y),
    ENNReal.ofReal (|coordinateDerivative f (holderOrder t) σ x -
      coordinateDerivative f (holderOrder t) σ y| / ‖x - y‖ ^ holderExponent t)

def holderNorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) : ℝ≥0∞ := by
  classical
  exact if 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) then
    derivativeSup f (holderOrder t) + holderSeminorm f t else ∞

def holderBall  (t H : ℝ) : Set (Covariate d → ℝ) :=
  {f | holderNorm f t ≤ ENNReal.ofReal H}
end RoughRegime.Model
