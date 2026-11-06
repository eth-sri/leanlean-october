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

abbrev Covariate (d : ℕ) := EuclideanSpace ℝ (Fin d)

def cube (d : ℕ) : Set (Covariate d) := {x | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1}

def cubeVolume (d : ℕ) : Measure (Covariate d) := volume.restrict (cube d)

def holderOrder (t : ℝ) : ℕ := Nat.ceil t - 1

def holderExponent (t : ℝ) : ℝ := t - holderOrder t

def coordinateDerivative {d : ℕ} (f : Covariate d → ℝ) (q : ℕ)
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

def holderBall {d : ℕ} (t H : ℝ) : Set (Covariate d → ℝ) :=
  {f | holderNorm f t ≤ ENNReal.ofReal H}

structure Parameters where
  d : ℕ
  α : ℝ
  β : ℝ
  H : ℝ
  δ : ℝ
  gminus : ℝ
  gplus : ℝ
  M0 : ℝ
  hd : 1 ≤ d
  hα : 0 < α
  hβ : 0 < β
  hH : 0 < H
  hδ : 0 < δ
  hgminus : 0 < gminus
  hgplus : gminus < gplus
  hM0 : 0 < M0

def Parameters.theta (A : Parameters) : ℝ := (A.α + A.β) / A.d

structure Observables (Z : Type*) [MeasurableSpace Z] (A : Parameters) where
  D : Z → ℝ
  U : Z → ℝ
  V : Z → ℝ
  W : Z → ℝ
  lam : ℝ
  hlam : lam ≠ 0
  measurableD : Measurable D
  measurableU : Measurable U
  measurableV : Measurable V
  measurableW : Measurable W
  boundD : ∀ z, 0 ≤ D z ∧ D z ≤ A.M0
  boundU : ∀ z, |U z| ≤ A.M0
  boundV : ∀ z, |V z| ≤ A.M0
  boundW : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |W z| ≤ C

abbrev Observation (A : Parameters) (Z : Type*) := Covariate A.d × Z

abbrev covariateInformation (A : Parameters) (Z : Type*) [MeasurableSpace Z] :
    MeasurableSpace (Observation A Z) := MeasurableSpace.comap Prod.fst inferInstance

/-- A witness consists of the density and versions of the conditional ratios. -/
structure ModelWitness (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) where
  p : Covariate A.d → ℝ
  w : Covariate A.d → ℝ
  a : Covariate A.d → ℝ
  b : Covariate A.d → ℝ
  measurableP : Measurable p
  measurableW : Measurable w
  measurableA : Measurable a
  measurableB : Measurable b
  nonnegativeP : 0 ≤ᵐ[cubeVolume A.d] p
  marginal : (P : Measure (Observation A Z)).map Prod.fst =
    (cubeVolume A.d).withDensity (fun x ↦ ENNReal.ofReal (p x))
  momentD : (P : Measure (Observation A Z))[F.D ∘ Prod.snd | covariateInformation A Z] =ᵐ[(P : Measure (Observation A Z))]
    w ∘ Prod.fst
  momentU : (P : Measure (Observation A Z))[F.U ∘ Prod.snd | covariateInformation A Z] =ᵐ[(P : Measure (Observation A Z))]
    fun o ↦ w o.1 * a o.1
  momentV : (P : Measure (Observation A Z))[F.V ∘ Prod.snd | covariateInformation A Z] =ᵐ[(P : Measure (Observation A Z))]
    fun o ↦ w o.1 * b o.1
  overlap : ∀ᵐ x ∂cubeVolume A.d, A.δ ≤ w x
  smoothA : a ∈ holderBall A.α A.H
  smoothB : b ∈ holderBall A.β A.H
  densityBounds : ∀ᵐ x ∂cubeVolume A.d,
    A.gminus ≤ w x * p x ∧ w x * p x ≤ A.gplus

end RoughRegime.Model
