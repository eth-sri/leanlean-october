module

public import Mathlib


@[expose] public section

/-!
The statistical model from §1.1 of the current manuscript.  In particular,
the minimax loss uses `lintegral`: an infinite second moment is not zero.
These are definitions, not a proof of the paper's minimax rate theorems.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace NearlyMinimax

abbrev Covariate d := Fin d → ℝ
abbrev Observation d := Covariate d × ℝ

def unitCube d : Set (Covariate d) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

section
variable {d : ℕ}

/-- The Euclidean norm, independently of the sup norm on the function type. -/
def euclideanNorm  (x : Covariate d)  :=
  Real.sqrt (∑ i, (x i) ^ 2)

def coordinatePartial  (i : Fin d) (F : Covariate d → ℝ) :
    Covariate d → ℝ := fun x => fderiv ℝ F x (Pi.single i 1)

/-- Ordered mixed partials; `ContDiffOn` on an open set supplies their usual meaning. -/
def multiPartial  F (γ : Fin d → ℕ)  :=
  ((List.finRange d).flatMap (fun i => List.replicate (γ i) i)).foldl
    (fun G i => coordinatePartial i G) F

section
variable (U : Set (Covariate d))
include U

def derivativeSup   (G : Covariate d → ℝ)  :=
  ⨆ x : U, ENNReal.ofReal |G x|

def holderSeminorm   (G : Covariate d → ℝ)
    (α : ℝ)  :=
  ⨆ x : U, ⨆ y : U, if (x : Covariate d) = y then 0 else
    ENNReal.ofReal (|G x - G y| / (euclideanNorm (x.val - y.val)) ^ α)

/-- Sum over distinct multi-indices, plus the maximum top-order seminorm. -/
def holderNorm   F
    ℓ α  :=
  (∑ γ : Fin d → Fin (ℓ + 1),
    if (∑ i, (γ i).val) ≤ ℓ then
      derivativeSup U (multiPartial F (fun i => (γ i).val)) else 0) +
  ⨆ γ : Fin d → Fin (ℓ + 1),
    if (∑ i, (γ i).val) = ℓ then
      holderSeminorm U (multiPartial F (fun i => (γ i).val)) α else 0
end

end


/-- The open extension domain and all fixed model constants. -/
structure ModelConstants (d : ℕ) where
  dimension_pos : 0 < d
  smoothness : ℝ
  order : ℕ
  smoothness_pos : 0 < smoothness
  order_lt : (order : ℝ) < smoothness
  smoothness_le_order_add_one : smoothness ≤ order + 1
  domain : Set (Covariate d)
  domain_open : IsOpen domain
  cube_subset : unitCube d ⊆ domain
  densityLower : ℝ
  densityUpper : ℝ
  densityLower_pos : 0 < densityLower
  densityLower_lt_one : densityLower < 1
  one_lt_densityUpper : 1 < densityUpper
  holderBound : ℝ
  holderBound_pos : 0 < holderBound
  varianceLower : ℝ
  varianceUpper : ℝ
  varianceLower_pos : 0 < varianceLower
  variance_interval : varianceLower < varianceUpper
  fourthBound : ℝ
  fourth_margin : varianceLower ^ 2 < fourthBound

def ModelConstants.alpha {d } (C : ModelConstants d)  :=
  C.smoothness - C.order

section
variable {d : ℕ} (C : ModelConstants d)

theorem ModelConstants.order_eq  :
    C.order = Nat.ceil C.smoothness - 1 := by
  have hc : Nat.ceil C.smoothness = C.order + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero C.order)).mpr
    simp_all [C.order_lt, C.smoothness_le_order_add_one]
  rw [hc, Nat.add_sub_cancel]

theorem ModelConstants.alpha_pos  : 0 < C.alpha := sub_pos.mpr C.order_lt

theorem ModelConstants.alpha_le_one  : C.alpha ≤ 1 := by
  dsimp [ModelConstants.alpha]
  linarith [C.smoothness_le_order_add_one]
end


/-- Kernels are defined on the ambient space; values outside the cube are irrelevant. -/
structure RegressionParameter (d : ℕ) where
  density : Covariate d → ℝ
  regression : Covariate d → ℝ
  variance : ℝ
  errors : Kernel (Covariate d) ℝ
  errors_markov : IsMarkovKernel errors

attribute [instance] RegressionParameter.errors_markov

def cubeVolume (d : ℕ) : Measure (Covariate d) :=
  volume.restrict (unitCube d)

section
variable {d : ℕ}

section
variable (θ : RegressionParameter d)
include θ

def designLaw   : Measure (Covariate d) :=
  (cubeVolume d).withDensity (fun x => ENNReal.ofReal (θ.density x))

def observationLaw   : Measure (Observation d) :=
  ((designLaw θ).compProd θ.errors).map
    (fun z => (z.1, θ.regression z.1 + z.2))

def sampleLaw   (n : ℕ) :
    Measure (Fin n → Observation d) := Measure.pi (fun _ => observationLaw θ)
end


/-- The fourth-moment and integrability constraints are on the error kernel,
not on a common error distribution independent of the covariate. -/
def Admissible  (C : ModelConstants d) (θ : RegressionParameter d) : Prop :=
  Measurable θ.density ∧ Measurable θ.regression ∧
  (∀ᵐ x ∂cubeVolume d, C.densityLower ≤ θ.density x ∧ θ.density x ≤ C.densityUpper) ∧
  (∫⁻ x, ENNReal.ofReal (θ.density x) ∂cubeVolume d) = 1 ∧
  (∃ F : Covariate d → ℝ,
    (∀ x ∈ unitCube d, F x = θ.regression x) ∧
    ContDiffOn ℝ C.order F C.domain ∧
    holderNorm C.domain F C.order C.alpha ≤ ENNReal.ofReal C.holderBound) ∧
  C.varianceLower ≤ θ.variance ∧ θ.variance ≤ C.varianceUpper ∧
  (∀ᵐ x ∂designLaw θ,
    Integrable (fun u : ℝ => u) (θ.errors x) ∧
    Integrable (fun u : ℝ => u ^ 2) (θ.errors x) ∧
    Integrable (fun u : ℝ => u ^ 4) (θ.errors x) ∧
    (∫ u : ℝ, u ∂θ.errors x) = 0 ∧
    (∫ u : ℝ, u ^ 2 ∂θ.errors x) = θ.variance ∧
    (∫ u : ℝ, u ^ 4 ∂θ.errors x) ≤ C.fourthBound)
end


abbrev Estimator d n :=
  {T : (Fin n → Observation d) → ℝ // Measurable T}

def meanSquaredRisk {d n } (T : Estimator d n) θ  :=
  ∫⁻ z, ENNReal.ofReal ((T.val z - θ.variance) ^ 2) ∂sampleLaw θ n

def worstCaseRisk {d n } C (T : Estimator d n)  :=
  ⨆ θ : {θ : RegressionParameter d // Admissible C θ}, meanSquaredRisk T θ.val

def minimaxRisk {d } C n  :=
  ⨅ T : Estimator d n, worstCaseRisk C T

def minimaxRMS {d } (C : ModelConstants d) n  :=
  (minimaxRisk C n) ^ (1 / 2 : ℝ)

section
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
include hθ

theorem designLaw_isProbability  :
    IsProbabilityMeasure (designLaw θ) := by
  refine ⟨?_⟩
  simpa [designLaw, withDensity_apply] using hθ.2.2.2.1

theorem observationLaw_isProbability  :
    IsProbabilityMeasure (observationLaw θ) := by
  letI := designLaw_isProbability C θ hθ
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)).aemeasurable).mpr
      inferInstance

theorem sampleLaw_isProbability  n :
    IsProbabilityMeasure (sampleLaw θ n) := by
  letI := observationLaw_isProbability C θ hθ
  exact inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => observationLaw θ)))
end


def constantEstimator (d n : ℕ) (v : ℝ) : Estimator d n :=
  ⟨fun _ => v, measurable_const⟩

section
variable {d n : ℕ} (C : ModelConstants d)

theorem constantEstimator_risk_bound 
    θ (hθ : Admissible C θ) :
    meanSquaredRisk (constantEstimator d n C.varianceLower) θ ≤
      ENNReal.ofReal ((C.varianceUpper - C.varianceLower) ^ 2) := by
  letI := sampleLaw_isProbability C θ hθ n
  obtain ⟨_, _, _, _, _, hlo, hhi, _⟩ := hθ
  have hs : (C.varianceLower - θ.variance) ^ 2 ≤
      (C.varianceUpper - C.varianceLower) ^ 2 := by
    nlinarith
  unfold meanSquaredRisk constantEstimator
  simp only [lintegral_const, measure_univ, mul_one]
  exact ENNReal.ofReal_le_ofReal hs

section
variable (T : Estimator d n)

theorem minimaxRisk_le_worstCaseRisk 
     : minimaxRisk C n ≤ worstCaseRisk C T :=
  iInf_le _ T

theorem meanSquaredRisk_le_worstCaseRisk 
     θ (hθ : Admissible C θ) :
    meanSquaredRisk T θ ≤ worstCaseRisk C T :=
  le_iSup (fun θ : {θ : RegressionParameter d // Admissible C θ} =>
    meanSquaredRisk T θ.val) ⟨θ, hθ⟩
end

end


theorem minimaxRisk_finite {d } (C : ModelConstants d) n :
    minimaxRisk C n < ∞ := by
  apply lt_of_le_of_lt (minimaxRisk_le_worstCaseRisk C
    (constantEstimator d n C.varianceLower))
  unfold worstCaseRisk
  aesop (add unsafe [lt_of_le_of_lt, constantEstimator_risk_bound])

end NearlyMinimax
