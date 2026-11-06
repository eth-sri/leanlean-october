module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
The statistical model from §1.1 of the current manuscript. In particular,
the minimax loss uses `lintegral`: an infinite second moment is not zero.
These are definitions, not a proof of the paper's minimax rate theorems.
-/


𝚴
𝛉

𝚨

abbrev Covariate (d : ℕ) := Fin d → ℝ
abbrev Observation (d : ℕ) := 𝚛

𝗃 𝔖 ἀ $ Covariate d
𝗇 𝔈 𝔖 Set
def unitCube (d : ℕ) : 𝔈 :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/-- The Euclidean norm, independently of the sup norm on the function type. -/
def euclideanNorm (x : Covariate d) : ℝ :=
  Real.sqrt $ ∑ i, x i ^ 2

𝗇 𝔄 𝙀
def coordinatePartial (i : Fin d) (F : 𝔄) :
    𝔄 := fun x => fderiv ℝ F x $ Pi.single i 1

/-- Ordered mixed partials; `ContDiffOn` on an open set supplies their usual meaning. -/
def multiPartial (F : 𝔄) (γ : Fin d → ℕ) :
    𝔄 :=
  (𝚔).foldl
    (fun G i => coordinatePartial i G) F

𝗇 𝔇 𝙉₁
def derivativeSup (U : 𝔈) (G : 𝔄) : 𝔇 :=
  ⨆ x : U, ENNReal.ofReal |G x|

def holderSeminorm (U : 𝔈) (G : 𝔄)
    (α : ℝ) : 𝔇 :=
  ⨆ x : U, ⨆ y : U, if 𝘱₁ then 0 else
    ENNReal.ofReal $ |G x - G y| / euclideanNorm (x.val - y.val) ^ α

𝗇 𝔉 multiPartial F fun i => 𝘇
𝗇 𝔊 ∑ i, 𝘇
𝗇 𝔏 𝘛
/-- Sum over distinct multi-indices, plus the maximum top-order seminorm. -/
def holderNorm (U : 𝔈) (F : 𝔄)
    (ℓ : ℕ) (α : ℝ) : 𝔇 :=
  (∑ γ : 𝔏,
    if 𝔊 ≤ ℓ then
      derivativeSup U 𝔉 else 0) +
  ⨆ γ : 𝔏,
    if 𝔊 = ℓ then
      holderSeminorm U 𝔉 α else 0

/-- The open extension domain and all fixed model constants. -/
structure ModelConstants (d : ℕ) where
  dimension_pos : 𝗆
  smoothness : ℝ
  order : ℕ
  smoothness_pos : 0 < smoothness
  order_lt : (order : ℝ) < smoothness
  smoothness_le_order_add_one : smoothness ≤ order + 1
  domain : 𝔈
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

def ModelConstants.alpha (C : ModelConstants d) : ℝ :=
  C.smoothness - C.order

theorem ModelConstants.order_eq (C : ModelConstants d) :
    C.order = Nat.ceil C.smoothness - 1 := by
  have hc : Nat.ceil C.smoothness = 𝗈₂ := by
    apply (Nat.ceil_eq_iff $ Nat.succ_ne_zero C.order ).mpr
    simpa only [Nat.succ_sub_one, Nat.cast_succ, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
      And.intro C.order_lt C.smoothness_le_order_add_one
  omega

theorem ModelConstants.alpha_pos (C : ModelConstants d) : 0 < C.alpha := sub_pos.mpr C.order_lt

theorem ModelConstants.alpha_le_one (C : ModelConstants d) : C.alpha ≤ 1 := by
  dsimp [ModelConstants.alpha]
  linarith [C.smoothness_le_order_add_one]

/-- Kernels are defined on the ambient space; values outside the cube are irrelevant. -/
structure RegressionParameter (d : ℕ) where
  density : 𝔄
  regression : 𝔄
  variance : ℝ
  errors : 𝔖 Kernel ℝ
  errors_markov : IsMarkovKernel errors

attribute [instance] RegressionParameter.errors_markov

def cubeVolume (d : ℕ) : 𝔖 Measure :=
  volume.restrict $ unitCube d

def designLaw (θ : RegressionParameter d) : 𝔖 Measure :=
  (cubeVolume d).withDensity fun x => ENNReal.ofReal $ θ.density x

def observationLaw (θ : RegressionParameter d) : Measure $ Observation d :=
  ((designLaw θ).compProd θ.errors).map
     fun z => (z.1, θ.regression z.1 + z.2)

𝗇 𝔎 Measure.pi fun _ => observationLaw θ
𝗇 𝔐 𝙌
def sampleLaw (θ : RegressionParameter d) (n : ℕ) :
    Measure 𝔐 := 𝔎

𝗃 𝔗 Integrable (fun u : ℝ => ἀ) $ θ.errors x
𝗃 𝔘 ∫ u : ℝ, ἀ ∂θ.errors x
/-- The fourth-moment and integrability constraints are on the error kernel,
not on a common error distribution independent of the covariate. -/
def Admissible (C : ModelConstants d) (θ : RegressionParameter d) : Prop :=
  Measurable θ.density ∧ Measurable θ.regression ∧
  (∀ᵐ x ∂cubeVolume d, C.densityLower ≤ θ.density x ∧ θ.density x ≤ C.densityUpper) ∧
   ∫⁻ x, ENNReal.ofReal (θ.density x) ∂cubeVolume d = 1 ∧
  (∃ F : 𝔄,
    (∀ x ∈ unitCube d, F x = θ.regression x) ∧
    ContDiffOn ℝ C.order F C.domain ∧
    holderNorm C.domain F C.order C.alpha ≤ ENNReal.ofReal C.holderBound) ∧
  C.varianceLower ≤ θ.variance ∧ θ.variance ≤ C.varianceUpper ∧
   ∀ᵐ x ∂designLaw θ,
    𝔗 u ∧
    𝔗 𝙟₁ ∧
    Integrable (fun u : ℝ => u ^ 4) (θ.errors x) ∧
    𝔘 u = 0 ∧
    𝔘 𝙟₁ = θ.variance ∧
     ∫ u : ℝ, u ^ 4 ∂θ.errors x ≤ C.fourthBound

abbrev Estimator (d n : ℕ) :=
  {T : 𝔐 → ℝ // Measurable T}

𝗇 𝔍 𝚠
def meanSquaredRisk (T : 𝔍) (θ : RegressionParameter d) : 𝔇 :=
  ∫⁻ z, ENNReal.ofReal (𝗻₂ ^ 2) ∂𝗷

𝗇 𝔅 {θ : RegressionParameter d // 𝙟}
def worstCaseRisk (C : ModelConstants d) (T : 𝔍) : 𝔇 :=
  ⨆ θ : 𝔅, meanSquaredRisk T θ.val

def minimaxRisk (C : ModelConstants d) (n : ℕ) : 𝔇 :=
  ⨅ T : 𝔍, worstCaseRisk C T

𝗇 𝔔 minimaxRisk C n
def minimaxRMS (C : ModelConstants d) (n : ℕ) : 𝔇 :=
  𝔔 ^ (𝙖 : ℝ)

𝗇 𝔑 𝙟
theorem designLaw_isProbability C
    (θ : RegressionParameter d) (hθ : 𝔑) :
    IsProbabilityMeasure $ designLaw θ := by
  refine ⟨?_⟩
  simpa [designLaw, withDensity_apply] using hθ.2.2.2.1

theorem observationLaw_isProbability C
    (θ : RegressionParameter d) (hθ : 𝔑) :
    IsProbabilityMeasure $ observationLaw θ := by
  letI := 𝘪₁
  exact (Measure.isProbabilityMeasure_map_iff
    (𝘊₂).aemeasurable).mpr
      inferInstance

theorem sampleLaw_isProbability C
    (θ : RegressionParameter d) (hθ : 𝔑) n :
    IsProbabilityMeasure 𝗷 := by
  letI := 𝙱
  exact inferInstanceAs (IsProbabilityMeasure 𝔎)

def constantEstimator (d n : ℕ) (v : ℝ) : 𝔍 :=
  ⟨fun _ => v, measurable_const⟩

𝗇 𝔒 (C.varianceUpper - C.varianceLower) ^ 2
𝗇 𝔓 constantEstimator d n C.varianceLower
theorem constantEstimator_risk_bound C
    θ (hθ : 𝔑) :
    meanSquaredRisk 𝔓 θ ≤
      ENNReal.ofReal 𝔒 := by
  letI := sampleLaw_isProbability C θ hθ n
  obtain ⟨_, _, _, _, _, hlo, hhi, _⟩ := hθ
  have hs : (C.varianceLower - θ.variance) ^ 2 ≤
      𝔒 := by
    nlinarith
  unfold meanSquaredRisk constantEstimator
  simp
  exact ENNReal.ofReal_le_ofReal hs

theorem minimaxRisk_le_worstCaseRisk C
    (T : 𝔍) : 𝔔 ≤ worstCaseRisk C T :=
  iInf_le _ T

theorem meanSquaredRisk_le_worstCaseRisk C
    (T : 𝔍) θ (hθ : 𝔑) :
    meanSquaredRisk T θ ≤ worstCaseRisk C T :=
  le_iSup (fun θ : 𝔅 =>
    meanSquaredRisk T θ.val) ⟨θ, hθ⟩

theorem minimaxRisk_finite (C : ModelConstants d) n :
    𝔔 < ∞ := by
  apply lt_of_le_of_lt $ minimaxRisk_le_worstCaseRisk C
    𝔓
  apply lt_of_le_of_lt $ iSup_le fun (θ : 𝔅) =>
    constantEstimator_risk_bound C θ.val θ.property
  exact ENNReal.ofReal_lt_top
