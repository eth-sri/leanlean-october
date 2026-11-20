module

public import NearlyMinimax.HighRowReferenceUnion

@[expose] public section

/-! The paper's global tagged Xi reference construction: first mix the
absolute row laws with their true variation masses, then add exactly one
zero-weight corrective branch. The generator action and source activation
constant are preserved by actual positive-measure integral identities. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

section
variable {J : Type*} [Fintype J] {E : J → Type*} [∀ j, MeasurableSpace (E j)]

section
variable (π : (j : J) → Measure (E j)) (B : J → ℝ) (w intercept : (j : J) → E j → ℝ) (δ : ℝ)

def highCenteredRowUnionLaw :
    Measure ((Sigma E) ⊕ Unit) := balancedReferenceLaw (highRowReferenceUnion π B) δ

def highCenteredRowUnionActivation :
    (Sigma E) ⊕ Unit → ℝ := balancedActivation (highRowUnionActivation B w) δ

def highCenteredRowUnionIntercept : (Sigma E) ⊕ Unit → ℝ :=
  balancedIntercept (fun e : Sigma E => intercept e.1 e.2) δ
    (∫ e : Sigma E, intercept e.1 e.2 ∂highRowReferenceUnion π B)

def highCenteredRowUnionSlope (slope : (j : J) → E j → ℝ) : (Sigma E) ⊕ Unit → ℝ :=
  balancedSlope (fun e : Sigma E => slope e.1 e.2)

theorem highCenteredRowUnionLaw_probability
    [∀ j, IsProbabilityMeasure (π j)] {B : J → ℝ} (hB : ∀ j, 0 ≤ B j)
    (hTotal : 0 < highRowTotalMass B) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    IsProbabilityMeasure (highCenteredRowUnionLaw π B δ) := by
  letI := highRowReferenceUnion_probability π hB hTotal
  exact balancedReferenceLaw_probability _ hδ0 hδ1

end

section
variable {π : (j : J) → Measure (E j)} {B : J → ℝ} (hB : ∀ j, 0 ≤ B j) {w : (j : J) → E j → ℝ}
    (hw : ∀ j, Measurable (w j)) (hInt : ∀ j, Integrable (w j) (π j)) (hTotal : 0 < highRowTotalMass B)
    {slope : (j : J) → E j → ℝ} (hSlope : ∀ j, Measurable (slope j))

include hB hw hInt in
theorem highCenteredRowUnionActivation_centered
    (hCenter : ∀ j, (∫ e, w j e ∂π j) = 0)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ e, highCenteredRowUnionActivation B w δ e ∂highCenteredRowUnionLaw π B δ) = 0 :=
  balancedActivation_integral_zero hδ hδ1 (highRowUnionActivation_measurable B hw)
    (highRowUnionActivation_integrable B hw hInt)
    (highRowUnionActivation_centered hB hw hInt hCenter)

theorem highCenteredRowUnionActivation_bound (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) {w : (j : J) → E j → ℝ}
    (hw : ∀ j e, |w j e| ≤ B j) {δ : ℝ} (hδ : 0 < δ) (e : (Sigma E) ⊕ Unit) :
    |highCenteredRowUnionActivation B w δ e| ≤ highRowTotalMass B / δ := by
  apply balancedActivation_bound _ hδ hTotal.le
  intro e
  simpa using highRowUnionActivation_bound hB hTotal 1 (by norm_num)
    w (by simpa only [div_one] using hw) e

theorem highCenteredRowUnionActivation_measurable (B : J → ℝ)
    {w : (j : J) → E j → ℝ} (hw : ∀ j, Measurable (w j)) (δ : ℝ) :
    Measurable (highCenteredRowUnionActivation B w δ) :=
  (((highRowUnionActivation_measurable B hw)).div_const δ).sumElim measurable_const

include hSlope in
theorem highCenteredRowUnionSlope_measurable : Measurable (highCenteredRowUnionSlope slope) :=
  ((sigma_uncurry_measurable hSlope)).sumElim measurable_const

theorem highCenteredRowUnionIntercept_measurable (π : (j : J) → Measure (E j)) (B : J → ℝ)
    {intercept : (j : J) → E j → ℝ} (hIntercept : ∀ j, Measurable (intercept j)) (δ : ℝ) :
    Measurable (highCenteredRowUnionIntercept π B intercept δ) :=
  ((sigma_uncurry_measurable hIntercept)).sumElim measurable_const

include hB hTotal hSlope in
theorem highCenteredRowUnionSlope_integral_zero
    (hiSlope : ∀ j, Integrable (slope j) (π j))
    (hCenter : ∀ j, (∫ e, slope j e ∂π j) = 0)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (∫ e, highCenteredRowUnionSlope slope e ∂highCenteredRowUnionLaw π B δ) = 0 :=
  balancedSlope_integral_zero hδ0 hδ1 (sigma_uncurry_measurable hSlope)
    (highRowReferenceUnion_integrable π B (sigma_uncurry_measurable hSlope) hiSlope)
    (highRowReferenceUnion_integral_common_mean hB hTotal hSlope hiSlope hCenter)

end

variable {d : ℕ} {C : ModelConstants d} (π : (j : J) → Measure (E j)) [∀ j, IsProbabilityMeasure (π j)]
    {B : J → ℝ} (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B) {intercept : (j : J) → E j → ℝ}
include hB hTotal

theorem highCenteredRowUnionIntercept_integral_one (hIntercept : ∀ j, Measurable (intercept j))
    {a b : ℝ} (hBound : ∀ j e, intercept j e ∈ Icc a b)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∫ e, highCenteredRowUnionIntercept π B intercept δ e ∂highCenteredRowUnionLaw π B δ) = 1 := by
  letI := highRowReferenceUnion_probability π hB hTotal
  exact balancedIntercept_integral_one hδ0 hδ1
    (sigma_uncurry_measurable hIntercept)
    (boundedIntercept_integrable (highRowReferenceUnion π B)
      (sigma_uncurry_measurable hIntercept) a b (fun e => hBound e.1 e.2))

/-- The source's single corrective intercept is legal at its uniform
resolution threshold, for the actual total union intercept mean. -/
theorem highCenteredRowUnionIntercept_source_interval (hIntercept : ∀ j, Measurable (intercept j))
    {M : ℝ} (hM : highCenterResolutionThreshold C ≤ M)
    (hBound : ∀ j e, intercept j e ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M)) :
    ∀ e, highCenteredRowUnionIntercept π B intercept (highCenterMix C) e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  letI := highRowReferenceUnion_probability π hB hTotal
  have hg := highCenterResolution_guards hM
  have hq := boundedIntercept_mean_mem (highRowReferenceUnion π B) (sigma_uncurry_measurable hIntercept)
    (C.densityLower+1/M) (C.densityUpper-1/M) (fun e => hBound e.1 e.2)
  intro e
  cases e with
  | inl e => exact hBound e.1 e.2
  | inr u =>
    exact sourceBalancedResetAnchor_mem (by linarith) hg.2 hq

/-- Source global density reset legality, including the one corrective branch. -/
theorem highCenteredRowUnion_reset_source_legal
    (slope intercept : (j : J) → E j → ℝ) (hIntercept : ∀ j, Measurable (intercept j))
    {M : ℝ} (hM : highCenterResolutionThreshold C ≤ M)
    (hBound : ∀ j e, intercept j e ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M))
    (hlegal : ∀ j e p, p ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) →
      slope j e*p+intercept j e ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M))
    (e : (Sigma E) ⊕ Unit) {p : ℝ}
    (hp : p ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M)) :
    highCenteredRowUnionSlope slope e*p+highCenteredRowUnionIntercept π B intercept (highCenterMix C) e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  cases e with
  | inl e => solve_by_elim [hlegal]
  | inr u =>
    simpa only [highCenteredRowUnionSlope, balancedSlope, Sum.elim_inr, zero_mul, zero_add]
      using highCenteredRowUnionIntercept_source_interval π hB hTotal hIntercept hM hBound (Sum.inr u)

end

end NearlyMinimax
