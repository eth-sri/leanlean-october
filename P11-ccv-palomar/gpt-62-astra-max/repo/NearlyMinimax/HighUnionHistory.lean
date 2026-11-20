module

public import NearlyMinimax.HighUnionReset
public import NearlyMinimax.HistoryPatchStateAppend

@[expose] public section

/-! Genuine complete-union canonical histories: Borel raw states, legal
density and coefficient values, and pointwise/total reference mean one. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

section Finite
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] (R : HighUnionRowData d k F I E)

variable (δ Cfr : ℝ) (hCfr : 0 < Cfr) (hVector : ∀ i e, (∑ γ, |R.rowVector i e γ|) ≤ Cfr⁻¹)
    (hTime : ∀ i e, R.rowTime i e ∈ Icc (0 : ℝ) 1) {n : ℕ} (labels : Fin n → HighWindowLabels d k)
    (initial : HighRawState d k F)

def highUnionHistoryState (marks : Fin n → HighUnionMark E) : HighRawState d k F :=
  (List.ofFn (fun i : Fin n => i)).foldl
    (fun θ i => highUnionRawUpdate R δ (labels i) (marks i) θ) initial

theorem highUnionHistory_density_joint_measurable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2))
    (hOffset : ∀ i, Measurable (R.rowIntercept i)) (δ : ℝ)
    {n : ℕ} (labels : Fin n → HighWindowLabels d k)
    {initial : HighRawState d k F} (hi : Measurable initial.1) :
    Measurable (fun mx : (Fin n → HighUnionMark E) × Covariate d =>
      (highUnionHistoryState R δ labels initial mx.1).1 mx.2) := affinePatchFold_density_joint_measurable
    (highTorusPatch_measurableSet d k) (highUnionSlope R)
    (fun _ e _ => highUnionIntercept R δ e)
    (fun j => highUnionSlope_joint_measurable R hSlope j)
    (fun _ => (highUnionIntercept_measurable R hOffset δ).comp measurable_fst)
    (fun _ => highUnionResponseReset R) labels (List.ofFn (fun i : Fin n => i))
    (initial := (fun _ => initial)) (hi.comp measurable_snd)

/-- Finite independent complete-union marks preserve pointwise density
mean one. Raw row slopes are centered by their actual absolute-law reflection
rules; the single global correction gives offset mean one. -/
theorem highUnionHistory_density_mean_one [∀ i, IsProbabilityMeasure (R.rowLaw i)]
    (hMass : ∀ i, 0 ≤ R.rowMass i) (hTotal : 0 < highRowTotalMass R.rowMass)
    (hSlope : ∀ j x i, Measurable (fun e => R.rowSlope j i e x))
    (hiSlope : ∀ j x i, Integrable (fun e => R.rowSlope j i e x) (R.rowLaw i))
    (hcSlope : ∀ j x i, (∫ e, R.rowSlope j i e x ∂(R.rowLaw i)) = 0)
    (hOffset : ∀ i, Measurable (R.rowIntercept i))
    {a b : ℝ} (hOffsetBound : ∀ i e, R.rowIntercept i e ∈ Icc a b)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {n : ℕ} (labels : Fin n → HighWindowLabels d k)
    (initial : HighRawState d k F) (hinit : ∀ x, initial.1 x = 1) (x : Covariate d) :
    (∫ marks, (highUnionHistoryState R δ labels initial marks).1 x
      ∂Measure.pi (fun _ : Fin n => highUnionLaw R δ)) = 1 := by
  let π := highUnionLaw R δ
  letI  := highUnionLaw_probability R hMass hTotal hδ0 hδ1.le
  let s := fun j e =>
    if x ∈ highTorusPatch j then highUnionSlope R j e x else 1
  let o := fun j e =>
    if x ∈ highTorusPatch (k := k) j then highUnionIntercept R δ e else 0
  have hs : ∀ j, Integrable (s j) π := by
    intro j
    by_cases hx : x ∈ highTorusPatch j
    · simp [s, if_pos hx]
      exact balancedReferenceLaw_integrable δ
        (highCenteredRowUnionSlope_measurable (hSlope j x))
        (highRowReferenceUnion_integrable R.rowLaw R.rowMass
          (sigma_uncurry_measurable (hSlope j x)) (hiSlope j x))
    · simp only [s, if_neg hx]
      exact integrable_const _
  have ho : ∀ j, Integrable (o j) π := by
    intro j
    by_cases hx : x ∈ highTorusPatch j
    · simp [o, if_pos hx]
      exact balancedReferenceLaw_integrable δ (highUnionIntercept_measurable R hOffset δ)
        (highRowReferenceUnion_integrable R.rowLaw R.rowMass
          (sigma_uncurry_measurable hOffset)
          (fun i => boundedIntercept_integrable (R.rowLaw i)
            (hOffset i) a b (hOffsetBound i)))
    · simp only [o, if_neg hx]
      exact integrable_const _
  have hmean : ∀ j, (∫ e, s j e ∂π) + (∫ e, o j e ∂π) = 1 := by
    intro j
    by_cases hx : x ∈ highTorusPatch j
    · simp [s, o, if_pos hx]
      change (∫ e, highCenteredRowUnionSlope (fun i e => R.rowSlope j i e x) e
        ∂highCenteredRowUnionLaw R.rowLaw R.rowMass δ) +
        (∫ e, highCenteredRowUnionIntercept R.rowLaw R.rowMass R.rowIntercept δ e
          ∂highCenteredRowUnionLaw R.rowLaw R.rowMass δ) = 1
      rw [highCenteredRowUnionSlope_integral_zero hMass hTotal (hSlope j x) (hiSlope j x) (hcSlope j x) hδ0 hδ1.le,
        highCenteredRowUnionIntercept_integral_one R.rowLaw hMass hTotal hOffset hOffsetBound hδ0 hδ1]
      norm_num
    · aesop
  convert finiteAffineHistory_integral_one hs ho hmean labels using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro marks
  exact (affinePatchFold_density_eq (highTorusPatch) (highUnionSlope R)
    (fun _ e _ => highUnionIntercept R δ e) (fun _ => highUnionResponseReset R)
    labels marks (List.ofFn (fun i : Fin n => i)) initial x).trans (by rw [hinit x]; rfl)

theorem highUnionHistory_density_interval {δ : ℝ} {a b : ℝ}
    (hLegal : ∀ j e x v, v ∈ Icc a b →
      highUnionSlope R j e x * v + highUnionIntercept R δ e ∈ Icc a b)
    {n : ℕ} (labels : Fin n → HighWindowLabels d k) (initial : HighRawState d k F)
    (hi : ∀ x, initial.1 x ∈ Icc a b) (marks : Fin n → HighUnionMark E) (x : Covariate d) :
    (highUnionHistoryState R δ labels initial marks).1 x ∈ Icc a b :=
  affineRawHistory_density_interval (highTorusPatch) (fun _ => highUnionResponseReset R)
    labels (List.ofFn (fun i : Fin n => i)) marks hLegal hi x

include hCfr hVector hTime in
theorem highUnionHistory_coefficient_ball
    (hi : ∀ j, (∑ γ, |initial.2 j γ|) ≤ Cfr⁻¹) (marks : Fin n → HighUnionMark E) :
    ∀ j, (∑ γ, |(highUnionHistoryState R δ labels initial marks).2 j γ|) ≤ Cfr⁻¹ := by
  have hf : ∀ indices : List (Fin n), ∀ initial : HighRawState d k F,
      (∀ j, (∑ γ, |initial.2 j γ|) ≤ Cfr⁻¹) → ∀ j,
      (∑ γ, |(indices.foldl (fun θ i => highUnionRawUpdate R δ (labels i) (marks i) θ)
        initial).2 j γ|) ≤ Cfr⁻¹ := by
    intro indices
    induction indices with
    | nil => intro initial hi j; exact hi j
    | cons i indices ih =>
      intro initial hi
      apply ih
      intro j
      by_cases hj : j = labels i
      · subst j
        change (∑ γ, |(Function.update initial.2 (labels i)
          (highUnionResponseReset R (marks i) (initial.2 (labels i)))) (labels i) γ|) ≤ _
        rw [Function.update_self]
        exact highUnionResponseReset_ball R hCfr hVector hTime _ (hi _)
      · simpa only [highUnionRawUpdate, rawPatchUpdate, responseCoordinateUpdate,
          Function.update_of_ne hj] using hi j
  exact hf _ initial hi

end Finite

section Canonical
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (R : HighUnionRowData d k F I E)
  (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)

section
variable (δ : ℝ) (initial : HighRawState d k F) (h : HistoryMarked dependent (HighUnionMark E))

def highUnionMarkedState : HighRawState d k F :=
  historyMarkedRawState (highUnionRawUpdate R δ) initial h

def highUnionMarkedDensity (x : Covariate d) : ℝ :=
  (highUnionMarkedState R dependent δ initial h).1 x

end

section
variable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2))
    (hOffset : ∀ i, Measurable (R.rowIntercept i)) (δ : ℝ) {initial : HighRawState d k F}
    (hi : Measurable initial.1)
include hOffset hSlope hi

theorem highUnionMarkedDensity_joint_measurable :
    Measurable (fun hx : HistoryMarked dependent (HighUnionMark E) × Covariate d =>
      highUnionMarkedDensity R dependent δ initial hx.1 hx.2) := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  let X := fun g : DependenceHeap dependent =>
    Fin (historyShapeLength g) → HighUnionMark E
  let G : Sigma (fun g => X g × Covariate d) → ℝ := fun hx =>
    highUnionMarkedDensity R dependent δ initial ⟨hx.1,hx.2.1⟩ hx.2.2
  have hG : Measurable G := by
    apply (sigma_measurable_iff G).mpr
    intro g
    exact highUnionHistory_density_joint_measurable R hSlope hOffset δ (historyShapeCanonicalLabels g) hi
  exact hG.comp (historySigmaProdMeasurableEquiv X (Covariate d)).measurable

end

theorem highUnionMarkedState_append [NeZero k] (δ : ℝ) (initial : HighRawState d k F)
    (j : HighWindowLabels d k)
    (h : WindowHistory d k E)
    (fresh : HighUnionMark E) :
    highUnionMarkedState R (windowDepends d k) δ initial
      (historyMarkedAppend j (h,fresh)) =
      highUnionRawUpdate R δ j fresh
        (highUnionMarkedState R (windowDepends d k) δ initial h) :=
  highMarkedRawState_patch_append (highUnionSlope R)
    (fun _ e _ => highUnionIntercept R δ e) (fun _ => highUnionResponseReset R) initial j h fresh

end Canonical
end NearlyMinimax
