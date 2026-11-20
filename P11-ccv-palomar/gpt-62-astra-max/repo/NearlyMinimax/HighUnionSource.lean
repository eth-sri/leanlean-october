module

public import NearlyMinimax.HighUnionHistory


@[expose] public section

/-! Source constant specialization for complete-row canonical histories.
The guard fields are primitive actual row-law identities and finite atomic
reset bounds; history expectations and original-model legality are outputs. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

theorem high_source_interval_numeric {d : ℕ} {C : ModelConstants d} {M : ℝ}
    (hM : highCenterResolutionThreshold C ≤ M) :
    0 < C.densityLower+1/M ∧ C.densityLower+1/M < C.densityUpper-1/M := by
  have hg := highCenterResolution_guards hM
  have hM0 : 0 < M := by bound
  constructor
  · linarith [C.densityLower_pos,one_div_pos.mpr hM0]
  · linarith [hg.2,highCenterRadius_pos C,(highCenterRadius_le_margins C).1,
      (highCenterRadius_le_margins C).2]

structure HighUnionSourceGuards {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] (C : ModelConstants d) (M Cfr : ℝ)
    (R : HighUnionRowData d k F I E) : Prop where
  resolution : highCenterResolutionThreshold C ≤ M
  frame : 1 ≤ Cfr
  row_probability : ∀ i, IsProbabilityMeasure (R.rowLaw i)
  mass_nonneg : ∀ i, 0 ≤ R.rowMass i
  total_positive : 0 < highRowTotalMass R.rowMass
  activation_measurable : ∀ i, Measurable (R.rowActivation i)
  activation_bound : ∀ i e, |R.rowActivation i e| ≤ R.rowMass i
  activation_centered : ∀ i, (∫ e, R.rowActivation i e ∂(R.rowLaw i)) = 0
  slope_measurable : ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2)
  slope_integrable : ∀ j x i, Integrable (fun e => R.rowSlope j i e x) (R.rowLaw i)
  slope_centered : ∀ j x i, (∫ e, R.rowSlope j i e x ∂(R.rowLaw i)) = 0
  intercept_measurable : ∀ i, Measurable (R.rowIntercept i)
  intercept_interval : ∀ i e, R.rowIntercept i e ∈
    Icc (C.densityLower + 1/M) (C.densityUpper - 1/M)
  row_reset_interval : ∀ j i e x v, v ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) →
    R.rowSlope j i e x * v + R.rowIntercept i e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M)
  vector_measurable : ∀ i γ, Measurable (fun e => R.rowVector i e γ)
  time_measurable : ∀ i, Measurable (R.rowTime i)
  vector_ball : ∀ i e, (∑ γ, |R.rowVector i e γ|) ≤ Cfr⁻¹
  time_interval : ∀ i e, R.rowTime i e ∈ Icc (0 : ℝ) 1

section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k F I E)

def highUnionVacuum : HighRawState d k F := ((fun _ => 1), 0)

section
variable (h : WindowHistory d k E)

def highUnionSourceState
    :
    HighRawState d k F :=
  highUnionMarkedState R (windowDepends d k) (highCenterMix C)
    highUnionVacuum h

def highUnionSourceDensity

    (x : Covariate d) : ℝ := (highUnionSourceState C R h).1 x

def highUnionSourceMass
    : ℝ :=
  ∫ x, highUnionSourceDensity C R h x ∂cubeVolume d

end

variable {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G

theorem highUnionSourceLaw_probability : IsProbabilityMeasure (highUnionLaw R (highCenterMix C)) := by
  letI := G.row_probability
  exact highUnionLaw_probability R G.mass_nonneg G.total_positive
    (highCenterMix_mem C).1.le (highCenterMix_mem C).2.le

theorem highUnionSource_reset_interval (j : HighWindowLabels d k) (e : HighUnionMark E)
    (x : Covariate d) (v : ℝ) (hv : v ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M)) :
    highUnionSlope R j e x * v + highUnionIntercept R (highCenterMix C) e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  letI := G.row_probability
  exact highCenteredRowUnion_reset_source_legal R.rowLaw
    G.mass_nonneg G.total_positive (fun i e => R.rowSlope j i e x) R.rowIntercept
    G.intercept_measurable G.resolution G.intercept_interval
    (fun i e v hv => G.row_reset_interval j i e x v hv) e hv

theorem highUnionSource_vacuum_interval :
    (1 : ℝ) ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  have hm := highCenterResolution_guards G.resolution
  have hr := highCenterRadius_le_margins C
  constructor <;> linarith [highCenterRadius_pos C]

section
variable (h : WindowHistory d k E)
    (g : HistoryShape (fun i j : HighWindowLabels d k => j ∉ highNeighborLabels i)) (x : Covariate d)

theorem highUnionSourceDensity_interval
    :
    highUnionSourceDensity C R h x ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) :=
  highUnionHistory_density_interval R
    (highUnionSource_reset_interval C R G)
    (historyShapeCanonicalLabels h.1) highUnionVacuum
    (fun _ => highUnionSource_vacuum_interval C R G) h.2 x

theorem highUnionSourceState_coefficient_ball
    :
    ∀ j, (∑ γ, |(highUnionSourceState C R h).2 j γ|) ≤ Cfr⁻¹ := highUnionHistory_coefficient_ball R (highCenterMix C) Cfr
    (by linarith [G.frame]) G.vector_ball G.time_interval
    (historyShapeCanonicalLabels h.1) highUnionVacuum
    (fun _ => by simpa [highUnionVacuum] using
      (inv_nonneg.mpr (by linarith [G.frame] : 0 ≤ Cfr))) h.2

theorem highUnionSourceDensity_joint_measurable [∀ i, StandardBorelSpace (E i)] :
    Measurable (fun hx : WindowHistory d k E × Covariate d => highUnionSourceDensity C R hx.1 hx.2) :=
  highUnionMarkedDensity_joint_measurable R (windowDepends d k)
    G.slope_measurable G.intercept_measurable (highCenterMix C) measurable_const

theorem highUnionSourceMass_measurable [∀ i, StandardBorelSpace (E i)] :
    Measurable (highUnionSourceMass C R) :=
  by letI := cubeVolume_isProbability d; exact (highUnionMarkedDensity_joint_measurable R (windowDepends d k) G.slope_measurable G.intercept_measurable (highCenterMix C) measurable_const).stronglyMeasurable.integral_prod_right'.measurable

theorem highUnionSourceDensity_fiber_mean_one
    :
    (∫ marks, highUnionSourceDensity C R ⟨g,marks⟩ x
      ∂Measure.pi (fun _ : Fin (historyShapeLength g) => highUnionLaw R (highCenterMix C))) = 1 := by
  letI := G.row_probability
  exact highUnionHistory_density_mean_one R G.mass_nonneg G.total_positive
    (fun j x i => (G.slope_measurable j i).comp (measurable_id.prodMk measurable_const))
    G.slope_integrable G.slope_centered G.intercept_measurable G.intercept_interval (highCenterMix_mem C).1.le (highCenterMix_mem C).2 (historyShapeCanonicalLabels g) highUnionVacuum (fun _ => rfl) x

end

variable [∀ i, StandardBorelSpace (E i)]

theorem highUnionSourceMass_interval
    (h : WindowHistory d k E) :
    highUnionSourceMass C R h ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  letI := cubeVolume_isProbability d
  exact boundedIntercept_mean_mem (cubeVolume d)
    ((highUnionSourceDensity_joint_measurable C R G).comp (measurable_const.prodMk measurable_id))
    _ _ (highUnionSourceDensity_interval C R G h)

theorem highUnionSourceMass_fiber_mean_one
    (g : HistoryShape (fun i j : HighWindowLabels d k => j ∉ highNeighborLabels i)) :
    let unionLaw := highUnionLaw R (highCenterMix C)
    (∫ marks, highUnionSourceMass C R ⟨g,marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength g) => unionLaw)) = 1 := by
  intro unionLaw
  letI := highUnionSourceLaw_probability C R G
  letI := cubeVolume_isProbability d
  let f := fun mx : (Fin (historyShapeLength g) → HighUnionMark E) × Covariate d =>
    highUnionSourceDensity C R ⟨g,mx.1⟩ mx.2
  have hm  := highUnionHistory_density_joint_measurable R G.slope_measurable
    G.intercept_measurable (highCenterMix C)
    (historyShapeCanonicalLabels g) (initial := highUnionVacuum) measurable_const
  have hM0 : 0 < M := by
    have := (highCenterResolution_guards G.resolution).1
    linarith
  have hi : Integrable f ((Measure.pi (fun _ : Fin (historyShapeLength g) =>
      unionLaw)).prod (cubeVolume d)) := by
    apply (integrable_const C.densityUpper).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro mx
    have hb := highUnionSourceDensity_interval C R G ⟨g,mx.1⟩ mx.2
    change ‖f mx‖ ≤ C.densityUpper
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      linarith [hb.1, C.densityLower_pos, one_div_pos.mpr hM0])]
    exact hb.2.trans (by linarith [one_div_pos.mpr hM0])
  change (∫ marks, ∫ x, f (marks,x) ∂cubeVolume d
    ∂Measure.pi (fun _ : Fin (historyShapeLength g) => unionLaw)) = 1
  rw [integral_integral_swap hi]
  have he (x : Covariate d) :
      (∫ marks, f (marks,x) ∂Measure.pi (fun _ : Fin (historyShapeLength g) =>
        unionLaw)) = 1 := highUnionSourceDensity_fiber_mean_one C R G g x
  simp_rw [he]
  simp

theorem highUnionSourceMass_block_oscillation (hk : 2 ≤ k)
    {g : HistoryShape (fun i j : HighWindowLabels d k => j ∉ highNeighborLabels i)}
    {marks marks' : Fin (historyShapeLength g) → HighUnionMark E} {j : HighWindowLabels d k}
    (hMarks : ∀ i, historyShapeCanonicalLabels g i ≠ j → marks i = marks' i) :
    |highUnionSourceMass C R ⟨g,marks⟩ - highUnionSourceMass C R ⟨g,marks'⟩| ≤
      (2 / (k : ℝ))^d * (C.densityUpper-C.densityLower) := by
  have h := highAffineMarkedMass_block_oscillation hk
    (fun j e => (highUnionSlope_joint_measurable R G.slope_measurable j).comp
      (measurable_const.prodMk measurable_id)) (fun _ _ => measurable_const)
    (fun _ => highUnionResponseReset R)
    (by linarith [(highUnionSource_vacuum_interval C R G).1,
      (highUnionSource_vacuum_interval C R G).2])
    (highUnionSource_reset_interval C R G) (initial := highUnionVacuum) measurable_const
    (fun _ => highUnionSource_vacuum_interval C R G) hMarks
  apply h.trans
  have hM0 : 0 < M := by
    have := (highCenterResolution_guards G.resolution).1
    linarith
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith [one_div_pos.mpr hM0]

end
end NearlyMinimax
