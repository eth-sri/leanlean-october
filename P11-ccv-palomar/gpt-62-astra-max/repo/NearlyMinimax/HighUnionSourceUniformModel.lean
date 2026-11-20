module

public import NearlyMinimax.HighUnionSourceModel
public import NearlyMinimax.PaperGoals


@[expose] public section

/-! The original model constants are chosen before the extension domain.
All field norm bounds hold on every set, so the complete-row prior uses one
fixed frame radius and amplitude cutoff for all extension domains. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

/-- Uniform original-model legality for actual complete-row canonical histories.
The coefficient radius and ternary amplitude cutoff precede `∀ U`, exactly
as required by the high-smoothness theorem in the manuscript. -/
theorem highUnionSource_original_model_uniform {d : ℕ} {C : ModelConstants d}
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr η0 : ℝ, 1 ≤ Cfr ∧ 0 < η0 ∧
      ∀ U,
      ∀ k F, ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)), 4 ≤ k →
      ∀ (I : Type*) (_ : Fintype I) E (_ : (i : I) → MeasurableSpace (E i))
        (_ : (i : I) → StandardBorelSpace (E i))
        (R : HighUnionRowData d k F I E) M,
      HighUnionSourceGuards C M Cfr R →
      ∀ cf, 0 ≤ cf → highWindowHolderConstant C * cf ≤ C.holderBound →
        cf * k^(-C.smoothness) ≤ η0 →
      ∀ cm, 0 ≤ cm → cm ≤ 1/C.densityUpper →
      ∀ h,
        |highUnionSourceMass C R h-1| ≤ cm/M →
      ∀ V, |V-Q.v| ≤ Q.ρ →
      let p := highUnionSourceDensity C R h
      let f := highUnionSourceRegression C R (cf * k^(-C.smoothness)) h
      ∃ hq : ∀ x y, 0 ≤ ternaryMass Q.a (f x) V y,
        Admissible (C.withDomain U) (normalizedDensityTernaryParameter p
          (highFrameField_contDiff d k _ _).continuous.measurable Q.a_pos.ne' hq) := by
  obtain ⟨Cfr, hCfr, hbound⟩ := highFrameField_original_model_bounds C
  obtain ⟨η0, hη0, hguard⟩ := highFrame_ternary_amplitude_guards Q
  refine ⟨Cfr, η0, hCfr, hη0, ?_⟩
  intro U k F hk0 horder hk I hI E hE hEB R M G cf hcf hcfH hη cm hcm hcmU h hmass V hV
  letI := hk0
  letI := horder
  letI := hI
  letI := hE
  letI := hEB
  let η := cf * k^(-C.smoothness)
  let P := fun j => highFramePolynomial ((highUnionSourceState C R h).2 j)
  let f := highFrameField k η P
  let p := highUnionSourceDensity C R h
  have hP (j)  :=
    (highFramePolynomial_coefficientL1_le _).trans (highUnionSourceState_coefficient_ball C R G h j)
  obtain ⟨_, hsupη⟩ := hguard η (by dsimp [η]; positivity) hη
  obtain ⟨hvalue, _, _, hnorm⟩ := hbound k hk0 hk cf hcf P hP
  have hf x : |f x| ≤ Q.ρ :=
    (hvalue x).trans (hsupη.trans (by linarith [Q.ρ_pos]))
  have hlegal x := Q.legal _ V (hf x) hV
  have hq  :=
    fun x y => Q.c_pos.le.trans ((hlegal x).2.2.1 y)
  refine ⟨hq, ?_⟩
  have hF := highFrameField_contDiff d k η P
  have hp : Measurable p :=
    (highUnionSourceDensity_joint_measurable C R G).comp (measurable_const.prodMk measurable_id)
  have hraw : ∀ᵐ x ∂cubeVolume d,
      C.densityLower+1/M ≤ p x ∧ p x ≤ C.densityUpper-1/M :=
    Filter.Eventually.of_forall (fun x => highUnionSourceDensity_interval C R G h x)
  have hM := (highCenterResolution_guards G.resolution).1
  have hM0 : 0 < M := by linarith
  have hint := highRawDensity_integrable hM0 hp hraw
  have hp0 : 0 ≤ᵐ[cubeVolume d] p := by
    filter_upwards [hraw] with x hx
    change 0 ≤ _
    linarith [C.densityLower_pos, one_div_pos.mpr hM0]
  refine ⟨(hp.div_const _), hF.continuous.measurable,
    (by filter_upwards [hraw] with x hx; exact high_normalized_density_interval hM hcm hcmU hmass hx),
    highNormalizedDensity_normalized hint hp0 (lt_of_lt_of_le (by norm_num) (high_raw_mass_lower hM hcm hcmU hmass)), ?_,
    (hlegal 0).1.le, (hlegal 0).2.1.le, ?_⟩
  · refine ⟨f, fun _ _ => rfl, (hF.of_le (by simp)).contDiffOn, ?_⟩
    exact (hnorm U.carrier).trans (ENNReal.ofReal_le_ofReal hcfH)
  · apply Filter.Eventually.of_forall
    intro x
    refine ⟨ternary_error_integrable Q.a V hF.continuous.measurable x _,
      ternary_error_integrable Q.a V hF.continuous.measurable x _,
      ternary_error_integrable Q.a V hF.continuous.measurable x _,
      ternary_error_mean hF.continuous.measurable Q.a_pos.ne' (hq x),
      ternary_error_variance hF.continuous.measurable Q.a_pos.ne' (hq x), ?_⟩
    exact (ternary_error_fourth hF.continuous.measurable Q.a_pos.ne' (hq x)).trans_le
      (by simpa only [ternary_fourth_central_moment _ _ _ Q.a_pos.ne', ModelConstants.withDomain] using (hlegal x).2.2.2)

end NearlyMinimax
