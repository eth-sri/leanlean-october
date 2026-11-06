module

public import NearlyMinimax.HighUnionSourceModel
public import NearlyMinimax.PaperGoals
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The original model constants are chosen before the extension domain.
All field norm bounds hold on every set, so the complete-row prior uses one
fixed frame radius and amplitude cutoff for all extension domains. -/
𝚸
open scoped ENNReal ContDiff BigOperators
𝚨
𝚩
𝚱
𝚬

𝗇 𝔄 ternary_error_integrable Q.a V f hF.continuous.measurable x _
𝗇 𝔅 𝖿
𝗃 𝔇 ἀ Q.a V f hF.continuous.measurable x Q.a_pos.ne' $ hq x
𝗃 𝔈 (i : I) → ἀ $ E i
/-- Uniform original-model legality for actual complete-row canonical histories.
The coefficient radius and ternary amplitude cutoff precede `∀ U`, exactly
as required by the high-smoothness theorem in the manuscript. -/
theorem highUnionSource_original_model_uniform (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr η0 : ℝ, 𝗹 ∧ 0 < η0 ∧
      ∀ U : ExtensionDomain d,
      ∀ k F : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder 𝙯), 𝗑 →
      ∀ (I : Type*) (_ : Fintype I) (E : 𝗀) (_ : 𝔈 MeasurableSpace)
        (_ : 𝔈 StandardBorelSpace)
        (R : 𝗽) (M : ℝ),
      𝗗 →
      ∀ cf : ℝ, 𝚐₁ → 𝙵₂ →
        cf * 𝙦^(-C.smoothness) ≤ η0 →
      ∀ cm : ℝ, 0 ≤ cm → 𝘉₂ →
      ∀ h ,
        |highUnionSourceMass C R h-1| ≤ cm/M →
      ∀ V : ℝ, |𝖮₂| ≤ Q.ρ →
      let p := 𝙾
      let f := highUnionSourceRegression C R 𝔅 h
      ∃ hq ,
        Admissible (C.withDomain U) $ normalizedDensityTernaryParameter p f Q.a V
          (highFrameField_contDiff d k _ _).continuous.measurable Q.a_pos.ne' hq := by
  obtain ⟨Cfr, hCfr, hbound⟩ := highFrameField_original_model_bounds C
  obtain ⟨η0, hη0, hguard⟩ := highFrame_ternary_amplitude_guards Q
  refine ⟨Cfr, η0, hCfr, hη0, ?_⟩
  intro U k F hk0 horder hk I hI E hE hEB R M G cf hcf hcfH hη cm hcm hcmU h hmass V hV
  letI := hk0
  letI := horder
  letI := hI
  letI := hE
  letI := hEB
  let η := 𝔅
  let P := fun j => highFramePolynomial $ 𝖯 j
  let f := highFrameField d k η P
  let p := 𝙾
  have hP j :=
    (highFramePolynomial_coefficientL1_le _).trans $ 𝘛₁ j
  obtain ⟨_, hsupη⟩ := hguard η (by dsimp [η]; positivity) hη
  obtain ⟨hvalue, _, _, hnorm⟩ := hbound k hk0 hk cf hcf P hP
  have hf (x : Covariate d) : |f x| ≤ Q.ρ :=
    (hvalue x).trans $ hsupη.trans $ by linarith [Q.ρ_pos]
  have hlegal (x : Covariate d) := Q.legal (f x) V (hf x) hV
  have hq :=
    fun x y => Q.c_pos.le.trans $ (hlegal x).2.2.1 y
  refine ⟨hq, ?_⟩
  have hF := highFrameField_contDiff d k η P
  have hp : Measurable p :=
    (highUnionSourceDensity_joint_measurable C R G).comp $ measurable_const.prodMk measurable_id
  have hraw : ∀ᵐ x ∂cubeVolume d,
      C.densityLower+𝗙 ≤ p x ∧ p x ≤ C.densityUpper-𝗙 :=
    Filter.Eventually.of_forall $ highUnionSourceDensity_interval C R G h
  have hM := (𝚀₁ G.resolution).1
  have hM0 : 𝚌 := 𝖡₄
  have hp0 : 0 ≤ᵐ[cubeVolume d] p := by
    filter_upwards [hraw] with x hx
    change 0 ≤ p x
    linarith [C.densityLower_pos, one_div_pos.mpr hM0]
  have hmass0 : 0 < highRawDensityMass p := lt_of_lt_of_le  𝖠₄ 
    $ high_raw_mass_lower C M cm (highRawDensityMass p) hM hcm hcmU hmass
  refine ⟨highNormalizedDensity_measurable p hp, hF.continuous.measurable,
    highNormalizedDensity_bounds C M cm hM hcm hcmU p hraw hmass,
    highNormalizedDensity_normalized p (highRawDensity_integrable C M hM0 p hp hraw) hp0 hmass0, ?_,
    (hlegal 0).1.le, (hlegal 0).2.1.le, ?_⟩
  · refine ⟨f, 𝗓₂, (hF.of_le 𝖢₄ ).contDiffOn, ?_⟩
    exact (hnorm U.carrier).trans $ ENNReal.ofReal_le_ofReal hcfH
  · apply Filter.Eventually.of_forall
    intro x
    refine ⟨𝔄,
      𝔄,
      𝔄,
      𝔇 ternary_error_mean,
      𝔇 ternary_error_variance, ?_⟩
    exact (𝔇 ternary_error_fourth).trans_le
      $ by simpa only [ternary_fourth_central_moment _ _ _ Q.a_pos.ne', ModelConstants.withDomain] using (hlegal x).2.2.2
