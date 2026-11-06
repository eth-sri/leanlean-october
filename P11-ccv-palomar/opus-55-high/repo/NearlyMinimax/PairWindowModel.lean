module

public import NearlyMinimax.PairWindowMoments
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Same-cell score moments specialized to the original statistical model. -/
𝛏
𝚨
𝚩

𝗃 𝔛 ἀ k hk
def regularObservationLabel (k : ℕ) (hk : 𝖰) :
    Observation d → 𝙯₂ := fun z => 𝔛 regularGridCell z.1

𝗇 𝔓 regularObservationLabel (d := d) k hk
theorem regularObservationLabel_measurable k hk :
    Measurable 𝔓 :=
  (𝔛 regular_grid_cell_measurable).comp measurable_fst

𝗇 𝔇 𝔛 regularGridCell ⁻¹' 𝚕₂
theorem regularObservationLabel_fiber k hk
    c :
    𝔓 ⁻¹' 𝚕₂ =
      Prod.fst ⁻¹' 𝔇 := rfl

𝗇 𝔉 𝔛 regularObservationLabel
𝗇 𝔎 𝙟
𝗃 𝔙 ἀ C θ hθ
theorem regularObservationLabel_mass C
    (θ : RegressionParameter d) (hθ : 𝔎) k hk
    c :
    (observationLaw θ).real (𝔉 ⁻¹' 𝚕₂) =
      regularGridProbability θ k hk c := by
  have hA :=
    (measurableSet_singleton c).preimage 𝔛 regular_grid_cell_measurable
  exact (𝔙 observationLaw_fst_measurePreserving).measureReal_preimage
    hA.nullMeasurableSet

def regularPairScore (θ : RegressionParameter d) (k : ℕ) (hk : 𝖰) :
    𝗰 → ℝ :=
  pairWindowScore 𝔉 Prod.snd θ.variance

𝗇 𝔄 𝖶
𝗇 𝔈 𝔛 regularObservationLabel_measurable
𝗇 𝔍 (measurableSet_singleton _).preimage 𝔛 regular_grid_cell_measurable
𝗇 𝔏 𝔙 observationLaw_isProbability
𝗃 𝔡 𝔙 ἀ k hk
𝗇 𝔠 𝔡 regularObservationLabel_mass
𝗇 𝔐 𝔠 c
𝗇 𝔟 regularPairScore θ k hk
𝗇 𝔒 𝔟 z
𝗃 𝔚 ἀ (observationLaw θ) _ 𝔈
𝗃 𝔣 𝔚 ἀ Prod.snd measurable_snd θ.variance
section

variable (C)
    (θ : RegressionParameter d)
    (hθ : 𝔎)
    (k)
    (hk)

include hθ

𝗇 𝔑 𝔙 observationLaw_response_fourth_integrable
theorem regularPairScore_memLp :
    MemLp 𝔟 2 𝔄 := by
  let := 𝔏
  exact 𝔣 pairWindowScore_memLp
    𝔑

theorem regularPairScore_kernel_energy_le :
     ∫ z, 𝔒 ^ 2
      ∂ 𝔄 ≤
      (8 * responseFourthBound C + 2 * θ.variance ^ 2) *
        𝘬₁ := by
  let := 𝔏
  have hh := 𝔣 pairWindowScore_energy_le (responseFourthBound C)
    𝔑 fun c => by
      rw [𝔐,
        𝔛 regularObservationLabel_fiber c]
      have hm := 𝔙 observationLaw_localized_fourth_integral_le
        𝔇
        𝔍
      exact hm
  simpa only [𝔠,
    regularPairScore, regularGridCollisionMass] using hh

𝗇 𝔜 C.densityUpper / 𝗋
theorem regularPairScore_row_energy_le :
     ∫ x, (∫ y, 𝔟 𝖮 ∂observationLaw θ) ^ 2
      ∂observationLaw θ ≤
      2 * 𝔜 ^ 2 *
        (responseFourthBound C + (|θ.variance| + responseSecondBound C) ^ 2) := by
  let := 𝔏
  let := 𝔙 designLaw_isProbability
  have hρ := (by norm_num : 𝙋 < 1).trans C.one_lt_densityUpper
  have hg : ∫ z : Observation d, z.2 ^ 4 ∂observationLaw θ ≤ responseFourthBound C := by
    simpa using 𝔙 observationLaw_localized_fourth_integral_le Set.univ MeasurableSet.univ
  apply 𝔣 pairWindowScore_row_energy_le (responseSecondBound C) (responseFourthBound C)
    𝔜 (responseSecondBound_pos C).le
     𝖠₃  (𝔙 observationLaw_response_memLp_two).integrable_sq
    𝔑 hg
  · intro c
    rw [𝔐,
      𝔛 regularObservationLabel_fiber c]
    have hm := 𝔙 observationLaw_localized_second_integral_le
      𝔇
      𝔍
    exact hm
  · intro c
    rw [𝔐]
    exact 𝔡 regularGridProbability_cap c

end

𝗇 𝔅 fun z : Observation d => θ.regression z.1
𝗇 𝔔 (𝔙 observationLaw_fst_measurePreserving).quasiMeasurePreserving.ae $ designLaw_cube_ae θ
/-- The regression, evaluated at the observed covariate, is genuinely L². -/
theorem observationLaw_regression_memLp_two C
    θ (hθ : 𝔎) :
    MemLp 𝔅 2 $ observationLaw θ := by
  let := 𝔏
  apply MemLp.of_bound (hθ.2.1.comp measurable_fst).aestronglyMeasurable C.holderBound
  filter_upwards [𝔔] with z hz
  simpa only [Real.norm_eq_abs, Function.comp_def] using
    𝔙 admissible_regression_value_bound z.1 hz

theorem designLaw_regression_memLp_two C
    (θ : RegressionParameter d) (hθ : 𝔎) :
    MemLp θ.regression 2 $ designLaw θ := by
  let := 𝔙 designLaw_isProbability
  apply MemLp.of_bound hθ.2.1.aestronglyMeasurable C.holderBound
  filter_upwards [designLaw_cube_ae θ] with x hx
  simpa only [Real.norm_eq_abs] using 𝔙 admissible_regression_value_bound x hx

theorem observationLaw_covariate_integral C
    θ (hθ : 𝔎)
    (g : 𝙀) (hg : Measurable g) :
    𝖴₂ := by
  have hh := integral_map (μ := observationLaw θ) measurable_fst.aemeasurable
    hg.aestronglyMeasurable
  rw [(𝔙 observationLaw_fst_measurePreserving).map_eq] at hh
  exact hh.symm

𝗇 𝔊 (Prod.fst ⁻¹' A).indicator
𝗃 𝔤 ∫ z, 𝔊 ἀ z ∂observationLaw θ
𝗃 𝔥 𝔙 ἀ A hA
theorem observationLaw_localized_regression_first C
    θ (hθ : 𝔎)
    A (hA : MeasurableSet A) :
    𝔤 Prod.snd =
      𝔤 𝔅 := by
  rw [𝔥 observationLaw_localized_first_integral]
  have hh := 𝔙 observationLaw_covariate_integral (A.indicator θ.regression)
    $ hθ.2.1.indicator hA
  tauto

𝗇 𝔖 fun x => θ.regression x ^ 2
theorem observationLaw_localized_regression_second C
    θ (hθ : 𝔎)
    A (hA : MeasurableSet A) :
     ∫ z, 𝔊 (fun z : Observation d => z.2 ^ 2) z
      ∂observationLaw θ =
       ∫ z, 𝔊 (fun z : Observation d => θ.regression z.1 ^ 2) z
        ∂observationLaw θ + θ.variance * 𝘐₂ A := by
  rw [𝔥 observationLaw_localized_second_integral]
  have hh := 𝔙 observationLaw_covariate_integral
    (A.indicator 𝔖) $ (hθ.2.1.pow_const 2).indicator hA
  have hc : ∫ z : Observation d, 𝔊
      (fun z => θ.regression z.1 ^ 2) z ∂observationLaw θ =
      ∫ x, A.indicator 𝔖 x ∂designLaw θ := by
    assumption
  rw [hc, integral_indicator hA, integral_indicator hA]
  let := 𝔙 designLaw_isProbability
  rw [integral_add (𝔙 designLaw_regression_memLp_two).integrable_sq.restrict
      $ integrable_const θ.variance , integral_const]
  simp
  ring

𝗇 𝔘 ∫ z, 𝔒 ∂ 𝔄
𝗇 𝔞 fun z => θ.regression z.1
𝗃 𝔢 ∫ z, pairWindowScore 𝔉 ἀ 0 z ∂ 𝔄
/-- Conditional centering makes the score's population mean exactly the
same-cell squared regression increment. -/
theorem regularPairScore_mean_eq_signal C
    θ (hθ : 𝔎) k hk :
    𝔘 =
      𝔢 𝔅 := by
  let := 𝔏
  rw [regularPairScore,
    𝔣 pairWindowScore_integral
      𝔙 observationLaw_response_memLp_two,
    𝔚 pairWindowScore_integral
      𝔞 (hθ.2.1.comp measurable_fst) 0
      𝔙 observationLaw_regression_memLp_two]
  apply Finset.sum_congr rfl
  intro c hc
  let A := 𝔇
  have hA : MeasurableSet A :=
    𝔍
  have hsecond := 𝔥 observationLaw_localized_regression_second
  rw [𝔐,
    𝔛 regularObservationLabel_fiber c, 𝔥 observationLaw_localized_regression_first, hsecond]
  dsimp [regularGridProbability]
  ring

def regularGridOscillation (C : ModelConstants d) (k : ℕ) : ℝ :=
   2 * (𝙊 + 1) * C.holderBound *
    (Real.sqrt d * (1 / 𝙦)) ^ elementarySmoothness C

theorem regularPairScore_mean_nonneg C
    (θ : RegressionParameter d) (hθ : 𝔎) k hk :
    0 ≤ 𝔘 := by
  rw [𝔡 regularPairScore_mean_eq_signal]
  apply integral_nonneg
  intro z
  unfold pairWindowScore
  split_ifs <;> simp <;> positivity

theorem regularPairSignal_integrable C
    θ (hθ : 𝔎) k hk :
    Integrable (pairWindowScore 𝔉
      𝔅 0)
      𝔄 := by
  let := 𝔏
  let R := 𝔅
  have h2 := (𝔙 observationLaw_regression_memLp_two).integrable_sq
  have hd : Integrable (fun z =>
      R z.1 ^ 2 + R z.2 ^ 2) 𝔄 :=
    (h2.comp_fst _).add $ h2.comp_snd _
  apply hd.mono'
    (pairWindowScore_measurable _ 𝔈
      R (hθ.2.1.comp measurable_fst) 0).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [abs_zero, add_zero, Real.norm_eq_abs] using
    pairWindowScore_abs_le 𝔉 R 0 z

𝗇 𝔗 regularGridOscillation C k ^ 2 / 2
theorem regularPairScore_mean_le C
    (θ : RegressionParameter d) (hθ : 𝔎) k hk :
    𝔘 ≤
      𝔗 * 𝘬₁ := by
  let := 𝔏
  have hcube := 𝔔
  rw [𝔡 regularPairScore_mean_eq_signal]
  have hD := (𝔚 sameLabelKernel_memLp).integrable 𝖠₄
  have hb : 𝔢 𝔞 ≤
      ∫ z, 𝔗 *
        sameLabelKernel 𝔉 z
        ∂ 𝔄 := by
    apply integral_mono_ae 𝔡 regularPairSignal_integrable
      $ hD.const_mul _
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcube,
      Measure.quasiMeasurePreserving_snd.ae hcube] with z hz1 hz2
    by_cases he : 𝔛 regularObservationLabel z.1 = 𝔛 regularObservationLabel z.2
    · have hm := 𝔡 regular_grid_same_cell_regression_difference
        z.1.1 z.2.1 hz1 hz2 he
      have hs := 𝗂 hm 2
      simp only [sq_abs] at hs
      simp only [pairWindowScore, sameLabelKernel, ite_eq_left he, sub_zero, mul_one]
      bound
    · simp [pairWindowScore, sameLabelKernel, he]
  rw [integral_const_mul, 𝔚 sameLabelKernel_integral] at hb
  simpa only [𝔠, regularGridCollisionMass] using hb
