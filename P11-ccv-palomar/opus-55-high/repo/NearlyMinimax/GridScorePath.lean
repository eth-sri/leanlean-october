module

public import NearlyMinimax.GridMixtureDerivative
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Measurability and integrated square-root score budget for the actual grid path. -/

𝚫
open scoped Topology BigOperators
𝚨

𝗇 𝔑 𝙎
𝗇 𝔄 v - 𝔑 * z.1
𝗇 𝔉 gridWindowCount d k
𝗇 𝔊 ℝ × 𝙇
𝗇 𝔒 𝙖
𝗃 𝔔 ἀ d k n
theorem grid_full_score_energy_joint_measurable d k n a v η
    ξ :
    Measurable fun z : 𝔊 =>
      𝔔 gridFullScoreEnergy a 𝔄 η ξ z.2 := by
  let f : 𝔊 →
      (Fin 𝔉 → Fin 3) → 𝙔 :=
    fun z => latentRegression 𝔉 n η 𝖾 $ 𝔔 gridSampleWeights z.2
  have hV : Measurable fun z : 𝔊 => 𝔄 := 𝖦₃
  have hf ξ' i :
      Measurable fun z => f z ξ' i := by
    simpa only [f, grid_latent_regression_eq, Function.comp_def] using (indexedGridField_continuous d k η ξ').measurable.comp $ 𝘜 measurable_snd
  have hq ξ' i y :
      Measurable fun z => ternaryMass a (f z ξ' i) 𝔄 y := by
    exact (ternaryMass_joint_continuous a y).measurable.comp $ (hf ξ' i).prodMk hV
  have hL ξ' y :
      Measurable fun z => finiteResponseLikelihood 𝔉 n a
        𝔄 (f z) ξ' y :=
    Finset.measurable_prod _ fun i _ => hq ξ' i $ y i
  have hU y i :
      Measurable fun z => finiteResponseVarianceTerm 𝔉 n a
        𝔄 (f z) ξ y i :=
    𝗄₂
  have hD y j :=
    (((hL (Function.update ξ j 2) y).const_mul 𝔒).add
      $ (hL (Function.update ξ j 0) y).const_mul 𝔒 ).sub $ hL (Function.update ξ j 1) y
  have hR y :
      Measurable fun z => finiteExperimentScore 𝔉 n a
        𝔄 η (f z) ξ y :=
    ((Finset.measurable_sum _ fun j _ => hD y j ).sub
      $ (Finset.measurable_sum _ fun i _ => hU y i ).const_mul 𝔑 ).div $ hL ξ y
  exact 𝘭₁

theorem grid_prior_score_energy_path_measurable d k n a v η :
    Measurable $ 𝔔 gridPriorScoreEnergy a v η := by
  let _ := cubeVolume_isProbability d
  apply Finset.measurable_sum
  intro ξ _
  have hPrior :=
    (continuous_iff_continuousAt.mpr fun t =>
      (activation_product_prior_hasDerivAt 𝔉 t ξ).continuousAt ).measurable
  have hInt := (𝔔 grid_full_score_energy_joint_measurable a v η ξ).stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi 𝙮₁)
  exact hPrior.mul hInt.measurable

def gridUniformScoreBudget {d : ℕ} {C : ModelConstants d}
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η : ℝ) : ℝ :=
  𝘮₁ * 𝚍 * 𝗩 / 𝙦 ^ d

𝗇 𝔅 Real.sqrt $ 𝔔 gridPriorScoreEnergy P.a P.v η t
𝗇 𝔇 n * (2 / 𝙦) ^ d ≤ 1
𝗇 𝔈 (𝖥 + 2) * η ≤ P.ρ
𝗇 𝔍 gridUniformScoreBudget P k n η
𝗇 𝔎 grid_prior_score_energy_bound C P k n η t hk hη ht hfield hvariance hmean
𝗇 𝔏 fun t => 𝔅
theorem grid_sqrt_score_energy_intervalIntegrable {d } (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) η (hk : 𝗽₁)
    (hη : 𝗼) (hfield : 𝔈) (hvariance : 𝔑 ≤ P.ρ)
    (hmean : 𝔇) :
    IntervalIntegrable 𝔏 volume 0 1 := by
  have hMeas : Measurable 𝔏 :=
    Real.continuous_sqrt.measurable.comp $ 𝔔 grid_prior_score_energy_path_measurable P.a P.v η
  have hI : IntegrableOn 𝔏 (Icc 0 1) volume := by
    apply Integrable.of_bound hMeas.aestronglyMeasurable $ Real.sqrt 𝔍
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg $ Real.sqrt_nonneg _ ]
    exact Real.sqrt_le_sqrt 𝔎
  apply IntegrableOn.intervalIntegrable
  simpa

𝗇 𝔐 ∫ t in (0)..1, 𝔅
𝗃 𝔓 ἀ C P k n η hk hη hfield hvariance hmean
theorem grid_sqrt_score_energy_integral_le {d } (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) η (hk : 𝗽₁)
    (hη : 𝗼) (hfield : 𝔈) (hvariance : 𝔑 ≤ P.ρ)
    (hmean : 𝔇) :
    𝔐 ≤
      Real.sqrt 𝔍 := by
  have h := intervalIntegral.integral_mono_on  𝖠₄  𝔓 grid_sqrt_score_energy_intervalIntegrable
    (intervalIntegrable_const : IntervalIntegrable (fun _ => Real.sqrt 𝔍) volume 0 1)
     fun t ht => Real.sqrt_le_sqrt 𝔎
  simp_all

theorem grid_sqrt_score_energy_integral_le_one (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) η (hk : 𝗽₁)
    (hη : 𝗼) (hfield : 𝔈) (hvariance : 𝔑 ≤ P.ρ)
    (hmean : 𝔇) (hbudget : 𝔍 ≤ 1) :
    𝔐 ≤ 1 := by
  apply (𝔓 grid_sqrt_score_energy_integral_le).trans
  simpa
