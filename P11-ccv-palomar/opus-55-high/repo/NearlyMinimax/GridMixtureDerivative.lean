module

public import NearlyMinimax.LowMixtureDerivative
public import NearlyMinimax.LowSmoothnessGridExperiment
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The design-integrated derivative for the paper's actual grid prior. -/

𝚫
open scoped Topology BigOperators
𝚨

𝗇 𝔇 gridWindowCount d k
𝗇 𝔉 𝙇
def gridSampleField (d k n : ℕ) (η : ℝ) (x : 𝔉) :
    (Fin 𝔇 → Fin 3) → 𝙔 :=
  fun ξ i => indexedGridField d k η ξ $ x i

𝗃 𝔜 ἀ d k n
𝗇 𝔅 𝔜 gridSampleField η
theorem gridSampleField_measurable d k n η :
    Measurable 𝔅 := by
  apply measurable_pi_lambda
  intro ξ
  apply measurable_pi_lambda
  intro i
  have h := (indexedGridField_continuous d k η ξ).measurable.comp
    $ show Measurable fun x : 𝔉 => x i from measurable_pi_apply i
  exact h

𝗇 𝔑 𝙼₂ $ x i
𝗇 𝔔 𝗼
theorem gridSampleField_norm_le d k n η (hη : 𝔔)
    x : ‖𝔅 x‖ ≤ 𝖥 * η := by
  apply (pi_norm_le_iff_of_nonneg 𝖠₃ ).mpr
  intro ξ
  apply (pi_norm_le_iff_of_nonneg 𝖠₃ ).mpr
  intro i
  simpa only [gridSampleField, Real.norm_eq_abs] using 𝔑

𝗇 𝔓 𝔉 → 𝙈 → ℝ
𝗃 𝔛 ἀ 𝔇 n a v η t (𝔅 x) $ T x
def gridMixtureExpectation (d k n : ℕ) (a v η t : ℝ)
    (T : 𝔓) : ℝ :=
  ∫ x, 𝔛 finiteExperimentExpectation ∂Measure.pi 𝘂

𝗇 𝔏 v - 𝙎 * t
def gridMixtureScoreObservable (d k n : ℕ) (a v η t : ℝ)
    (T : 𝔓)
    (x : 𝔉) : ℝ :=
  ∑ ξ, activationProductPrior 𝔇 t ξ * ∑ y,
    finiteResponseLikelihood 𝔇 n a 𝔏
      (𝔅 x) ξ y * T x y *
    finiteExperimentScore 𝔇 n a 𝔏 η
      (𝔅 x) ξ y

𝗇 𝔈 (𝖥 + 2) * η ≤ P.ρ
𝗇 𝔖 𝙎 ≤ P.ρ
𝗇 𝔚 t ∈ 𝗃
theorem grid_response_likelihood_pos (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) k n η t
    (hη : 𝔔) (ht : 𝔚)
    (hfield : 𝔈) (hvariance : 𝔖)
    x ξ y :
    0 < finiteResponseLikelihood 𝔇 n P.a (P.v - 𝙎 * t)
      (𝔅 x) ξ y := by
  apply Finset.prod_pos
  intro i _
  exact P.c_pos.trans_le $ (P.path_legality η t _ ht hvariance $ (𝔑).trans 𝖥₃ ).2.2.1 $ y i

𝗇 𝔄 Measure.pi 𝙮₁
𝗇 𝔊 𝔜 gridMixtureScoreObservable P.a P.v η t T
𝗇 𝔍 Filter.Eventually.of_forall $ 𝔜 gridSampleField_norm_le η hη
𝗇 𝔎 grid_response_likelihood_pos C P k n η t hη ht hfield hvariance
𝗇 𝔐 ‖T x‖ ≤ M
𝗇 𝔒 ∀ᵐ x ∂𝔄, 𝔐
𝗇 𝔗 ∫ x, 𝔊 x ∂𝔄
𝗇 𝔘 𝗝 * η
𝗇 𝔙 𝔜 gridSampleField_measurable η
/-- The actual grid-prior mean has the exact integrated score derivative.
Every domination, measurability, and positivity requirement follows from
the grid construction and the original ternary legality neighborhood. -/
theorem grid_mixture_expectation_hasDerivAt (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) k n η t M
    (hη : 𝔔) (ht : 𝔚)
    (hfield : 𝔈) (hvariance : 𝔖)
    T (hT : Measurable T)
    (hTBound : 𝔒) :
    Integrable 𝔊
        𝔄 ∧
      HasDerivAt (fun u => 𝔜 gridMixtureExpectation P.a P.v η u T)
        𝔗 t := by
  let _ := cubeVolume_isProbability d
  exact finite_experiment_integrated_score_hasDerivAt
    𝔄 𝔇 n P.a P.v η t
    𝔘 M 𝔅 T
    𝔙 hT
    𝔍 hTBound
    $ Filter.Eventually.of_forall 𝔎

theorem grid_mixture_raw_derivative_continuous d k n a v η M (hη : 𝔔)
    T (hT : Measurable T)
    (hTBound : 𝔒) :
    Continuous fun t => ∫ x, 𝔛 finiteExperimentRawDerivative ∂𝔄 := by
  let _ := cubeVolume_isProbability d
  exact finite_experiment_integrated_raw_derivative_continuous
    𝔄 𝔇 n a v η 𝔘 M
    𝔅 T 𝔙 hT
    𝔍 hTBound

/-- The score-observable derivative along the actual probability path is
interval integrable, with no regularity assumption on the bounded observable. -/
theorem grid_mixture_score_observable_intervalIntegrable (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) k n η M
    (hη : 𝔔) (hfield : 𝔈) (hvariance : 𝔖)
    T (hT : Measurable T)
    (hTBound : 𝔒) :
    IntervalIntegrable (fun t => 𝔗) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc 𝖠₄
  apply (𝔜 grid_mixture_raw_derivative_continuous P.a P.v η M hη T hT hTBound).continuousOn.congr
  intro t ht
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact (finite_experiment_raw_derivative_eq_score 𝔇 n P.a P.v η t
    (𝔅 x) (T x)
    $ 𝔎 x ).symm
