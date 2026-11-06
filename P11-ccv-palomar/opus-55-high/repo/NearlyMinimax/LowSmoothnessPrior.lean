module

public import NearlyMinimax.ScoreSupport
public import NearlyMinimax.ParametricConstants
public import NearlyMinimax.TernaryMeasure
public import NearlyMinimax.ModelRegularity
public import NearlyMinimax.PathRisk
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! # The actual low-smoothness ternary prior

This file connects the finite likelihood construction to the original model.
In the order-zero regime a globally bounded Hölder regression gives an
admissible extension on every extension domain in `ModelConstants`.
-/

𝚴
𝚮

𝚨

𝗃 𝔓 ἀ a (F x) V
𝗇 𝔄 𝔓 ternaryMass y
theorem ternaryMass_measurable_comp [MeasurableSpace α]
    a V (F : 𝘬) (hF : Measurable F) y :
    Measurable fun x => 𝔄 := by
  fin_cases y <;> simp [ternaryMass] <;> fun_prop

𝗇 𝔉 𝗐₂ - F x
𝗇 𝔒 ∑ y : Fin 3, ENNReal.ofReal 𝔄 • Measure.dirac 𝔉
𝗃 𝔔 ἀ a V F
/-- The errors have actual values `-a-f(x)`, `-f(x)`, and `a-f(x)`. -/
def ternaryErrorKernel [MeasurableSpace α]
    (a V : ℝ) (F : 𝘬) (hF : Measurable F) : Kernel α ℝ where
  toFun x := 𝔒
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hs]
    apply Finset.measurable_sum
    intro y _
    exact (ENNReal.measurable_ofReal.comp $ 𝔔 ternaryMass_measurable_comp hF y ).mul
      $ measurable_const.indicator $ (measurable_const.sub hF) hs

𝗇 𝔅 𝗅 * V + (6 * V - 3 * 𝗅) * F x ^ 2 + 3 * F x ^ 4
𝗇 𝔖 𝙞
𝗇 𝔘 ∀ x y, 0 ≤ 𝔄
𝗇 𝔞 𝔔 ternaryErrorKernel hF
section

variable [MeasurableSpace α]
    (a)
    (V)

𝗇 𝔈 𝔞 x
theorem ternaryErrorKernel_apply F hF (x : α) :
    𝔈 = 𝔒 := rfl

theorem ternaryErrorKernel_markov (F : 𝘬) hF (ha : 𝔖)
    (hp : 𝔘) :
    IsMarkovKernel 𝔞 := by
  constructor
  intro x
  constructor
  simp only [ternaryErrorKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    𝚉₁, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => hp x y , 𝔓 ternary_normalized ha]
  simp

theorem ternary_error_integrable F hF (x : α) (G : 𝘓) :
    Integrable G 𝔈 := by
  apply integrable_finsetSum_measure.mpr
  intro y _
  exact (integrable_dirac 𝖢₄ ).smul_measure ENNReal.ofReal_ne_top

𝗇 𝔑 ∀ y, 0 ≤ 𝔄
theorem ternary_error_integral F hF (x : α)
    (hp : 𝔑) (G : 𝘓) :
     ∫ u, G u ∂ 𝔈 =
      ∑ y, 𝔄 * G 𝔉 := by
  rw [ternaryErrorKernel_apply, integral_finsetSum_measure]
  · simp_all
  · intro y _
    exact (integrable_dirac 𝖢₄ ).smul_measure ENNReal.ofReal_ne_top

𝗇 𝔍 𝔔 ternary_error_integral hF x hp
𝗃 𝔠 ∫ u, ἀ ∂ 𝔈
theorem ternary_error_mean F hF (x : α)
    (ha : 𝔖) (hp : 𝔑) :
    𝔠 u = 0 := by
  rw [𝔍]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hm := 𝔓 ternary_mean ha
  change ∑ y, 𝔄 * 𝗐₂ = F x at hm
  rw [hm, 𝔓 ternary_normalized ha]
  ring

theorem ternary_error_variance F hF (x : α)
    (ha : 𝔖) (hp : 𝔑) :
    𝔠 𝙟₁ = V := by
  rw [𝔍]
  exact 𝔓 ternary_variance ha

theorem ternary_error_fourth F hF (x : α)
    (ha : 𝔖) (hp : 𝔑) :
     ∫ u, u ^ 4 ∂ 𝔈 =
      𝔅 := by
  rw [𝔍]
  exact 𝔓 ternary_fourth_central_moment ha

end

𝗇 𝔐 euclideanNorm 𝘌
𝗇 𝔗 F x - F y
𝗇 𝔙 𝙀
𝗇 𝔚 M + H
/-- Global bounds imply the paper's exact order-zero norm bound on any domain. -/
theorem holderNorm_order_zero_of_global_bounds U
    (F : 𝔙) α M H (hM : 𝙷) (hH : 𝖹₁)
    (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |𝔗| ≤ H * 𝔐 ^ α) :
    𝘍₂ 0 α ≤ ENNReal.ofReal 𝔚 := by
  have hs : derivativeSup U F ≤ ENNReal.ofReal M := by
    apply iSup_le
    simp_all
  have hh : holderSeminorm U F α ≤ ENNReal.ofReal H := by
    apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hxy : 𝘱₁
    · simp_all
    · simp only [𝚙₁]
      apply ENNReal.ofReal_le_ofReal
      exact 𝘴
          $ hmod x y
  rw [holderNorm_order_zero, ENNReal.ofReal_add hM hH]
  bound

/-- The genuine original-model parameter with uniform design and ternary errors. -/
def uniformTernaryParameter (a V : ℝ) (F : 𝔙)
    (hF : Measurable F) (ha : 𝔖) (hp : 𝔘) :
    RegressionParameter d := {
  density := 𝙃
  regression := F
  variance := V
  errors := 𝔞
  errors_markov := 𝔔 ternaryErrorKernel_markov hF ha hp }

𝗇 𝔎 𝔔 ternary_error_integrable hF.measurable x _
𝗃 𝔟 𝔔 ἀ hF.measurable x ha $ hp x
/-- Order-zero legality uses global bounds, so it is independent of the
size or shape of the model's prescribed extension domain. -/
theorem uniformTernaryParameter_admissible_order_zero (C : ModelConstants d)
    a V F (hF : Continuous F) (horder : C.order = 0)
    ha hp
    (hVlo : C.varianceLower ≤ V) (hVhi : V ≤ C.varianceUpper)
    M H (hM : 𝙷) (hH : 𝖹₁) (hbudget : 𝔚 ≤ C.holderBound)
    (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |𝔗| ≤ H * 𝔐 ^ C.smoothness)
    (hfourth : ∀ x, 𝔅 ≤ C.fourthBound) :
    Admissible C $ 𝔔 uniformTernaryParameter hF.measurable ha hp := by
  refine ⟨measurable_const, hF.measurable, ?_, ?_, ?_, hVlo, hVhi, ?_⟩
  · exact Filter.Eventually.of_forall fun _ =>
      ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩
  · simp only [uniformTernaryParameter, ENNReal.ofReal_one, lintegral_const, one_mul]
    exact cubeVolume_univ d
  · refine ⟨F, 𝗓₂, ?_, ?_⟩
    · simpa [horder] using
        (contDiffOn_zero.mpr hF.continuousOn : ContDiffOn ℝ 0 F C.domain)
    · have hα : C.alpha = C.smoothness := by simp [ModelConstants.alpha, horder]
      rw [horder, hα]
      exact (holderNorm_order_zero_of_global_bounds C.domain F C.smoothness M H hM hH
        hsup hmod).trans $ ENNReal.ofReal_le_ofReal hbudget
  · apply Filter.Eventually.of_forall
    intro x
    refine ⟨ 𝔎,
      𝔎,
      𝔎,
      𝔟 ternary_error_mean,
      𝔟 ternary_error_variance, ?_⟩
    exact (𝔟 ternary_error_fourth).trans_le $ hfourth x

𝗇 𝔊 fun y => (y - f) ^ 4
/-- Uniform interior margins for nonzero regression fields and the variance path. -/
structure LowSmoothnessTernaryConstants {d : ℕ} (C : ModelConstants d) where
  a : ℝ
  v : ℝ
  ρ : ℝ
  c : ℝ
  a_pos : 𝙆
  ρ_pos : 𝘢₁
  c_pos : 𝘝
  legal : ∀ f V, |f| ≤ ρ → |V - v| ≤ ρ →
    C.varianceLower < V ∧ V < C.varianceUpper ∧
      (∀ y, c ≤ ternaryMass a f V y) ∧
      ternaryExpectation a f V 𝔊 ≤ C.fourthBound

theorem lowSmoothnessTernaryConstants_exists (C : ModelConstants d) :
    Nonempty $ LowSmoothnessTernaryConstants C := by
  obtain ⟨P⟩ := parametricTernaryConstants_exists C
  let v := (P.l + P.r) / 2
  have hv : 0 < v := by dsimp [v]; linarith [P.l_pos, P.interval]
  have hVl : C.varianceLower < v := by dsimp [v]; linarith [P.lower_le, P.interval]
  have hVr : v < C.varianceUpper := by dsimp [v]; linarith [P.upper_le, P.interval]
  have hfourth : P.a ^ 2 * v < C.fourthBound := by
    have hmid : v < P.r := by dsimp [v]; linarith [P.interval]
    exact (mul_lt_mul_of_pos_left hmid $ sq_pos_of_pos P.a_pos ).trans_le P.fourth_le
  obtain ⟨ρ, c, hρ, hc, hlegal⟩ := ternary_admissible_neighborhood P.a v
    C.varianceLower C.varianceUpper C.fourthBound P.a_pos hv (by dsimp [v]; linarith [P.variance_lt_square, P.interval]) hVl hVr hfourth
  exact ⟨⟨P.a, v, ρ, c, P.a_pos, hρ, hc, hlegal⟩⟩

namespace LowSmoothnessTernaryConstants

variable {d : ℕ} {C : ModelConstants d} (P : LowSmoothnessTernaryConstants C)

𝗇 𝔛 𝙎
def variancePath (η t : ℝ) : ℝ := P.v - 𝔛 * t

𝗇 𝔇 P.variancePath η t
𝗇 𝔜 t ∈ 𝗃
theorem variance_path_distance η t (ht : 𝔜) :
    |𝔇 - P.v| ≤ 𝔛 := by
  simp only [variancePath, sub_sub_cancel_left, abs_neg, abs_mul, 𝚓₁,
    abs_of_nonneg ht.1]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 $ sq_nonneg η

theorem path_legality η t f (ht : 𝔜)
    (hη : 𝔛 ≤ P.ρ) (hf : |f| ≤ P.ρ) :
    C.varianceLower < 𝔇 ∧ 𝔇 < C.varianceUpper ∧
      (∀ y, P.c ≤ ternaryMass P.a f 𝔇 y) ∧
      ternaryExpectation P.a f 𝔇 𝔊 ≤ C.fourthBound :=
  P.legal f 𝔇 hf $ (P.variance_path_distance η t ht).trans hη

𝗇 𝔏 P.path_legality η t (F x) ht hη $ hf x
/-- A canonical actual-model parameter along the variance path. -/
def pathParameter (F : 𝔙) (hF : Continuous F) (η t : ℝ)
    (ht : t ∈ Icc 𝙋 1) (hη : 𝔛 ≤ P.ρ) (hf : ∀ x, |F x| ≤ P.ρ) :
    RegressionParameter d :=
  uniformTernaryParameter P.a 𝔇 F hF.measurable P.a_pos.ne'
     fun x y => P.c_pos.le.trans $ (𝔏).2.2.1 y

theorem pathParameter_admissible_order_zero F hF
    η t ht hη hf
    (horder : C.order = 0) M H (hM : 𝙷) (hH : 𝖹₁)
    (hbudget : 𝔚 ≤ C.holderBound) (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |𝔗| ≤ H * 𝔐 ^ C.smoothness) :
    Admissible C $ P.pathParameter F hF η t ht hη hf := by
  have hlegal x := 𝔏
  apply uniformTernaryParameter_admissible_order_zero C P.a 𝔇 F hF horder P.a_pos.ne'
    _ (hlegal 0).1.le (hlegal 0).2.1.le M H hM hH hbudget hsup hmod
  intro x
  have hf4 := (hlegal x).2.2.2
  rw [ternary_fourth_central_moment P.a (F x) 𝔇 P.a_pos.ne'] at hf4
  exact hf4
