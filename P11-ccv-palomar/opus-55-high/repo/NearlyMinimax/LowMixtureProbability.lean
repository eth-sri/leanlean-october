module

public import NearlyMinimax.LowSmoothnessGridExperiment
public import NearlyMinimax.PathRisk
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual augmented design--activation--response probability measures.
The conditional finite weights and scores are those of the low-smoothness
experiment. Markov normalization and all integral identities are proved. -/
𝛏
𝚮
𝚨
𝚩
𝚱

𝗇 𝔳 Fin m → Fin 3
abbrev LowMixtureMarks (m n : ℕ) := 𝔳 × 𝙈

𝗇 𝔇 α → 𝔳 → 𝙔
𝗇 𝔔 LowMixtureMarks m n
𝗃 𝔮 ἀ m n a V
𝗇 𝔧 𝔮 finiteResponseLikelihood $ f x
def lowMixtureWeight (m n : ℕ) (a V t : ℝ)
    (f : 𝔇) (x : α)
    (z : 𝔔) : ℝ :=
  activationProductPrior m t z.1 * 𝔧 z.1 z.2

𝗇 𝔪 f x ξ i
𝗃 𝔰 fun x => ἀ
𝗇 𝔊 ∀ ξ i, Measurable 𝔰 𝔪
𝗇 𝔑 𝔮 lowMixtureWeight t f x z
𝗇 𝔲 ternaryMass_measurable_comp a V _
theorem lowMixtureWeight_measurable [MeasurableSpace α]
    m n a V t (f : 𝔇)
    (hf : 𝔊) z :
    Measurable 𝔰 𝔑 := (Finset.measurable_prod _ fun i _ =>
    𝔲 (hf z.1 i) $ z.2 i ).const_mul _

𝗇 𝔥 ∑ z : 𝔔, ENNReal.ofReal 𝔑 • Measure.dirac z
𝗃 𝔴 𝔮 ἀ t f hf
def lowMixtureIndexKernel [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : 𝔇)
    (hf : 𝔊) : Kernel α 𝔔 where
  toFun x := 𝔥
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun z _ =>
      (ENNReal.measurable_ofReal.comp $ 𝔴 lowMixtureWeight_measurable z ).mul_const _

𝗇 𝔘 𝔴 lowMixtureIndexKernel x
theorem lowMixtureIndexKernel_apply [MeasurableSpace α]
    m n a V t f
    hf (x : α) :
    𝔘 =
      𝔥 := rfl

𝗇 𝔄 ∀ x ξ i y, 0 ≤ ternaryMass a 𝔪 V y
𝗇 𝔉 t ∈ 𝗃
theorem lowMixtureWeight_nonneg m n a V t
    f (ht : 𝔉)
    (hp : 𝔄) (x : α) z :
    0 ≤ 𝔑 :=
  𝔮 finite_experiment_joint_nonnegative t (f x) ht.1 ht.2 (hp x) z.1 z.2

𝗇 𝔖 𝙞
𝗇 𝔛 𝔴 lowMixtureIndexKernel
𝗇 𝔦 𝔮 lowMixtureWeight_nonneg t f ht hp x
theorem lowMixtureIndexKernel_markov [MeasurableSpace α]
    m n a V t (f : 𝔇)
    hf (ha : 𝔖)
    (ht : 𝔉) (hp : 𝔄) :
    IsMarkovKernel 𝔛 := by
  constructor
  intro x
  constructor
  simp only [lowMixtureIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    𝚉₁, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun z _ =>
    𝔦 z ]
  simp only [lowMixtureWeight, Fintype.sum_prod_type]
  rw [𝔮 finite_experiment_joint_normalized t (f x) ha]
  simp

𝗇 𝔅 𝔧 ξ y
𝗇 𝔐 activationProductPrior m t ξ
𝗃 𝕭 ∫ z, H z ∂ ἀ
theorem lowMixtureIndexKernel_integral [MeasurableSpace α]
    m n a V t f
    hf
    (ht : 𝔉) (hp : 𝔄)
    (x : α) (H : 𝔔 → ℝ) :
    𝕭 𝔘 =
      ∑ ξ, 𝔐 *
        ∑ y, 𝔅 * H (ξ, y) := by
  rw [lowMixtureIndexKernel_apply, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, lowMixtureWeight, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    have hpos : 0 ≤ 𝔐 * 𝔅 :=
      𝔦 (ξ, y)
    rw [ENNReal.toReal_ofReal hpos]
    ring
  · intro z hz
    exact (integrable_dirac 𝖢₄ ).smul_measure ENNReal.ofReal_ne_top

𝗇 𝔱 α × 𝔔
def lowMixtureLaw [MeasurableSpace α]
    (μ : Measure α) (m n : ℕ) (a V t : ℝ)
    (f : 𝔇)
    (hf : 𝔊) : Measure 𝔱 :=
  μ.compProd 𝔛

𝗃 𝔯 ἀ μ m n a V t f hf
𝗇 𝔈 𝔯 lowMixtureLaw
𝗇 𝔭 𝔴 lowMixtureIndexKernel_markov ha ht
𝗇 𝔓 𝔭 hp
theorem lowMixtureLaw_probability [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] m n a V t
    f
    hf (ha : 𝔖)
    (ht : 𝔉) (hp : 𝔄) :
    IsProbabilityMeasure 𝔈 := by
  let := 𝔓
  unfold lowMixtureLaw
  infer_instance

𝗇 𝔍 H (x, ξ, y)
𝗇 𝔞 𝔴 lowMixtureIndexKernel_integral ht hp
theorem lowMixtureLaw_integrable_of_weighted_norm [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] m n a V t
    f
    hf (ha : 𝔖)
    (ht : 𝔉) (hp : 𝔄)
    (H : 𝔱 → ℝ) (hH : Measurable H)
    (hNorm : Integrable (fun x => ∑ ξ, 𝔐 *
      ∑ y, 𝔅 * |𝔍|) μ) :
    Integrable H 𝔈 := by
  let := 𝔓
  apply (Measure.integrable_compProd_iff hH.aestronglyMeasurable).mpr
  constructor
  · simp
  · simp_rw [𝔞,
      Real.norm_eq_abs]
    exact hNorm

𝗇 𝔟 ∑ y, 𝔅 * 𝔍
𝗇 𝔡 𝕭 𝔈
𝗃 𝔷 ∑ ξ, 𝔐 * ἀ
theorem lowMixtureLaw_integral [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] m n a V t
    f
    hf (ha : 𝔖)
    (ht : 𝔉) (hp : 𝔄)
    H
    (hH : Integrable H 𝔈) :
    𝔡 =
      ∫ x, 𝔷 𝔟 ∂μ := by
  let := 𝔓
  rw [lowMixtureLaw, Measure.integral_compProd hH]
  simp_rw [𝔞]

theorem finiteResponseLikelihood_measurable_comp [MeasurableSpace α]
    m n a V (f : 𝔇)
    (hf : 𝔊)
    ξ y :
    Measurable 𝔰 𝔅 := Finset.measurable_prod _ fun i _ =>
    𝔲 (hf ξ i) $ y i

𝗃 𝕬 𝔮 ἀ η
𝗇 𝔏 𝕬 finiteExperimentScore (f x) ξ y
theorem finiteExperimentScore_measurable_comp [MeasurableSpace α]
    m n a V η (f : 𝔇)
    (hf : 𝔊)
    ξ y :
    Measurable 𝔰 𝔏 := by
  have hL := 𝔮 finiteResponseLikelihood_measurable_comp f hf
  have hU i : Measurable fun x =>
      𝔮 finiteResponseVarianceTerm (f x) ξ y i := (Finset.measurable_prod _ fun l _ =>
      𝔲 (hf ξ l) $ y l ).const_mul _
  have hD j : Measurable fun x => latentDifference m j
      (fun ξ' => 𝔧 ξ' y) ξ := by
    unfold latentDifference
    fun_prop
  unfold finiteExperimentScore finiteExperimentScoreNumerator
  fun_prop

def lowMixtureScore (m n : ℕ) (a V η : ℝ)
    (f : 𝔇) (z : 𝔱) : ℝ :=
  𝕬 finiteExperimentScore (f z.1) z.2.1 z.2.2

𝗇 𝔨 𝕬 lowMixtureScore f
𝗇 𝔜 𝔨
theorem lowMixtureScore_measurable [MeasurableSpace α]
    m n a V η (f : 𝔇)
    (hf : 𝔊) :
    Measurable 𝔜 := by
  apply measurable_from_prod_countable_left
  intro z
  exact 𝕬 finiteExperimentScore_measurable_comp f hf z.1 z.2

𝗇 𝔠 ∑ y, 𝔅 * 𝔏 ^ 2
def lowMixtureConditionalScoreEnergy (m n : ℕ) (a V η t : ℝ)
    (f : 𝔇) (x : α) : ℝ :=
  𝔷 𝔠

𝗇 𝔒 Integrable (𝕬 lowMixtureConditionalScoreEnergy t f) μ
𝗇 𝔙 𝔨 z
𝗃 𝔵 ἀ μ m n a V η t f
𝗇 𝔢 𝔵 lowMixtureScore_sq_integrable hf ha ht hp
𝗇 𝔣 𝔯 lowMixtureLaw_integrable_of_weighted_norm ha ht hp
section

variable [MeasurableSpace α]
    (μ : Measure α)
    [IsProbabilityMeasure μ]
    (m)
    (n)
    (a)
    (V)
    (η)
    (t)
    (f)
    (hf)
    (ha : 𝔖)
    (ht : 𝔉)
    (hp : 𝔄)
    (hE : 𝔒)

include ha ht hp hE

theorem lowMixtureScore_sq_integrable :
    Integrable (fun z => 𝔙 ^ 2)
      𝔈 := by
  apply 𝔣 _
    $ (𝕬 lowMixtureScore_measurable f hf).pow_const 2
  simpa

theorem lowMixtureScore_memLp_two :
    MemLp 𝔜 2 𝔈 :=
  (memLp_two_iff_integrable_sq (𝕬 lowMixtureScore_measurable f hf).aestronglyMeasurable).mpr
    $ 𝔢 hE

end

section

variable [MeasurableSpace α]

𝗇 𝔎 fun x ξ i y => (hp x ξ i y).le
𝗇 𝔗 ∀ x ξ i y, 0 < ternaryMass a 𝔪 V y
theorem lowMixtureIndexKernel_score_centered m n a V η t f
    hf (ha : 𝔖)
    (ht : 𝔉) (hp : 𝔗)
    (x : α) :
     ∫ z, 𝔨 (x, z)
      ∂ 𝔘 = 0 := by
  rw [𝔴 lowMixtureIndexKernel_integral ht
    𝔎]
  unfold lowMixtureScore
  have hc ξ := 𝕬 finite_experiment_score_centered (f x) ξ ha
     fun y => Finset.prod_pos fun i _ => hp x ξ i $ y i
  simp_all

theorem lowMixtureScore_centered (μ : Measure α) [IsProbabilityMeasure μ] m n a V η t
    f
    hf (ha : 𝔖)
    (ht : 𝔉) (hp : 𝔗)
    (hE : 𝔒) :
     ∫ z, 𝔙 ∂ 𝔈 = 0 := by
  let := 𝔭 𝔎
  let := 𝔯 lowMixtureLaw_probability ha ht 𝔎
  have hi := (𝔵 lowMixtureScore_memLp_two hf ha ht
    𝔎 hE).integrable 𝖠₄
  rw [lowMixtureLaw, Measure.integral_compProd hi]
  simp_rw [𝕬 lowMixtureIndexKernel_score_centered t f hf ha ht hp]
  simp

𝗇 𝔚 fun ξ _ => (hξ ξ).const_mul _
𝗃 𝔶 ∑ ξ, 𝔐 * ∫ x, ἀ ∂μ
𝗇 𝔩 𝔡 = 𝔶 𝔟
𝗇 𝔫 ∀ ξ, Integrable 𝔰 𝔟 μ
/-- Integrate the design first in each latent state, with all integrability
hypotheses stated on genuine finite response expectations. -/
theorem lowMixtureLaw_integral_sum (μ : Measure α) [IsProbabilityMeasure μ] m n a V t
    f
    hf (ha : 𝔖)
    (ht : 𝔉) (hp : 𝔄)
    H
    (hH : Integrable H 𝔈)
    (hξ : 𝔫) :
    𝔩 := by
  rw [𝔯 lowMixtureLaw_integral ha ht hp H hH,
    integral_finsetSum _ 𝔚]
  simp_rw [integral_const_mul]

𝗇 𝔤 𝔯 lowMixtureLaw_integral_sum ha ht hp
theorem lowMixtureLaw_nonneg_integral_sum (μ : Measure α) [IsProbabilityMeasure μ] m n a V t
    f
    hf (ha : 𝔖)
    (ht : 𝔉) (hp : 𝔄)
    (H : 𝔱 → ℝ) (hH : Measurable H) (hnonneg : ∀ z, 0 ≤ H z)
    (hξ : 𝔫) :
    𝔩 := by
  have hNorm : Integrable (fun x => ∑ ξ, 𝔐 * ∑ y,
      𝔅 * |𝔍|) μ := by
    have heq : (fun x => ∑ ξ, 𝔐 * ∑ y,
        𝔅 * |𝔍|) =
         fun x => 𝔷 𝔟 := by
      funext x
      apply Finset.sum_congr rfl
      intro ξ hξ
      congr 1
      apply Finset.sum_congr rfl
      simp_all
    rw [heq]
    fun_prop
  exact 𝔤 H
    (𝔣 H hH hNorm) hξ

𝗇 𝔬 ∀ ξ, Integrable 𝔰 𝔠 μ
theorem lowMixtureConditionalScoreEnergy_integrable (μ : Measure α) m n a V η t
    f
    (hξ : 𝔬) :
    𝔒 :=
  integrable_finsetSum _ 𝔚

theorem lowMixtureScore_sq_integral_eq_sum (μ : Measure α) [IsProbabilityMeasure μ] m n a V η t
    f
    hf (ha : 𝔖)
    (ht : 𝔉) (hp : 𝔄)
    (hξ : 𝔬) :
     ∫ z, 𝔙 ^ 2 ∂ 𝔈 =
      𝔶 𝔠 := by
  apply 𝔤 _
    $ 𝔢
      $ 𝔵 lowMixtureConditionalScoreEnergy_integrable hξ
  exact hξ
