module

public import NearlyMinimax.FairCellSigns
public import NearlyMinimax.FiniteSigmaProbability
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! A genuine probability law for the fair-cell Poisson partition field. -/
𝚵
open scoped ENNReal NNReal
𝚨
𝚩
set_option maxHeartbeats 400000

𝗇 𝔈 Fin n → H
𝗇 𝔍 Fin n → Fin 2
abbrev partitionFieldFiber (H : Type*) (n : ℕ) :=
  𝔈 × (𝔍 → Fin 2)

𝗇 𝔇 partitionFieldFiber H n
abbrev partitionFieldMark (H : Type*) := Σ n : ℕ, 𝔇

𝛝

𝗇 𝔎 fun z => g z $ p z
theorem measurable_variable_finite_eval [MeasurableSpace E]
    [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] [MeasurableSpace B]
    (g : E → I → B) p (hg : Measurable g) (hp : Measurable p) :
    Measurable 𝔎 := by
  intro s hs
  have he : 𝔎 ⁻¹' s =
      ⋃ i, p ⁻¹' {i} ∩ (fun z => g z i) ⁻¹' s := by
    ext z
    simp
  rw [he]
  exact MeasurableSet.iUnion fun i =>
    (hp $ measurableSet_singleton i ).inter $ hg.eval hs

def partitionFieldFiberLaw (μ : Measure H) (n : ℕ) : Measure 𝔇 :=
  (𝖲₂).prod $ cellSignLaw 𝔍

𝗇 𝔊 partitionFieldFiberLaw μ n
instance partitionFieldFiberLaw_probability (μ : Measure H) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure 𝔊 := by
  unfold partitionFieldFiberLaw
  infer_instance

𝗇 𝔔 (𝔊).map $ Sigma.mk n
𝗇 𝔗 Real.exp $ -r
def poissonCellFieldLaw (μ : Measure H) (r : ℝ≥0) : Measure $ partitionFieldMark H :=
  Measure.sum fun n => ENNReal.ofReal (𝔗 * 𝗥₂ ^ n / n.factorial) •
    𝔔

𝗇 𝔏 poissonCellFieldLaw μ r
instance poissonCellFieldLaw_probability (μ : Measure H) [IsProbabilityMeasure μ] (r : ℝ≥0) :
    IsProbabilityMeasure 𝔏 := by
  constructor
  simp only [poissonCellFieldLaw, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, smul_eq_mul]
  have hm n : 𝔔 Set.univ = 1 := by
    simp
  simp_rw [hm, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg fun n => by positivity
    (hasSum_one_poissonMeasure r).summable, (hasSum_one_poissonMeasure r).tsum_eq]
  simp

theorem poissonCellFieldLaw_measurable (μ : Measure H) :
    Measurable $ poissonCellFieldLaw μ := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [poissonCellFieldLaw, Measure.sum_apply _ hs, Measure.smul_apply]
  fun_prop

instance partitionFieldMark_standardBorel [StandardBorelSpace H] :
    StandardBorelSpace $ partitionFieldMark H := sigma_standardBorel_actual

𝗇 𝔉 H → X → Fin 2
𝗇 𝔓 ρ $ h i
def partitionFieldPattern (ρ : 𝔉)
    (h : 𝔈) (x : X) : 𝔍 := fun i => 𝔓 x

def partitionFieldFiberValue (ρ : 𝔉)
    (z : 𝔇) (x : X) : ℝ :=
  fairSignValue $ z.2 $ partitionFieldPattern ρ z.1 x

def poissonCellFieldValue (ρ : 𝔉)
    (z : partitionFieldMark H) (x : X) : ℝ := partitionFieldFiberValue ρ z.2 x

𝗇 𝔑 partitionFieldFiberValue ρ z x
theorem partitionFieldFiberValue_abs ρ
    (z : 𝔇) (x : X) : |𝔑| = 1 :=
  fairSignValue_abs _

𝗇 𝔒 poissonCellFieldValue ρ z x
theorem poissonCellFieldValue_abs ρ
    (z : partitionFieldMark H) (x : X) : |𝔒| = 1 :=
  partitionFieldFiberValue_abs ..

𝗇 𝔄 Measurable $ Function.uncurry ρ
theorem partitionFieldPattern_measurable ρ
    (hρ : 𝔄) n :
    Measurable fun z : 𝔈 × X => partitionFieldPattern ρ z.1 z.2 := by
  apply Measurable.of_eval
  intro i
  change Measurable fun z : 𝔈 × X => ρ (z.1 i) z.2
  fun_prop

𝗃 𝔛 ἀ ρ hρ
theorem partitionFieldFiberValue_measurable ρ
    (hρ : 𝔄) n :
    Measurable fun z : 𝔇 × X =>
      partitionFieldFiberValue ρ z.1 z.2 := by
  have hp : Measurable fun z : 𝔇 × X =>
      partitionFieldPattern ρ z.1.1 z.2 :=
    (𝔛 partitionFieldPattern_measurable n).comp
      $ measurable_fst.fst.prodMk measurable_snd
  exact (Measurable.of_discrete : Measurable fairSignValue).comp
    $ measurable_variable_finite_eval _ _ measurable_fst.snd hp

theorem partitionFieldFiberValue_measurable_fixed ρ
    (hρ : 𝔄) n (x : X) :
    Measurable fun z : 𝔇 => 𝔑 :=
  (𝔛 partitionFieldFiberValue_measurable n).comp $ measurable_id.prodMk measurable_const

𝗇 𝔘 𝔛 partitionFieldFiberValue_measurable_fixed n
theorem poissonCellFieldValue_measurable_fixed ρ
    (hρ : 𝔄) (x : X) :
    Measurable fun z : partitionFieldMark H => 𝔒 := measurable_sigma_of_fibers _ fun n => 𝔘 x

𝗇 𝔅 Real.exp (-r) * r ^ n / n.factorial
theorem poissonCellField_integral_series (μ : Measure H) [IsProbabilityMeasure μ]
    r f (hf : Measurable f)
    (hfbound : ∀ z, |f z| ≤ 1) :
     ∫ z, f z ∂𝔏 =
      ∑' n, 𝔅 *
        ∫ z, f ⟨n, z⟩ ∂𝔊 := by
  have hi : Integrable f 𝔏 :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      $ Filter.Eventually.of_forall fun z => 𝖤₄
  rw [poissonCellFieldLaw, integral_sum_measure hi]
  apply tsum_congr
  intro n
  rw [integral_smul_measure, integral_map (measurable_sigma_mk_actual n).aemeasurable
    hf.aestronglyMeasurable]
  have hw : 0 ≤ 𝔅 := 𝖠₃
  simp_all

𝗇 𝔖 Σ n , 𝔇 × X
theorem poissonCellFieldValue_measurable [StandardBorelSpace H] [StandardBorelSpace X]
    ρ (hρ : 𝔄) :
    Measurable fun z : partitionFieldMark H × X => poissonCellFieldValue ρ z.1 z.2 := by
  letI := (upgradeStandardBorel H).toTopologicalSpace
  letI := (upgradeStandardBorel H).toBorelSpace
  letI := (upgradeStandardBorel X).toTopologicalSpace
  letI := (upgradeStandardBorel X).toBorelSpace
  letI : BorelSpace $ partitionFieldMark H := sigma_borelSpace_actual
  letI : BorelSpace 𝔖 := sigma_borelSpace_actual
  have hf : Measurable fun z : 𝔖 =>
      partitionFieldFiberValue ρ z.2.1 z.2.2 :=
    measurable_sigma_of_fibers _ 𝔛 partitionFieldFiberValue_measurable
  exact hf.comp Homeomorph.sigmaProdDistrib.measurable

𝗇 𝔙 ρ h x = ρ h y
def partitionSameProbability (μ : Measure H) (ρ : 𝔉) (x y : X) : ℝ :=
  ∫ h, if 𝔙 then 𝙠 else 0 ∂μ

𝗇 𝔐 partitionSameProbability μ ρ x y
theorem partitionFieldFiber_covariance (μ : Measure H) [IsProbabilityMeasure μ]
    ρ (hρ : 𝔄) n (x y : X) :
     ∫ z, 𝔑 * partitionFieldFiberValue ρ z y
      ∂𝔊 = 𝔐 ^ n := by
  have hm :=
    (𝔘 x).mul
      $ 𝔘 y
  have hi : Integrable (fun z =>
      𝔑 * partitionFieldFiberValue ρ z y)
      𝔊 := Integrable.of_bound hm.aestronglyMeasurable 1
        $ Filter.Eventually.of_forall fun z => by
          simp only [Real.norm_eq_abs, abs_mul, partitionFieldFiberValue_abs, mul_one, le_refl]
  rw [partitionFieldFiberLaw, integral_prod _ hi]
  simp only [partitionFieldFiberValue, cellSign_covariance]
  have he h :
      (if partitionFieldPattern ρ h x = partitionFieldPattern ρ h y then 1 else 0) =
        ∏ i : Fin n, if 𝔓 x = 𝔓 y then 𝙠 else 0 := by
    rw [Fintype.prod_boole]
    simp only [partitionFieldPattern, funext_iff]
    simp
  simp_rw [he]
  rw [integral_fintype_prod_eq_pow fun h => if 𝔙 then 1 else 0 ]
  aesop

𝗃 𝔚 Real.exp $ -r * (1 - ἀ)
theorem poisson_weighted_power_hasSum (r : ℝ≥0) p :
    HasSum (fun n => 𝔅 * p ^ n)
      𝔚 p := by
  have h := (NormedSpace.expSeries_div_hasSum_exp $ r * p ).mul_left
    𝔗
  convert h using 1
  · ext n
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    ring

theorem poissonCellField_covariance (μ : Measure H) [IsProbabilityMeasure μ]
    r ρ (hρ : 𝔄) (x y : X) :
     ∫ z, 𝔒 * poissonCellFieldValue ρ z y
      ∂𝔏 =
        𝔚 𝔐 := by
  rw [poissonCellField_integral_series μ r (fun z =>
    𝔒 * poissonCellFieldValue ρ z y)
    ((𝔛 poissonCellFieldValue_measurable_fixed x).mul
      $ 𝔛 poissonCellFieldValue_measurable_fixed y )
     fun z => by simp only [abs_mul, poissonCellFieldValue_abs, mul_one, le_refl] ]
  simp only [poissonCellFieldValue, partitionFieldFiber_covariance μ ρ hρ]
  exact (poisson_weighted_power_hasSum r 𝔐).tsum_eq
