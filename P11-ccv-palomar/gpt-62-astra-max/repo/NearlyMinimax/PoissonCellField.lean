module

public import NearlyMinimax.FairCellSigns
public import NearlyMinimax.FiniteSigmaProbability


@[expose] public section

/-! A genuine probability law for the fair-cell Poisson partition field. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

abbrev partitionFieldFiber (H : Type*) (n : ℕ) :=
  (Fin n → H) × ((Fin n → Fin 2) → Fin 2)

abbrev partitionFieldMark (H : Type*) := Σ n : ℕ, partitionFieldFiber H n

variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]

section
variable (μ : Measure H) {E I B : Type*}

theorem measurable_variable_finite_eval [MeasurableSpace E]
    [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] [MeasurableSpace B]
    {g : E → I → B} {p : E → I} (hg : Measurable g) (hp : Measurable p) :
    Measurable (fun z => g z (p z)) := by
  intro s hs
  have he : (fun z => g z (p z)) ⁻¹' s =
      ⋃ i, (p ⁻¹' {i}) ∩ ((fun z => g z i) ⁻¹' s) := by
    ext z
    simp
  rw [he]
  exact MeasurableSet.iUnion (fun i =>
    (hp (measurableSet_singleton i)).inter (hg.eval hs))

def partitionFieldFiberLaw (n : ℕ) : Measure (partitionFieldFiber H n) :=
  (Measure.pi (fun _ => μ)).prod (cellSignLaw (Fin n → Fin 2))

instance partitionFieldFiberLaw_probability [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (partitionFieldFiberLaw μ n) := by
  unfold partitionFieldFiberLaw
  infer_instance

def poissonCellFieldLaw (r : ℝ≥0) : Measure (partitionFieldMark H) :=
  Measure.sum fun n => ENNReal.ofReal (Real.exp (-r) * r ^ n / n.factorial) •
    (partitionFieldFiberLaw μ n).map (Sigma.mk n)

instance poissonCellFieldLaw_probability [IsProbabilityMeasure μ] (r : ℝ≥0) :
    IsProbabilityMeasure (poissonCellFieldLaw μ r) := by
  constructor
  simp only [poissonCellFieldLaw, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, smul_eq_mul]
  have hm (n : ℕ) : (partitionFieldFiberLaw μ n).map (Sigma.mk n) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_sigma_mk_actual n) MeasurableSet.univ]
    simp
  simp_rw [hm, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (hasSum_one_poissonMeasure r).summable, (hasSum_one_poissonMeasure r).tsum_eq]
  simp

theorem poissonCellFieldLaw_measurable :
    Measurable (poissonCellFieldLaw μ) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [poissonCellFieldLaw, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
  fun_prop

end

instance partitionFieldMark_standardBorel [StandardBorelSpace H] :
    StandardBorelSpace (partitionFieldMark H) := sigma_standardBorel_actual

section
variable (ρ : H → X → Fin 2) {n : ℕ} (z : partitionFieldFiber H n) (h : Fin n → H) (x : X)

def partitionFieldPattern : Fin n → Fin 2 := fun i => ρ (h i) x

def partitionFieldFiberValue : ℝ :=
  fairSignValue (z.2 (partitionFieldPattern ρ z.1 x))

def poissonCellFieldValue
    (z : partitionFieldMark H) (x : X) : ℝ := partitionFieldFiberValue ρ z.2 x

theorem partitionFieldFiberValue_abs : |partitionFieldFiberValue ρ z x| = 1 :=
  fairSignValue_abs _

theorem poissonCellFieldValue_abs
    (z : partitionFieldMark H) (x : X) : |poissonCellFieldValue ρ z x| = 1 :=
  partitionFieldFiberValue_abs ..

end

section
variable {ρ : H → X → Fin 2} (hρ : Measurable (Function.uncurry ρ))
include hρ

theorem partitionFieldPattern_measurable (n : ℕ) :
    Measurable (fun z : (Fin n → H) × X => partitionFieldPattern ρ z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  have he : Measurable (fun z : (Fin n → H) × X => (z.1 i, z.2)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
  exact hρ.comp he

theorem partitionFieldFiberValue_measurable (n : ℕ) :
    Measurable (fun z : partitionFieldFiber H n × X =>
      partitionFieldFiberValue ρ z.1 z.2) := by
  have hp : Measurable (fun z : partitionFieldFiber H n × X =>
      partitionFieldPattern ρ z.1.1 z.2) :=
    (partitionFieldPattern_measurable hρ n).comp
      (measurable_fst.fst.prodMk measurable_snd)
  have hb : Measurable (fun z : partitionFieldFiber H n × X => z.1.2) :=
    measurable_fst.snd
  exact Measurable.of_discrete.comp
    (measurable_variable_finite_eval hb hp)

theorem partitionFieldFiberValue_measurable_fixed (n : ℕ) (x : X) :
    Measurable (fun z : partitionFieldFiber H n => partitionFieldFiberValue ρ z x) :=
  (partitionFieldFiberValue_measurable hρ n).comp (measurable_id.prodMk measurable_const)

theorem poissonCellFieldValue_measurable_fixed (x : X) :
    Measurable (fun z => poissonCellFieldValue ρ z x) := (sigma_measurable_iff _).2 (fun n => partitionFieldFiberValue_measurable_fixed hρ n x)

end

variable (μ : Measure H)

theorem poissonCellField_integral_series [IsProbabilityMeasure μ]
    (r : ℝ≥0) {f : partitionFieldMark H → ℝ} (hf : Measurable f)
    (hfbound : ∀ z, |f z| ≤ 1) :
    (∫ z, f z ∂poissonCellFieldLaw μ r) =
      ∑' n, (Real.exp (-r) * r ^ n / n.factorial) *
        ∫ z, f ⟨n, z⟩ ∂partitionFieldFiberLaw μ n := by
  have hi : Integrable f (poissonCellFieldLaw μ r) :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by bound))
  rw [poissonCellFieldLaw, integral_sum_measure hi]
  apply tsum_congr
  intro n
  rw [integral_smul_measure, integral_map (measurable_sigma_mk_actual n).aemeasurable
    hf.aestronglyMeasurable]
  have hw : 0 ≤ Real.exp (-r) * r ^ n / n.factorial := by positivity
  simp [ENNReal.toReal_ofReal hw, smul_eq_mul]

theorem poissonCellFieldValue_measurable [StandardBorelSpace H] [StandardBorelSpace X]
    {ρ : H → X → Fin 2} (hρ : Measurable (Function.uncurry ρ)) :
    Measurable (fun z : partitionFieldMark H × X => poissonCellFieldValue ρ z.1 z.2) := by
  letI  := (upgradeStandardBorel H).toTopologicalSpace
  letI  := (upgradeStandardBorel H).toBorelSpace
  letI  := (upgradeStandardBorel X).toTopologicalSpace
  letI  := (upgradeStandardBorel X).toBorelSpace
  letI : BorelSpace (partitionFieldMark H) := sigma_borelSpace_actual
  letI : BorelSpace (Σ n : ℕ, partitionFieldFiber H n × X) := sigma_borelSpace_actual
  have hf : Measurable (fun z : Σ n : ℕ, partitionFieldFiber H n × X =>
      partitionFieldFiberValue ρ z.2.1 z.2.2) :=
    (sigma_measurable_iff _).2 (partitionFieldFiberValue_measurable hρ)
  exact hf.comp Homeomorph.sigmaProdDistrib.measurable

def partitionSameProbability (ρ : H → X → Fin 2) (x y : X) : ℝ :=
  ∫ h, if ρ h x = ρ h y then 1 else 0 ∂μ

theorem partitionFieldFiber_covariance [IsProbabilityMeasure μ]
    {ρ : H → X → Fin 2} (hρ : Measurable (Function.uncurry ρ)) (n : ℕ) (x y : X) :
    (∫ z, partitionFieldFiberValue ρ z x * partitionFieldFiberValue ρ z y
      ∂partitionFieldFiberLaw μ n) = partitionSameProbability μ ρ x y ^ n := by
  have hm  :=
    (partitionFieldFiberValue_measurable_fixed hρ n x).mul
      (partitionFieldFiberValue_measurable_fixed hρ n y)
  have hi : Integrable (fun z =>
      partitionFieldFiberValue ρ z x * partitionFieldFiberValue ρ z y)
      (partitionFieldFiberLaw μ n) := Integrable.of_bound hm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun z => by
          simp [Real.norm_eq_abs, abs_mul, partitionFieldFiberValue_abs, mul_one, le_refl]))
  rw [partitionFieldFiberLaw, integral_prod _ hi]
  simp only [partitionFieldFiberValue, cellSign_covariance]
  have he (h : Fin n → H) :
      (if partitionFieldPattern ρ h x = partitionFieldPattern ρ h y then 1 else 0) =
        ∏ i, if ρ (h i) x = ρ (h i) y then (1 : ℝ) else 0 := by
    rw [Fintype.prod_boole]
    simp only [partitionFieldPattern, funext_iff]
    split_ifs <;> rfl
  simp_rw [he]
  rw [integral_fintype_prod_eq_pow (fun h => if ρ h x = ρ h y then 1 else 0)]
  simp [partitionSameProbability]

theorem poisson_weighted_power_hasSum (r : ℝ≥0) (p : ℝ) :
    HasSum (fun n => (Real.exp (-r) * r ^ n / n.factorial) * p ^ n)
      (Real.exp (-r * (1 - p))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (r * p)).mul_left
    (Real.exp (-r))
  convert h using 1
  · ext n
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    ring

theorem poissonCellField_covariance [IsProbabilityMeasure μ]
    (r : ℝ≥0) {ρ : H → X → Fin 2} (hρ : Measurable (Function.uncurry ρ)) (x y : X) :
    (∫ z, poissonCellFieldValue ρ z x * poissonCellFieldValue ρ z y
      ∂poissonCellFieldLaw μ r) =
        Real.exp (-r * (1 - partitionSameProbability μ ρ x y)) := by
  rw [poissonCellField_integral_series μ r (f := (fun z =>
    poissonCellFieldValue ρ z x * poissonCellFieldValue ρ z y))
    ((poissonCellFieldValue_measurable_fixed hρ x).mul
      (poissonCellFieldValue_measurable_fixed hρ y))
    (fun z => by simp [abs_mul, poissonCellFieldValue_abs, mul_one, le_refl])]
  simp only [poissonCellFieldValue, partitionFieldFiber_covariance μ hρ]
  exact (poisson_weighted_power_hasSum r (partitionSameProbability μ ρ x y)).tsum_eq

end NearlyMinimax
