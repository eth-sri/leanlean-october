module

public import NearlyMinimax.LowSmoothnessConstants
public import NearlyMinimax.ParametricLower

@[expose] public section

/-! # Actual probability laws of the low-smoothness mixture

The finite response labels encode the original real response experiment.
This file proves the law identification and transfers its risks to the
original model; it introduces no statistical risk premise.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace NearlyMinimax

/-- The index representation before decoding observations into real responses. -/
abbrev IndexedSample (d n : ℕ) := DesignSample d n × TernaryVector n

section
variable {α : Type*} [MeasurableSpace α] (a V : ℝ)

def responseIndexKernel
    {F : α → ℝ} (hF : Measurable F) : Kernel α (Fin 3) where
  toFun x := ∑ y, ENNReal.ofReal (ternaryMass a (F x) V y) • Measure.dirac y
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun y _ =>
      (ENNReal.measurable_ofReal.comp (ternaryMass_measurable_comp a V F hF y)).mul_const _)

theorem responseIndexKernel_apply
    (F : α → ℝ) (hF : Measurable F) (x : α) :
    responseIndexKernel a V hF x =
      ∑ y, ENNReal.ofReal (ternaryMass a (F x) V y) • Measure.dirac y := rfl

theorem responseIndexKernel_markov {a V : ℝ}
    {F : α → ℝ} (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (responseIndexKernel a V hF) := by
  constructor
  intro x
  constructor
  simp [responseIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp x y), ternary_normalized (F x) V ha]
  simp

end

section
variable {d : ℕ} {α : Type*} {p : Covariate d → ℝ}
    (hdesign : IsProbabilityMeasure ((cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x)))) {n : ℕ}
    {a V : ℝ} {F : Covariate d → ℝ} (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y)

include hdesign in
/-- Encoding the genuine conditional index law gives the original real-response
observation law, including its covariate-dependent error kernel. -/
theorem ternaryParameter_observation_index_map :
    (((cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x))).compProd (responseIndexKernel a V hF)).map
      (fun z => (z.1, ternaryValue a z.2)) =
      observationLaw (ternaryParameter p hF ha hp) := by
  let _ := hdesign
  let _ := responseIndexKernel_markov hF ha hp
  let _ := ternaryErrorKernel_markov hF ha hp
  have hencode : Measurable (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2)) :=
    by fun_prop
  have hreal : Measurable (fun z : Covariate d × ℝ => (z.1, F z.1 + z.2)) :=
    by fun_prop
  ext s hs
  rw [Measure.map_apply hencode hs, observationLaw]
  change _ = (((designLaw (ternaryParameter p hF ha hp)).compProd
    (ternaryErrorKernel a V hF)).map (fun z => (z.1, F z.1 + z.2))) s
  rw [Measure.map_apply hreal hs]
  change _ = (((cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x))).compProd (ternaryErrorKernel a V hF)) _
  rw [Measure.compProd_apply (hs.preimage hencode), Measure.compProd_apply (hs.preimage hreal)]
  apply lintegral_congr
  intro x
  have hSreal : MeasurableSet {u | (x, F x + u) ∈ s} :=
    hs.preimage (by fun_prop)
  have hSindex : MeasurableSet {y | (x, ternaryValue a y) ∈ s} :=
    hs.preimage (by fun_prop)
  simp [responseIndexKernel_apply, ternaryErrorKernel_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  have he : F x + (ternaryValue a y - F x) = ternaryValue a y := by ring
  by_cases h : (x, ternaryValue a y) ∈ s <;> simp [Set.indicator, he, h]

/-- The genuine conditional law of all finite response labels. -/
def responseSampleIndexKernel [MeasurableSpace α] (n : ℕ) (a V : ℝ)
    {F : α → ℝ} (hF : Measurable F) : Kernel (Fin n → α) (TernaryVector n) where
  toFun x := ∑ y,
    ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)) • Measure.dirac y
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro y _
    apply Measurable.mul_const
    apply ENNReal.measurable_ofReal.comp
    exact Finset.measurable_prod _ (fun i _ =>
      ternaryMass_measurable_comp a V (fun x : Fin n → α => F (x i))
        (by fun_prop) (y i))

theorem responseSampleIndexKernel_apply [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : Fin n → α) :
    responseSampleIndexKernel n a V hF x =
      ∑ y,
        ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)) • Measure.dirac y := rfl

theorem responseSampleIndexKernel_markov [MeasurableSpace α]
    (n : ℕ) {a V : ℝ} {F : α → ℝ} (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (responseSampleIndexKernel n a V hF) := by
  constructor
  intro x
  constructor
  simp [responseSampleIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => Finset.prod_nonneg
      (fun i _ => hp ..)), ← Fintype.prod_sum]
  simp [ternary_normalized _ V ha]

/-- The sample kernel, with designs drawn independently, is the same law as
independent pairs from the one-observation kernel. -/
theorem responseSampleIndexKernel_joint_map [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) {a V : ℝ} {F : α → ℝ} (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ => μ)).compProd
      (responseSampleIndexKernel n a V hF)).map
      (fun z => fun i => (z.1 i, z.2 i)) =
      Measure.pi (fun _ => μ.compProd (responseIndexKernel a V hF)) := by
  let _ := responseIndexKernel_markov hF ha hp
  let _ := responseSampleIndexKernel_markov n hF ha hp
  have hm : Measurable (fun z : (Fin n → α) × (TernaryVector n) =>
      fun i => (z.1 i, z.2 i)) := by fun_prop
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs),
    Measure.compProd_apply ((MeasurableSet.univ_pi hs).preimage hm)]
  have hinner x :
      responseSampleIndexKernel n a V hF x
        (Prod.mk x ⁻¹' (fun z =>
          fun i => (z.1 i, z.2 i)) ⁻¹' Set.pi Set.univ s) =
        ∏ i, ∑ y, ENNReal.ofReal (ternaryMass a (F (x i)) V y) *
          (s i).indicator 1 (x i, y) := by
    simp [responseSampleIndexKernel_apply, Measure.finsetSum_apply,
      Measure.smul_apply, smul_eq_mul]
    simp_rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hp (x i) _)]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : ∀ i, (x i, y i) ∈ s i
    · simp [Set.indicator_of_mem, h, Set.mem_pi]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hz : (s i).indicator (1 : α × Fin 3 → ℝ≥0∞) (x i, y i) = 0 :=
        Set.indicator_of_notMem hi _
      rw [Finset.prod_mul_distrib]
      have hzero : ∏ j, (s j).indicator (1 : α × Fin 3 → ℝ≥0∞) (x j, y j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hz
      rw [hzero]
      simp [Set.indicator_of_notMem, Set.mem_pi, h]
  simp_rw [hinner]
  let G  := fun i x =>
    ∑ y, ENNReal.ofReal (ternaryMass a (F x) V y) * (s i).indicator 1 (x, y)
  have hG : ∀ i, Measurable (G i) := fun i => Finset.measurable_sum _ (fun y _ =>
      (ENNReal.measurable_ofReal.comp (ternaryMass_measurable_comp a V F hF y)).mul
        ((Measurable.indicator measurable_const (hs i)).comp (measurable_id.prodMk measurable_const)))
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _
    (iIndepFun_pi (fun i => (hG i).aemeasurable))
    (fun i => (hG i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [(measurePreserving_eval (fun _ => μ) i).lintegral_comp (hG i), Measure.compProd_apply (hs i)]
  apply lintegral_congr
  intro x
  simp [G, responseIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ ((hs i).preimage measurable_prodMk_left), smul_eq_mul]
  rfl

/-- Encode all finite response labels as the paper's real observations. -/
def encodeDesignResponse (a : ℝ) :
    IndexedSample d n → (Fin n → Observation d) :=
  fun z i => (z.1 i, ternaryValue a (z.2 i))

theorem encodeDesignResponse_measurable (a : ℝ) :
    Measurable (encodeDesignResponse (d := d) (n := n) a) := (encodeResponse_measurable a).comp measurable_swap

/-- Identification with the complete iid sample law of the original model. -/
theorem ternaryParameter_sample_index_map
    (p : Covariate d → ℝ) (hdesign : IsProbabilityMeasure ((cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x))))
    (n : ℕ) {a V : ℝ} {F : Covariate d → ℝ} (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ => (cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x)))).compProd
      (responseSampleIndexKernel n a V hF)).map (encodeDesignResponse a) =
      sampleLaw (ternaryParameter p hF ha hp) n := by
  let _ := hdesign
  let _ := responseIndexKernel_markov hF ha hp
  let _ := responseSampleIndexKernel_markov n hF ha hp
  have hsingle : MeasurePreserving
      (fun z => (z.1, ternaryValue a z.2))
      (((cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x))).compProd (responseIndexKernel a V hF))
      (observationLaw (ternaryParameter p hF ha hp)) :=
    ⟨by fun_prop,
      ternaryParameter_observation_index_map hdesign ..⟩
  let _ : IsProbabilityMeasure (observationLaw (ternaryParameter p hF ha hp)) := by
    rw [← hsingle.map_eq]
    infer_instance
  have h := (measurePreserving_pi _ _ (fun _ : Fin n => hsingle)).map_eq
  rw [← responseSampleIndexKernel_joint_map ((cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x))) n hF ha hp,
    Measure.map_map] at h
  · exact h
  · fun_prop
  · fun_prop

theorem uniformTernaryParameter_sample_index_map
    (n : ℕ) {a V : ℝ} {F : Covariate d → ℝ} (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ => cubeVolume d)).compProd
      (responseSampleIndexKernel n a V hF)).map (encodeDesignResponse a) =
      sampleLaw (uniformTernaryParameter hF ha hp) n := by
  simpa using ternaryParameter_sample_index_map (fun _ => 1) (by simpa using cubeVolume_isProbability d) n hF ha hp

/-- Genuine finite conditional integrals, with no density representation
assumption, equal the likelihood sums used by the score proof. -/
theorem responseSampleIndexKernel_integral [MeasurableSpace α]
    {n : ℕ} (a V : ℝ) {F : α → ℝ} (hF : Measurable F) (x : Fin n → α)
    (hp : ∀ i y, 0 ≤ ternaryMass a (F (x i)) V y)
    (H : (TernaryVector n) → ℝ) :
    (∫ y, H y ∂responseSampleIndexKernel n a V hF x) =
      ∑ y, (∏ i, ternaryMass a (F (x i)) V (y i)) * H y := by
  rw [responseSampleIndexKernel_apply, integral_finsetSum_measure]
  · simp
    apply Finset.sum_congr rfl
    intro y _
    rw [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => hp i (y i)))]
  · intro y _
    let _ := (Measure.dirac y).smul_finite
      (c := ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i))) ENNReal.ofReal_ne_top
    exact Integrable.of_finite

/-- Bounded data-observable expectations in the genuine original sample law
are exactly the design-integrated finite likelihood expectations. -/
theorem uniformTernaryParameter_sample_integral
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H)
    {B : ℝ} (hB : ∀ z, |H z| ≤ B) :
    (∫ z, H z ∂sampleLaw (uniformTernaryParameter hF ha hp) n) =
      ∫ x, ∑ y,
        (∏ i, ternaryMass a (F (x i)) V (y i)) * H (encodeDesignResponse a (x, y))
        ∂Measure.pi (fun _ => cubeVolume d) := by
  let _ := cubeVolume_isProbability d
  let _ := responseSampleIndexKernel_markov n hF ha hp
  have hm := encodeDesignResponse_measurable (d := d) (n := n) a
  rw [← uniformTernaryParameter_sample_index_map n hF ha hp,
    integral_map hm.aemeasurable hH.aestronglyMeasurable]
  have hi : Integrable (fun z => H (encodeDesignResponse a z))
      ((Measure.pi (fun _ => cubeVolume d)).compProd
        (responseSampleIndexKernel n a V hF)) :=
    (integrable_const B).mono' (hH.comp hm).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by bound))
  rw [Measure.integral_compProd hi]
  grind [responseSampleIndexKernel_integral]

/-- Exact identification of the finite likelihood risk with the original
model's ENNReal mean-squared risk for every bounded measurable estimator. -/
theorem uniformTernaryParameter_risk_formula
    {T : Estimator d n} {B : ℝ} (hB : ∀ z, |T.val z| ≤ B) :
    ENNReal.ofReal (∫ x, ∑ y,
      (∏ i, ternaryMass a (F (x i)) V (y i)) *
        (T.val (encodeDesignResponse a (x, y)) - V) ^ 2
      ∂Measure.pi (fun _ => cubeVolume d)) =
      meanSquaredRisk T (uniformTernaryParameter hF ha hp) := by
  let _ := cubeVolume_isProbability d
  let _ := responseSampleIndexKernel_markov n hF ha hp
  let _ : IsProbabilityMeasure (sampleLaw (uniformTernaryParameter hF ha hp) n) := by
    rw [← uniformTernaryParameter_sample_index_map n hF ha hp]
    infer_instance
  have hm  := (T.property.sub_const V).pow_const 2
  have hbound z : |(T.val z - V) ^ 2| ≤ (B + |V|) ^ 2 := by
    have he := (abs_sub (T.val z) V).trans (add_le_add (hB z) (le_refl |V|))
    simpa using pow_le_pow_left₀ (abs_nonneg _) he 2
  rw [← uniformTernaryParameter_sample_integral hF ha hp hm hbound]
  exact ofReal_integral_eq_lintegral_ofReal ((integrable_const ((B + |V|) ^ 2)).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => by bound)))
    (Filter.Eventually.of_forall (fun z => sq_nonneg _))

end

variable {d n : ℕ} {C : ModelConstants d} {P : LowSmoothnessTernaryConstants C} {k : ℕ} {η b t : ℝ}
    (ξ : TernaryVector (gridWindowCount d k)) (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ)
    (hvariance : η ^ 2 ≤ P.ρ) (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : ((2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)) * b ≤ C.holderBound) (T : BoundedEstimator C n)

/-- Exact risk formula for every concrete grid-prior state. -/
theorem gridPathParameter_risk_formula
    {T : Estimator d n} {B : ℝ} (hB : ∀ z, |T.val z| ≤ B) :
    ENNReal.ofReal (∫ x, ∑ y,
      finiteResponseLikelihood P.a (P.v - η ^ 2 * t)
        (fun ξ i => indexedGridField η ξ (x i)) ξ y *
        (T.val (encodeDesignResponse P.a (x, y)) - (P.v - η ^ 2 * t)) ^ 2
      ∂Measure.pi (fun _ => cubeVolume d)) =
      meanSquaredRisk T (gridPathParameter ξ hη ht hfield hvariance) := by
  have hf x  :=
    (indexedGridField_abs_bound hη ξ x).trans (by nlinarith)
  have hp x y  :=
    P.c_pos.le.trans ((P.path_legality η t _ ht hvariance (hf x)).2.2.1 y)
  exact uniformTernaryParameter_risk_formula _ P.a_pos.ne' hp hB

include hk hs1 hb hη ht hfield hvariance hscale hholder in
/-- The prior risk contribution of every latent state is controlled by the
original bounded estimator's worst-case risk. -/
theorem gridPathParameter_finite_risk_le_worstCase :
    ENNReal.ofReal (∫ x, ∑ y,
      finiteResponseLikelihood P.a (P.v - η ^ 2 * t)
        (fun ξ i => indexedGridField η ξ (x i)) ξ y *
        (T.val.val (encodeDesignResponse P.a (x, y)) - (P.v - η ^ 2 * t)) ^ 2
      ∂Measure.pi (fun _ => cubeVolume d)) ≤ worstCaseRisk C T.val := by
  have hB z : |T.val.val z| ≤ effectiveVarianceUpper C := by
    rw [abs_of_nonneg (C.varianceLower_pos.le.trans (T.property z).1)]
    exact (T.property z).2
  rw [gridPathParameter_risk_formula ξ hη ht hfield hvariance hB]
  exact le_iSup (fun θ : {θ // Admissible C θ} => meanSquaredRisk T.val θ.val)
    ⟨_, gridPathParameter_admissible ξ hk hs1 hb hη ht hfield
      hvariance hscale hholder⟩

/-- Clipped estimators have finite genuine worst-case risk, independently of
which admissible parameter realizes that risk. -/
theorem boundedEstimator_worstCaseRisk_ne_top : worstCaseRisk C T.val ≠ ∞ := by
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply iSup_le
  intro θ
  exact boundedEstimator_risk_le_diameter T θ.property

end NearlyMinimax
