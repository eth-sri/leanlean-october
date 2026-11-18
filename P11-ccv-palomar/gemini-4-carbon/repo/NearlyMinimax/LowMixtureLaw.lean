module

public import NearlyMinimax.ParametricLower

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace NearlyMinimax

def responseIndexKernel {α : Type*} [MeasurableSpace α] (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F) : Kernel α (Fin 3) where
  toFun x := ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F x) V y) • Measure.dirac y
  measurable' := Measure.measurable_of_measurable_coe _ fun s _ => by
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun y _ =>
      (ternaryMass_measurable_comp a V F hF y).ennreal_ofReal.mul_const _

theorem responseIndexKernel_apply {α : Type*} [MeasurableSpace α] (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F) (x : α) :
    responseIndexKernel a V F hF x =
      ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F x) V y) • Measure.dirac y := rfl

theorem responseIndexKernel_markov {α : Type*} [MeasurableSpace α] (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (responseIndexKernel a V F hF) := ⟨fun x => ⟨by
  simp only [responseIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one,
    ← ENNReal.ofReal_sum_of_nonneg fun y _ => hp x y, ternary_normalized a (F x) V ha, ENNReal.ofReal_one]⟩⟩

theorem uniformTernaryParameter_observation_index_map {d : ℕ}
    (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((cubeVolume d).compProd (responseIndexKernel a V F hF)).map
      (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2)) =
      observationLaw (uniformTernaryParameter a V F hF ha hp) := by
  let _ := cubeVolume_isProbability d
  let _ := responseIndexKernel_markov a V F hF ha hp
  let _ := ternaryErrorKernel_markov a V F hF ha hp
  have hencode : Measurable fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2) :=
    measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)
  have hreal : Measurable fun z : Covariate d × ℝ => (z.1, F z.1 + z.2) :=
    measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
  ext s hs
  rw [Measure.map_apply hencode hs, observationLaw]
  change _ = (((designLaw (uniformTernaryParameter a V F hF ha hp)).compProd
    (ternaryErrorKernel a V F hF)).map fun z : Covariate d × ℝ => (z.1, F z.1 + z.2)) s
  rw [Measure.map_apply hreal hs]
  simp only [designLaw, uniformTernaryParameter, ENNReal.ofReal_one, withDensity_const, one_smul]
  rw [Measure.compProd_apply (hs.preimage hencode), Measure.compProd_apply (hs.preimage hreal)]
  refine lintegral_congr fun x => ?_
  have hSr : MeasurableSet {u : ℝ | (x, F x + u) ∈ s} :=
    hs.preimage (measurable_const.prodMk (measurable_const.add measurable_id))
  have hSi : MeasurableSet {y : Fin 3 | (x, ternaryValue a y) ∈ s} :=
    hs.preimage (measurable_const.prodMk (measurable_of_countable _))
  simp only [responseIndexKernel_apply, ternaryErrorKernel_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  change Measure.dirac y {y | (x, ternaryValue a y) ∈ s} =
    Measure.dirac (ternaryValue a y - F x) {u | (x, F x + u) ∈ s}
  rw [Measure.dirac_apply' _ hSi, Measure.dirac_apply' _ hSr]
  have he : F x + (ternaryValue a y - F x) = ternaryValue a y := by ring
  by_cases h : (x, ternaryValue a y) ∈ s <;> simp [Set.indicator, he, h]

def responseSampleIndexKernel {α : Type*} [MeasurableSpace α] (n : ℕ) (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F) : Kernel (Fin n → α) (Fin n → Fin 3) where
  toFun x := ∑ y : Fin n → Fin 3,
    ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)) • Measure.dirac y
  measurable' := Measure.measurable_of_measurable_coe _ fun s _ => by
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun y _ =>
      ((Finset.measurable_prod _ fun i _ =>
        ternaryMass_measurable_comp a V _ (hF.comp (measurable_pi_apply i)) (y i)).ennreal_ofReal).mul_const _

theorem responseSampleIndexKernel_apply {α : Type*} [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : Fin n → α) :
    responseSampleIndexKernel n a V F hF x =
      ∑ y : Fin n → Fin 3,
        ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)) • Measure.dirac y := rfl

theorem responseSampleIndexKernel_markov {α : Type*} [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (responseSampleIndexKernel n a V F hF) := ⟨fun x => ⟨by
  simp only [responseSampleIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => Finset.prod_nonneg fun i _ => hp (x i) (y i),
    ← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]⟩⟩

theorem responseSampleIndexKernel_joint_map {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi fun _ : Fin n => μ).compProd
      (responseSampleIndexKernel n a V F hF)).map
      (fun z : (Fin n → α) × (Fin n → Fin 3) => fun i => (z.1 i, z.2 i)) =
      Measure.pi fun _ : Fin n => μ.compProd (responseIndexKernel a V F hF) := by
  let _ := responseIndexKernel_markov a V F hF ha hp
  let _ := responseSampleIndexKernel_markov n a V F hF ha hp
  have hm : Measurable fun z : (Fin n → α) × (Fin n → Fin 3) => fun i => (z.1 i, z.2 i) := by fun_prop
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs),
    Measure.compProd_apply ((MeasurableSet.univ_pi hs).preimage hm)]
  have hinner (x : Fin n → α) :
      responseSampleIndexKernel n a V F hF x
        (Prod.mk x ⁻¹' (fun z : (Fin n → α) × (Fin n → Fin 3) => fun i => (z.1 i, z.2 i)) ⁻¹' Set.pi univ s) =
        ∏ i, ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F (x i)) V y) * (s i).indicator 1 (x i, y) := by
    simp only [responseSampleIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    simp_rw [ENNReal.ofReal_prod_of_nonneg fun i _ => hp (x i) _]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Measure.dirac_apply' _ (((MeasurableSet.univ_pi hs).preimage hm).preimage measurable_prodMk_left)]
    by_cases h : ∀ i, (x i, y i) ∈ s i
    · simp [Set.indicator_of_mem, h, Set.mem_pi]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hzero : ∏ j, (s j).indicator (1 : α × Fin 3 → ℝ≥0∞) (x j, y j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
      rw [Finset.prod_mul_distrib, hzero, mul_zero]
      simp [Set.indicator_of_notMem, Set.mem_pi, h]
  simp_rw [hinner]
  let G : Fin n → α → ℝ≥0∞ := fun i x =>
    ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F x) V y) * (s i).indicator 1 (x, y)
  have hG (i : Fin n) : Measurable (G i) := Finset.measurable_sum _ fun y _ =>
    (ternaryMass_measurable_comp a V F hF y).ennreal_ofReal.mul
      ((Measurable.indicator measurable_const (hs i)).comp (measurable_id.prodMk measurable_const))
  change (∫⁻ x, ∏ i, G i (x i) ∂Measure.pi fun _ : Fin n => μ) = _
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _
    (iIndepFun_pi fun i => (hG i).aemeasurable) fun i => (hG i).comp (measurable_pi_apply i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(measurePreserving_eval (fun _ : Fin n => μ) i).lintegral_comp (hG i), Measure.compProd_apply (hs i)]
  refine lintegral_congr fun x => ?_
  simp only [G, responseIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ ((hs i).preimage measurable_prodMk_left), smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => rfl

def encodeDesignResponse {d n : ℕ} (a : ℝ) :
    (Fin n → Covariate d) × (Fin n → Fin 3) → (Fin n → Observation d) :=
  fun z i => (z.1 i, ternaryValue a (z.2 i))

theorem encodeDesignResponse_measurable {d n : ℕ} (a : ℝ) :
    Measurable (encodeDesignResponse (d := d) (n := n) a) :=
  (encodeResponse_measurable a).comp measurable_swap

theorem uniformTernaryParameter_sample_index_map {d : ℕ}
    (n : ℕ) (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi fun _ : Fin n => cubeVolume d).compProd
      (responseSampleIndexKernel n a V F hF)).map (encodeDesignResponse a) =
      sampleLaw (uniformTernaryParameter a V F hF ha hp) n := by
  let _ := cubeVolume_isProbability d
  let _ := responseIndexKernel_markov a V F hF ha hp
  let _ := responseSampleIndexKernel_markov n a V F hF ha hp
  have hsingle : MeasurePreserving (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2))
      ((cubeVolume d).compProd (responseIndexKernel a V F hF))
      (observationLaw (uniformTernaryParameter a V F hF ha hp)) :=
    ⟨measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd),
      uniformTernaryParameter_observation_index_map a V F hF ha hp⟩
  let _ : IsProbabilityMeasure (observationLaw (uniformTernaryParameter a V F hF ha hp)) := by
    rw [← hsingle.map_eq]; infer_instance
  have h := (measurePreserving_pi _ _ fun _ : Fin n => hsingle).map_eq
  rw [← responseSampleIndexKernel_joint_map (cubeVolume d) n a V F hF ha hp, Measure.map_map] at h
  · exact h
  · exact Measurable.of_eval fun i =>
      (measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)).comp (measurable_pi_apply i)
  · fun_prop

theorem responseSampleIndexKernel_integral {α : Type*} [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : Fin n → α)
    (hp : ∀ i y, 0 ≤ ternaryMass a (F (x i)) V y)
    (H : (Fin n → Fin 3) → ℝ) :
    (∫ y, H y ∂responseSampleIndexKernel n a V F hF x) =
      ∑ y, (∏ i, ternaryMass a (F (x i)) V (y i)) * H y := by
  rw [responseSampleIndexKernel_apply, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    exact Finset.sum_congr rfl fun y _ => by rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => hp i (y i))]
  · intro y _
    let _ := (Measure.dirac y).smul_finite (c := ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i))) ENNReal.ofReal_ne_top
    exact Integrable.of_finite

end NearlyMinimax
