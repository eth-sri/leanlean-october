module

public import NearlyMinimax.LowSmoothnessConstants
public import NearlyMinimax.ParametricLower
public import NearlyMinimax.ConditionalLaw

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

def responseIndexKernel {α : Type*} [MeasurableSpace α] (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F) : Kernel α (Fin 3) :=
  weightedAtomKernel (fun x => ternaryMass a (F x) V) (fun _ y => y)
    (ternaryMass_measurable_comp a V F hF) (fun _ => measurable_const)

section
variable {α : Type*} [MeasurableSpace α] (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F)

theorem responseIndexKernel_apply (x : α) :
    responseIndexKernel a V F hF x =
      ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F x) V y) • Measure.dirac y := rfl

theorem responseIndexKernel_markov (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (responseIndexKernel a V F hF) :=
  weightedAtomKernel_markov _ _ _ _ hp (fun x => ternary_normalized a (F x) V)

end

/-- The conditional index representation works for every design law. -/
private theorem ternaryIndex_observation_map {d : ℕ} (μ : Measure (Covariate d))
    [IsProbabilityMeasure μ] (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    (μ.compProd (responseIndexKernel a V F hF)).map (fun z => (z.1, ternaryValue a z.2)) =
      (μ.compProd (ternaryErrorKernel a V F hF)).map (fun z => (z.1, F z.1 + z.2)) := by
  let _ := responseIndexKernel_markov a V F hF ha hp
  let _ := ternaryErrorKernel_markov a V F hF ha hp
  have hencode : Measurable (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2)) :=
    measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)
  have hreal : Measurable (fun z : Covariate d × ℝ => (z.1, F z.1 + z.2)) :=
    measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
  ext s hs
  rw [Measure.map_apply hencode hs, Measure.map_apply hreal hs]
  rw [Measure.compProd_apply (hs.preimage hencode), Measure.compProd_apply (hs.preimage hreal)]
  apply lintegral_congr
  intro x
  have hSreal : MeasurableSet {u : ℝ | (x, F x + u) ∈ s} :=
    hs.preimage (measurable_const.prodMk (measurable_const.add measurable_id))
  have hSindex : MeasurableSet {y : Fin 3 | (x, ternaryValue a y) ∈ s} :=
    hs.preimage (measurable_const.prodMk (measurable_of_countable _))
  simp only [responseIndexKernel_apply, ternaryErrorKernel_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  change Measure.dirac y {y | (x, ternaryValue a y) ∈ s} =
    Measure.dirac (ternaryValue a y - F x) {u | (x, F x + u) ∈ s}
  rw [Measure.dirac_apply' _ hSindex, Measure.dirac_apply' _ hSreal]
  have he : F x + (ternaryValue a y - F x) = ternaryValue a y := by ring
  by_cases h : (x, ternaryValue a y) ∈ s <;> simp [Set.indicator, he, h]

/-- The genuine conditional law of all finite response labels. -/
def responseSampleIndexKernel {α : Type*} [MeasurableSpace α] (n : ℕ) (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F) : Kernel (Fin n → α) (Fin n → Fin 3) :=
  weightedAtomKernel (fun x y => ∏ i, ternaryMass a (F (x i)) V (y i)) (fun _ y => y)
    (fun y => Finset.measurable_prod _ fun i _ =>
      ternaryMass_measurable_comp a V _ (hF.comp (measurable_pi_apply i)) (y i))
    (fun _ => measurable_const)

section
variable {α : Type*} [MeasurableSpace α]

section
variable (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F)
include n hF

theorem responseSampleIndexKernel_apply (x : Fin n → α) :
    responseSampleIndexKernel n a V F hF x =
      ∑ y : Fin n → Fin 3,
        ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)) • Measure.dirac y := rfl

private theorem responseSampleIndexKernel_eq_product (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    letI := responseIndexKernel_markov a V F hF ha hp
    responseSampleIndexKernel n a V F hF = finiteProductKernel (fun _ : Fin n => responseIndexKernel a V F hF) := by
  let _ := responseIndexKernel_markov a V F hF ha hp
  ext x : 1
  apply Measure.ext_of_singleton
  intro y
  rw [finiteProductKernel_apply, Measure.pi_singleton, responseSampleIndexKernel_apply,
    ← Measure.sum_fintype, Measure.sum_smul_dirac_singleton,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => hp (x i) (y i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [responseIndexKernel_apply, ← Measure.sum_fintype, Measure.sum_smul_dirac_singleton]

theorem responseSampleIndexKernel_markov (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (responseSampleIndexKernel n a V F hF) := by
  let _ := responseIndexKernel_markov a V F hF ha hp
  rw [responseSampleIndexKernel_eq_product n a V F hF ha hp]
  infer_instance

end

/-- The sample kernel, with designs drawn independently, is the same law as
independent pairs from the one-observation kernel. -/
theorem responseSampleIndexKernel_joint_map
    (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ : Fin n => μ)).compProd
      (responseSampleIndexKernel n a V F hF)).map pairVectors =
      Measure.pi (fun _ : Fin n => μ.compProd (responseIndexKernel a V F hF)) := by
  let _ := responseIndexKernel_markov a V F hF ha hp
  rw [responseSampleIndexKernel_eq_product n a V F hF ha hp]
  exact (pi_compProd_eq_map_pairVectors _ _).symm

end

/-- Encode all finite response labels as the paper's real observations. -/
def encodeDesignResponse {d n : ℕ} (a : ℝ) :
    TernarySample d n → ObservedSample d n :=
  fun z i => (z.1 i, ternaryValue a (z.2 i))

theorem encodeDesignResponse_measurable {d n : ℕ} (a : ℝ) :
    Measurable (encodeDesignResponse (d := d) (n := n) a) := (encodeResponse_measurable a).comp measurable_swap

section
variable {d : ℕ}

theorem responseSampleIndexKernel_encoded_map (μ : Measure (Covariate d))
    [IsProbabilityMeasure μ] (n : ℕ) (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ : Fin n => μ)).compProd (responseSampleIndexKernel n a V F hF)).map
      (encodeDesignResponse a) =
      Measure.pi (fun _ : Fin n => (μ.compProd (ternaryErrorKernel a V F hF)).map
        (fun z => (z.1, F z.1 + z.2))) := by
  let _ := responseIndexKernel_markov a V F hF ha hp
  let e : Covariate d × Fin 3 → Observation d := fun z => (z.1, ternaryValue a z.2)
  have he : Measurable e := measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)
  let σ := μ.compProd (responseIndexKernel a V F hF)
  let ν := σ.map e
  have : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff he.aemeasurable).2 inferInstance
  have hm : MeasurePreserving e σ ν := ⟨he, rfl⟩
  rw [← ternaryIndex_observation_map μ a V F hF ha hp]
  have h := (measurePreserving_pi _ _ (fun _ : Fin n => hm)).map_eq
  rw [← responseSampleIndexKernel_joint_map μ n a V F hF ha hp,
    Measure.map_map] at h
  exact h
  all_goals first | exact pairVectors_measurable | fun_prop

/-- Identification with the complete iid sample law of the original model. -/
theorem uniformTernaryParameter_sample_index_map
    (n : ℕ) (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ : Fin n => cubeVolume d)).compProd
      (responseSampleIndexKernel n a V F hF)).map (encodeDesignResponse a) =
      sampleLaw (uniformTernaryParameter a V F hF ha hp) n := by
  let _ := cubeVolume_isProbability d
  simpa only [sampleLaw, observationLaw, designLaw, uniformTernaryParameter, ENNReal.ofReal_one,
    withDensity_const, one_smul] using responseSampleIndexKernel_encoded_map (cubeVolume d) n a V F hF ha hp

end

/-- Genuine finite conditional integrals, with no density representation
assumption, equal the likelihood sums used by the score proof. -/
theorem responseSampleIndexKernel_integral {α : Type*} [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : Fin n → α)
    (hp : ∀ i y, 0 ≤ ternaryMass a (F (x i)) V y)
    (H : (Fin n → Fin 3) → ℝ) :
    (∫ y, H y ∂responseSampleIndexKernel n a V F hF x) =
      ∑ y, (∏ i, ternaryMass a (F (x i)) V (y i)) * H y :=
  weightedAtomMeasure_integral _ _ (fun y => Finset.prod_nonneg fun i _ => hp i (y i)) H

section
variable {d n : ℕ}

/-- Integrability and exact risk identification use the same joint design-label law. -/
theorem uniformTernaryParameter_finite_risk
    (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (T : Estimator d n) (B : ℝ) (hB : ∀ z, |T.val z| ≤ B) :
    let μ := Measure.pi (fun _ : Fin n => cubeVolume d)
    let R := fun x => ∑ y : Fin n → Fin 3,
      (∏ i, ternaryMass a (F (x i)) V (y i)) * (T.val (encodeDesignResponse a (x, y)) - V)^2
    Integrable R μ ∧ ENNReal.ofReal (∫ x, R x ∂μ) =
      meanSquaredRisk T (uniformTernaryParameter a V F hF ha hp) := by
  let := cubeVolume_isProbability d
  let := responseSampleIndexKernel_markov n a V F hF ha hp
  let μ := Measure.pi (fun _ : Fin n => cubeVolume d)
  let κ := responseSampleIndexKernel n a V F hF
  let G := fun z => (T.val z - V)^2
  let H := fun z => G (encodeDesignResponse a z)
  have hm := encodeDesignResponse_measurable (d := d) (n := n) a
  have hG : Measurable G := (T.property.sub_const V).pow_const 2
  have hi : MemLp (T.val ∘ encodeDesignResponse a) 2 (μ.compProd κ) :=
    MemLp.of_bound (T.property.comp hm).aestronglyMeasurable B
      (.of_forall fun z => (Real.norm_eq_abs _).trans_le (hB _))
  have hH : Integrable H (μ.compProd κ) := (hi.sub (memLp_const V)).integrable_sq
  have hsum (x) := responseSampleIndexKernel_integral n a V F hF x (fun i y => hp (x i) y) (fun y => H (x,y))
  have hμ : Integrable (fun x => ∫ y, H (x,y) ∂κ x) μ := by
    unfold Measure.compProd at hH
    simpa only [Kernel.prodMkLeft_apply, Kernel.const_apply] using hH.integral_compProd
  change Integrable _ μ ∧ _
  constructor
  · simpa only [κ, hsum] using hμ
  · have hmap := uniformTernaryParameter_sample_index_map n a V F hF ha hp
    have h' : Integrable G (sampleLaw (uniformTernaryParameter a V F hF ha hp) n) := by
      rw [← hmap]
      exact (integrable_map_measure hG.aestronglyMeasurable hm.aemeasurable).mpr hH
    change _ = ∫⁻ z, ENNReal.ofReal (G z) ∂sampleLaw (uniformTernaryParameter a V F hF ha hp) n
    rw [← ofReal_integral_eq_lintegral_ofReal h' (.of_forall fun _ => sq_nonneg _),
      ← hmap, integral_map hm.aemeasurable hG.aestronglyMeasurable, Measure.integral_compProd hH]
    simp only [κ, hsum, H, G, μ]

/-- The actual finite likelihood for a grid-prior state, with its squared loss. -/
def gridStateRisk (k : ℕ) (a v η t : ℝ) (T : Estimator d n)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (x : Fin n → Covariate d) : ℝ :=
  ∑ y, finiteResponseLikelihood (gridWindowCount d k) n a
    (v - η^2*t) (fun ξ i => indexedGridField d k η ξ (x i)) ξ y *
      (T.val (encodeDesignResponse a (x,y)) - (v - η^2*t))^2

section
variable (C : ModelConstants d)

theorem gridPathParameter_risk_formula (P : LowSmoothnessTernaryConstants C)
    (k : ℕ) (η t : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (hamp : GridAmplitudeBounds d η P.ρ) (ht : t ∈ Icc (0 : ℝ) 1)
    (T : BoundedEstimator C n) :
    let μ := Measure.pi (fun _ : Fin n => cubeVolume d)
    let R := gridStateRisk k P.a P.v η t T.val ξ
    Integrable R μ ∧ ENNReal.ofReal (∫ x, R x ∂μ) =
      meanSquaredRisk T.val (gridPathParameter C P k η t ξ hamp ht) := by
  have hp (x : Covariate d) (y : Fin 3) :=
    P.c_pos.le.trans ((P.path_legality η t _ ht hamp.sq_le (indexedGridField_le_margin hamp ξ x)).2.2.1 y)
  exact uniformTernaryParameter_finite_risk P.a (P.v - η ^ 2 * t)
    (indexedGridField d k η ξ) (indexedGridField_continuous d k η ξ).measurable
    P.a_pos.ne' hp T.val _ (T.abs_le C)

/-- Clipped estimators have finite genuine worst-case risk, independently of
which admissible parameter realizes that risk. -/
theorem boundedEstimator_worstCaseRisk_ne_top
    (T : BoundedEstimator C n) : worstCaseRisk C T.val ≠ ∞ := by
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply iSup_le
  intro θ
  exact boundedEstimator_risk_le_diameter C T θ.val θ.property

end

end

end NearlyMinimax
