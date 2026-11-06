module
public import NearlyMinimax.LowSmoothnessVariance
public import NearlyMinimax.ParametricConstants
public import NearlyMinimax.TernaryMeasure
public import NearlyMinimax.ModelRegularity
public import NearlyMinimax.PathRisk
@[expose] public section
noncomputable section
section
open MeasureTheory ProbabilityTheory
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable
section
variable {α : Type*}
attribute [local instance] Classical.propDecidable
def designPatchCount  (n ) (A : Set α) (x : Fin n → α) : ℕ :=
  (Finset.univ.filter fun i => x i ∈ A).card
def designMembershipCell  (n ) (A : Set α) (s : Finset (Fin n)) : Set (Fin n → α) :=
  Set.pi Set.univ (fun i => if i ∈ s then A else Aᶜ)
theorem design_patch_count_le  (n : ℕ) (A : Set α) (x : Fin n → α) :
    designPatchCount n A x ≤ n := by
  unfold designPatchCount
  simpa using Finset.card_le_card (Finset.filter_subset (fun i => x i ∈ A) Finset.univ)
theorem design_membership_cell_iff  (n : ℕ) (A : Set α)
    (s : Finset (Fin n)) (x : Fin n → α) :
    x ∈ designMembershipCell n A s ↔ ∀ i, x i ∈ A ↔ i ∈ s := by
  simp only [designMembershipCell, Set.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · intro h i
    by_cases hi : i ∈ s
    · simpa [hi] using h i
    · simpa [hi] using h i
  · intro h i
    by_cases hi : i ∈ s
    · simpa [hi] using (h i).mpr hi
    · simpa [hi] using (h i).not.mpr hi
theorem design_membership_cell_measurable  [MeasurableSpace α]
    (n : ℕ) (A : Set α) (hA : MeasurableSet A) (s : Finset (Fin n)) :
    MeasurableSet (designMembershipCell n A s) := by
  apply MeasurableSet.pi Set.countable_univ
  intro i _
  split_ifs
  · exact hA
  · exact hA.compl
theorem design_membership_cells_disjoint  (n : ℕ) (A : Set α) :
    Pairwise (fun s t : Finset (Fin n) => Disjoint (designMembershipCell n A s) (designMembershipCell n A t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hs ht
  apply hst
  ext i
  exact ((design_membership_cell_iff n A s x).mp hs i).symm.trans
    ((design_membership_cell_iff n A t x).mp ht i)
theorem design_patch_count_measurable  [MeasurableSpace α]
    (n : ℕ) (A : Set α) (hA : MeasurableSet A) : Measurable (designPatchCount n A) := by
  have heq : designPatchCount n A =
      (fun x => ∑ i : Fin n, if x i ∈ A then 1 else 0) := by
    funext x
    exact Finset.card_filter _ _
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (hA.preimage (measurable_pi_apply i)) measurable_const measurable_const
end
theorem overlap_matrix_sum_bound {ι : Type*} [Fintype ι] (A : ι → ι → Prop)
    (hsym : ∀ i j, A i j ↔ A j i) (D : ℕ) (e : ι → ℝ) (c : ι → ι → ℝ)
    (he : ∀ i, 0 ≤ e i) (hdegree : ∀ i, (Finset.univ.filter (A i)).card ≤ D)
    (hzero : ∀ i j, ¬A i j → c i j = 0)
    (hpair : ∀ i j, c i j ≤ (1 / 2 : ℝ) * (e i + e j)) :
    (∑ i, ∑ j, c i j) ≤ D * ∑ i, e i := by
  have hpoint (i j : ι) : c i j ≤
      (1 / 2 : ℝ) * (if A i j then e i else 0) +
        (1 / 2 : ℝ) * (if A i j then e j else 0) := by
    by_cases h : A i j
    · simp only [if_pos h]
      nlinarith [hpair i j]
    · simp [h, hzero i j h]
  have htranspose : (∑ i, ∑ j, if A i j then e j else 0) =
      ∑ i, ∑ j, if A i j then e i else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have : (∑ i, ∑ j, if A i j then e i else 0) ≤ D * ∑ i, e i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree i) (he i)
  calc
    _ ≤ ∑ i, ∑ j, ((1 / 2 : ℝ) * (if A i j then e i else 0) +
        (1 / 2 : ℝ) * (if A i j then e j else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun j _ => hpoint i j)
    _ = (1 / 2 : ℝ) * (∑ i, ∑ j, if A i j then e i else 0) +
        (1 / 2 : ℝ) * (∑ i, ∑ j, if A i j then e j else 0) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ D * ∑ i, e i := by rw [htranspose]; linarith
theorem finite_overlap_variance_bound  [Fintype Ω] [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (r : ι → Ω → ℝ) (A : ι → ι → Prop) (D : ℕ)
    (hsym : ∀ i j, A i j ↔ A j i) (hdegree : ∀ i, (Finset.univ.filter (A i)).card ≤ D)
    (hzero : ∀ i j, ¬A i j → (∫ x, r i x * r j x ∂μ) = 0) :
    (∫ x, (∑ i, r i x) ^ 2 ∂μ) ≤ D * ∑ i, ∫ x, (r i x) ^ 2 ∂μ := by
  have hpair (i j : ι) : (∫ x, r i x * r j x ∂μ) ≤
      (1 / 2 : ℝ) * ((∫ x, (r i x) ^ 2 ∂μ) + (∫ x, (r j x) ^ 2 ∂μ)) := by
    have h := integral_mono (μ := μ) (f := fun x => r i x * r j x)
      (g := fun x => (1 / 2 : ℝ) * ((r i x) ^ 2 + (r j x) ^ 2))
      Integrable.of_finite Integrable.of_finite (fun x => by nlinarith [sq_nonneg (r i x - r j x)])
    rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite] at h
    exact h
  calc
    _ = ∫ x, ∑ i, ∑ j, r i x * r j x ∂μ := by
      congr 1
      funext x
      rw [pow_two, Fintype.sum_mul_sum]
    _ = ∑ i, ∑ j, ∫ x, r i x * r j x ∂μ := by
      rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
    _ ≤ _ := overlap_matrix_sum_bound A hsym D (fun i => ∫ x, (r i x) ^ 2 ∂μ)
      (fun i j => ∫ x, r i x * r j x ∂μ) (fun i => integral_nonneg (fun x => sq_nonneg _))
      hdegree hzero hpair
theorem finite_product_local_scores_orthogonal (n μ) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Finset (Fin n)) (hST : Disjoint S T)
    (R : (S → Fin 3) → ℝ) (Q : (T → Fin 3) → ℝ)
    (hR : (∫ y : Fin n → Fin 3, R (fun i : S => y i) ∂Measure.pi μ) = 0) :
    (∫ y : Fin n → Fin 3, R (fun i : S => y i) * Q (fun i : T => y i) ∂Measure.pi μ) = 0 := by
  have h_finite_product_local_observables_independent : IndepFun (fun y : Fin n → Fin 3 => R (fun i : S => y i))
      (fun y : Fin n → Fin 3 => Q (fun i : T => y i)) (Measure.pi μ) := by
    have hi : iIndepFun (fun i (y : Fin n → Fin 3) => y i) (Measure.pi μ) :=
      iIndepFun_pi (fun _ => measurable_id.aemeasurable)
    have h := hi.indepFun_finset S T hST (fun i => measurable_pi_apply i)
    exact h.comp (measurable_of_countable R) (measurable_of_countable Q)
  have hi := h_finite_product_local_observables_independent
  rw [hi.integral_fun_mul_eq_mul_integral
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable, hR, zero_mul]
def ternaryIndexMeasure (a f V ) (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a f V y) : Measure (Fin 3) :=
  (PMF.ofFintype (fun y => ENNReal.ofReal (ternaryMass a f V y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp y), ternary_normalized a f V ha]
    norm_num)).toMeasure
instance ternaryIndexMeasure_isProbability (a f V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) : IsProbabilityMeasure (ternaryIndexMeasure a f V ha hp) :=
  PMF.toMeasure.isProbabilityMeasure _
theorem ternary_index_measure_singleton (a f V ha hp y) :
    (ternaryIndexMeasure a f V ha hp).real {y} = ternaryMass a f V y := by
  rw [measureReal_def, ternaryIndexMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)]
  exact ENNReal.toReal_ofReal (hp y)
theorem ternary_index_product_integral (n a V) (f : Fin n → ℝ) (ha : a ≠ 0)
    (hp : ∀ i y, 0 ≤ ternaryMass a (f i) V y) (F : (Fin n → Fin 3) → ℝ) :
    (∫ y, F y ∂Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (hp i))) =
      ∑ y, (∏ i, ternaryMass a (f i) V (y i)) * F y := by
  have h_ternary_index_product_singleton (y : Fin n → Fin 3) : (Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (hp i))).real {y} =
      ∏ i, ternaryMass a (f i) V (y i) := by
    have heq : ({y} : Set (Fin n → Fin 3)) = Set.pi Set.univ (fun i => ({y i} : Set (Fin 3))) := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro h
        subst x
        simp
      · intro h
        funext i
        exact h i
    rw [measureReal_def, heq, Measure.pi_pi, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact ternary_index_measure_singleton a (f i) V ha (hp i) (y i)
  rw [integral_fintype Integrable.of_finite]
  simp_rw [h_ternary_index_product_singleton, smul_eq_mul]
end NearlyMinimax
end
section
namespace NearlyMinimax
open MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
theorem latent_coordinate_score_eq_patch (m n a V η base w ξ j y) :
    finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j =
      patchObservableScore n a V η (latentRegressionWithout m n η base w ξ j)
        (fun i => w i j) y (ternaryValue 1 (ξ j)) := by
  unfold finiteCoordinateScore finiteCoordinateScoreNumerator patchObservableScore patchScoreNumerator
  have h_latent_regression_likelihood_difference : latentDifference m j
      (fun ξ' => finiteResponseLikelihood m n a V (latentRegression m n η base w) ξ' y) ξ =
      symmetricDifference (patchResponseProduct n a V η
        (latentRegressionWithout m n η base w ξ j) (fun i => w i j) y) := by
    simp [latentDifference, finiteResponseLikelihood, symmetricDifference,
      patchResponseProduct, latent_regression_update, ternaryValue]
  have h_latent_regression_variance_term (y : Fin n → Fin 3) (i : Fin n) : finiteResponseVarianceTerm m n a V (latentRegression m n η base w) ξ y i =
      patchVarianceTerm n a V η (latentRegressionWithout m n η base w ξ j)
        (fun k => w k j) y (ternaryValue 1 (ξ j)) i := by
    simp [finiteResponseVarianceTerm, patchVarianceTerm, latent_regression_decomposition m n η base w ξ j]
  rw [h_latent_regression_likelihood_difference]
  simp_rw [h_latent_regression_variance_term]
  have hL : finiteResponseLikelihood m n a V (latentRegression m n η base w) ξ y =
      patchResponseProduct n a V η (latentRegressionWithout m n η base w ξ j)
        (fun i => w i j) y (ternaryValue 1 (ξ j)) := by
    simp [finiteResponseLikelihood, patchResponseProduct,
      latent_regression_decomposition m n η base w ξ j]
  rw [hL]
def extendPatchResponses (n : ℕ) (S : Finset (Fin n)) (y : S → Fin 3) : Fin n → Fin 3 :=
  fun i => if hi : i ∈ S then y ⟨i, hi⟩ else 1
theorem latent_full_score_variance_bound (m n a V η base w ξ)
    (S : Fin m → Finset (Fin n)) (D : ℕ)
    (hw : ∀ j i, i ∉ S j → w i j = 0)
    (hsquares : ∀ i, ∑ j, (w i j) ^ 2 = 1)
    (hdegree : ∀ j, (Finset.univ.filter fun k => ¬Disjoint (S j) (S k)).card ≤ D)
    (ha : a ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (latentRegression m n η base w ξ i) V b) :
    (∫ y : Fin n → Fin 3,
      (finiteExperimentScore m n a V η (latentRegression m n η base w) ξ y) ^ 2
      ∂Measure.pi (fun i => ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha
        (fun b => (hp i b).le))) ≤
      D * ∑ j, ∫ y : Fin n → Fin 3,
        (finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j) ^ 2
        ∂Measure.pi (fun i => ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha
          (fun b => (hp i b).le)) := by
  have h_latent_coordinate_score_depends_on_support (j : Fin m) (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i j = 0) (y) (y') (hyy : ∀ i ∈ S, y i = y' i) (hp : ∀ i b, 0 < ternaryMass a (latentRegression m n η base w ξ i) V b) : finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j =
      finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y' j := by
    have h_patch_score_ratio_representation (z) (g) (w) (y) (hp : ∀ k, 0 < ternaryMass a (g k + η * w k * z) V (y k)) : patchObservableScore n a V η g w y z =
        symmetricDifference (patchResponseProduct n a V η g w y) /
          patchResponseProduct n a V η g w y z -
        η ^ 2 * ∑ i, (w i) ^ 2 *
          (ternaryVarianceDerivative a (y i) / ternaryMass a (g i + η * w i * z) V (y i)) := by
      unfold patchObservableScore patchScoreNumerator
      have h_patch_variance_ratio (i) : patchVarianceTerm n a V η g w y z i / patchResponseProduct n a V η g w y z =
          ternaryVarianceDerivative a (y i) / ternaryMass a (g i + η * w i * z) V (y i) := by
        unfold patchVarianceTerm patchResponseProduct
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        exact mul_div_mul_right _ _ (ne_of_gt (Finset.prod_pos (fun k _ => hp k)))
      rw [sub_div]
      simp_rw [mul_div_assoc, Finset.sum_div, mul_div_assoc, (h_patch_variance_ratio _)]
    rw [latent_coordinate_score_eq_patch, latent_coordinate_score_eq_patch]
    have h_patch_score_depends_on_support (z) (g) (w) (hw : ∀ i, i ∉ S → w i = 0) (hp : ∀ i b, 0 < ternaryMass a (g i + η * w i * z) V b) : patchObservableScore n a V η g w y z = patchObservableScore n a V η g w y' z := by
      let outside (v : Fin n → Fin 3) : ℝ :=
        ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, ternaryMass a (g i) V (v i)
      let inside (v : Fin n → Fin 3) u : ℝ :=
        ∏ i ∈ S, ternaryMass a (g i + η * w i * u) V (v i)
      have hfactor (v : Fin n → Fin 3) u :
          patchResponseProduct n a V η g w v u = outside v * inside v u := by
        unfold patchResponseProduct
        rw [← Finset.prod_sdiff (Finset.subset_univ S)]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        simp [hw i (Finset.mem_sdiff.mp hi).2]
      have hout (v : Fin n → Fin 3) : outside v ≠ 0 := by
        apply ne_of_gt
        apply Finset.prod_pos
        intro i hi
        simpa [hw i (Finset.mem_sdiff.mp hi).2] using hp i (v i)
      have hin (v : Fin n → Fin 3) : inside v z ≠ 0 := by
        exact ne_of_gt (Finset.prod_pos (fun i _ => hp i (v i)))
      have hs u : inside y u = inside y' u := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hyy i hi]
      have hratio u : patchResponseProduct n a V η g w y u /
          patchResponseProduct n a V η g w y z =
          patchResponseProduct n a V η g w y' u / patchResponseProduct n a V η g w y' z := by
        rw [hfactor y u, hfactor y z, hfactor y' u, hfactor y' z, hs u, hs z]
        field_simp [hout y, hout y', hin y']
      rw [h_patch_score_ratio_representation z g w y (fun i => hp i (y i)),
        h_patch_score_ratio_representation z g w y' (fun i => hp i (y' i))]
      congr 1
      · unfold symmetricDifference
        simp only [sub_div, add_div, mul_div_assoc]
        rw [hratio 1, hratio (-1), hratio 0]
      · congr 1
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · rw [hyy i hi]
        · simp [hw i hi]
    apply h_patch_score_depends_on_support (ternaryValue 1 (ξ j)) (latentRegressionWithout m n η base w ξ j) (fun i => w i j) hw
    intro i b
    simpa [latent_regression_decomposition m n η base w ξ j] using hp i b
  have h_finite_experiment_score_decomposition (f) (y) : finiteExperimentScore m n a V η f ξ y =
      ∑ j, finiteCoordinateScore m n a V η f w ξ y j := by
    unfold finiteExperimentScore finiteCoordinateScore
    have h_finite_experiment_score_numerator_decomposition : finiteExperimentScoreNumerator m n a V η f ξ y =
        ∑ j, finiteCoordinateScoreNumerator m n a V η f w ξ y j := by
      unfold finiteExperimentScoreNumerator finiteCoordinateScoreNumerator
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul, hsquares]
      simp
    rw [h_finite_experiment_score_numerator_decomposition,
      Finset.sum_div]
  simp_rw [h_finite_experiment_score_decomposition (latentRegression m n η base w) _]
  apply finite_overlap_variance_bound _ _ (fun j k => ¬Disjoint (S j) (S k)) D
  · intro j k
    exact not_congr disjoint_comm
  · intro j
    convert hdegree j using 1
    congr 1
    ext k
    simp
  · intro j k hjk
    let r : Fin m → (Fin n → Fin 3) → ℝ :=
      fun j y => finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j
    let R : ((S j) → Fin 3) → ℝ := fun y => r j (extendPatchResponses n (S j) y)
    let Q : ((S k) → Fin 3) → ℝ := fun y => r k (extendPatchResponses n (S k) y)
    let μ : Fin n → Measure (Fin 3) := fun i =>
      ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha (fun b => (hp i b).le)
    have hR (y : Fin n → Fin 3) : r j y = R (fun i : (S j) => y i) := by
      apply h_latent_coordinate_score_depends_on_support j (S j) (hw j)
        y (extendPatchResponses n (S j) (fun i : (S j) => y i)) _ hp
      intro i hi
      simp [extendPatchResponses, hi]
    have hQ (y : Fin n → Fin 3) : r k y = Q (fun i : (S k) => y i) := by
      apply h_latent_coordinate_score_depends_on_support k (S k) (hw k)
        y (extendPatchResponses n (S k) (fun i : (S k) => y i)) _ hp
      intro i hi
      simp [extendPatchResponses, hi]
    have h_finite_coordinate_score_centered (f) (hpositive : ∀ y, 0 < finiteResponseLikelihood m n a V f ξ y) : ∑ y : Fin n → Fin 3,
        finiteResponseLikelihood m n a V f ξ y * finiteCoordinateScore m n a V η f w ξ y j = 0 := by
      have heq (y : Fin n → Fin 3) :
          finiteResponseLikelihood m n a V f ξ y * finiteCoordinateScore m n a V η f w ξ y j =
            finiteCoordinateScoreNumerator m n a V η f w ξ y j := by
        unfold finiteCoordinateScore
        field_simp [ne_of_gt (hpositive y)]
      simp_rw [heq]
      unfold finiteCoordinateScoreNumerator latentDifference
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
      simp_rw [← Finset.mul_sum, finite_response_variance_term_sum_zero]
      simp [finite_response_normalized m n a V f _ ha]
      ring
    change (∫ y, r j y * r k y ∂Measure.pi μ) = 0
    simp_rw [hR, hQ]
    exact (finite_product_local_scores_orthogonal n μ (S j) (S k) (not_not.mp hjk) R Q (by simp_rw [← hR]; have hpositive : ∀ y, 0 < finiteResponseLikelihood m n a V (latentRegression m n η base w) ξ y := (by intro y; exact Finset.prod_pos (fun i _ => hp i (y i))); rw [ternary_index_product_integral]; exact (h_finite_coordinate_score_centered (latentRegression m n η base w) hpositive)))
end
end NearlyMinimax
end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
theorem ternaryMass_measurable_comp  [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (y : Fin 3) :
    Measurable (fun x => ternaryMass a (F x) V y) := by
  fin_cases y <;> simp [ternaryMass] <;> fun_prop
def ternaryErrorKernel  [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) : Kernel α ℝ where
  toFun x := ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F x) V y) •
    Measure.dirac (ternaryValue a y - F x)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hs]
    apply Finset.measurable_sum
    intro y _
    exact (ENNReal.measurable_ofReal.comp (ternaryMass_measurable_comp a V F hF y)).mul
      (measurable_const.indicator ((measurable_const.sub hF) hs))
theorem ternaryErrorKernel_apply  [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : α) :
    ternaryErrorKernel a V F hF x = ∑ y : Fin 3,
      ENNReal.ofReal (ternaryMass a (F x) V y) •
        Measure.dirac (ternaryValue a y - F x) := rfl
theorem ternaryErrorKernel_markov  [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (ternaryErrorKernel a V F hF) := by
  constructor
  intro x
  constructor
  simp only [ternaryErrorKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp x y), ternary_normalized a (F x) V ha]
  simp
theorem ternary_error_integrable  [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : α) (G : ℝ → ℝ) :
    Integrable G (ternaryErrorKernel a V F hF x) := by
  rw [ternaryErrorKernel_apply]
  apply integrable_finsetSum_measure.mpr
  intro y _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
theorem ternary_error_integral  [MeasurableSpace α]
    (a V F hF) (x : α)
    (hp : ∀ y, 0 ≤ ternaryMass a (F x) V y) (G : ℝ → ℝ) :
    (∫ u, G u ∂ternaryErrorKernel a V F hF x) =
      ∑ y, ternaryMass a (F x) V y * G (ternaryValue a y - F x) := by
  rw [ternaryErrorKernel_apply, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (hp _)]
  · intro y _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
theorem ternary_error_mean  [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : α)
    (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a (F x) V y) :
    (∫ u, u ∂ternaryErrorKernel a V F hF x) = 0 := by
  rw [ternary_error_integral a V F hF x hp]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hm := ternary_mean a (F x) V ha
  change (∑ y, ternaryMass a (F x) V y * ternaryValue a y) = F x at hm
  rw [hm, ternary_normalized a (F x) V ha]
  ring
theorem ternary_error_variance  [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : α)
    (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a (F x) V y) :
    (∫ u, u ^ 2 ∂ternaryErrorKernel a V F hF x) = V := by
  rw [ternary_error_integral a V F hF x hp]
  exact ternary_variance a (F x) V ha
theorem ternary_error_fourth  [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : α)
    (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a (F x) V y) :
    (∫ u, u ^ 4 ∂ternaryErrorKernel a V F hF x) =
      a ^ 2 * V + (6 * V - 3 * a ^ 2) * (F x) ^ 2 + 3 * (F x) ^ 4 := by
  rw [ternary_error_integral a V F hF x hp]
  exact ternary_fourth_central_moment a (F x) V ha
def uniformTernaryParameter {d : ℕ} (a V : ℝ) (F : Covariate d → ℝ)
    (hF : Measurable F) (ha : a ≠ 0) (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    RegressionParameter d := {
  density := fun _ => 1
  regression := F
  variance := V
  errors := ternaryErrorKernel a V F hF
  errors_markov := ternaryErrorKernel_markov a V F hF ha hp }
theorem uniformTernaryParameter_admissible_order_zero  (C : ModelConstants d)
    (a V F) (hF : Continuous F) (horder : C.order = 0)
    (ha hp)
    (hVlo : C.varianceLower ≤ V) (hVhi : V ≤ C.varianceUpper)
    (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H) (hbudget : M + H ≤ C.holderBound)
    (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |F x - F y| ≤ H * euclideanNorm (x - y) ^ C.smoothness)
    (hfourth : ∀ x, a ^ 2 * V + (6 * V - 3 * a ^ 2) * (F x) ^ 2 +
      3 * (F x) ^ 4 ≤ C.fourthBound) :
    Admissible C (uniformTernaryParameter a V F hF.measurable ha hp) := by
  refine ⟨measurable_const, hF.measurable, ?_, ?_, ?_, hVlo, hVhi, ?_⟩
  · exact Filter.Eventually.of_forall (fun _ =>
      ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩)
  · simp only [uniformTernaryParameter, ENNReal.ofReal_one, lintegral_const, one_mul]
    exact cubeVolume_univ d
  · refine ⟨F, fun _ _ => rfl, ?_, ?_⟩
    · simpa [horder] using
        (contDiffOn_zero.mpr hF.continuousOn : ContDiffOn ℝ 0 F C.domain)
    · have hα : C.alpha = C.smoothness := by simp [ModelConstants.alpha, horder]
      rw [horder, hα]
      have h_holderNorm_order_zero_of_global_bounds : holderNorm C.domain F 0 C.smoothness ≤ ENNReal.ofReal (M + H) := by
        have hh : holderSeminorm C.domain F C.smoothness ≤ ENNReal.ofReal H := by
          apply iSup_le
          intro x
          apply iSup_le
          intro y
          by_cases hxy : (x : Covariate d) = y
          · simp [hxy]
          · simp only [ite_eq_right_iff.mpr (fun h => False.elim (hxy h))]
            apply ENNReal.ofReal_le_ofReal
            exact (div_le_iff₀ (Real.rpow_pos_of_pos
              (euclideanNorm_pos_of_ne_zero (x.val - y.val) (sub_ne_zero.mpr hxy)) C.smoothness)).mpr
                (hmod x y)
        rw [holderNorm_order_zero, ENNReal.ofReal_add hM hH]
        exact add_le_add (by apply iSup_le; intro x; exact ENNReal.ofReal_le_ofReal (hsup x)) hh
      exact h_holderNorm_order_zero_of_global_bounds.trans (ENNReal.ofReal_le_ofReal hbudget)
  · apply Filter.Eventually.of_forall
    intro x
    refine ⟨ternary_error_integrable a V F hF.measurable x _,
      ternary_error_integrable a V F hF.measurable x _,
      ternary_error_integrable a V F hF.measurable x _,
      ternary_error_mean a V F hF.measurable x ha (hp x),
      ternary_error_variance a V F hF.measurable x ha (hp x), ?_⟩
    exact (ternary_error_fourth a V F hF.measurable x ha (hp x)).trans_le (hfourth x)
structure LowSmoothnessTernaryConstants {d : ℕ} (C : ModelConstants d) where
  a : ℝ
  v : ℝ
  ρ : ℝ
  c : ℝ
  a_pos : 0 < a
  ρ_pos : 0 < ρ
  c_pos : 0 < c
  legal : ∀ f V, |f| ≤ ρ → |V - v| ≤ ρ →
    C.varianceLower < V ∧ V < C.varianceUpper ∧
      (∀ y, c ≤ ternaryMass a f V y) ∧
      ternaryExpectation a f V (fun y => (y - f) ^ 4) ≤ C.fourthBound
theorem lowSmoothnessTernaryConstants_exists  (C : ModelConstants d) :
    Nonempty (LowSmoothnessTernaryConstants C) := by
  obtain ⟨P⟩ := parametricTernaryConstants_exists C
  let v := (P.l + P.r) / 2
  have hv : 0 < v := by dsimp [v]; linarith [P.l_pos, P.interval]
  have hVl : C.varianceLower < v := by dsimp [v]; linarith [P.lower_le, P.interval]
  have hVr : v < C.varianceUpper := by dsimp [v]; linarith [P.upper_le, P.interval]
  have hva : v < P.a ^ 2 := by dsimp [v]; linarith [P.variance_lt_square, P.interval]
  have hmid : v < P.r := by dsimp [v]; linarith [P.interval]
  have hfourth := (mul_lt_mul_of_pos_left hmid (sq_pos_of_pos P.a_pos)).trans_le P.fourth_le
  have h_ternary_admissible_neighborhood (a) (vMinus) (vPlus) (C4) (ha : 0 < a) (hva : v < a ^ 2) (hvMinus : vMinus < v) (hvPlus : v < vPlus) (hC4 : a ^ 2 * v < C4) : ∃ ρ c, 0 < ρ ∧ 0 < c ∧
      ∀ f V, |f| ≤ ρ → |V - v| ≤ ρ →
        vMinus < V ∧ V < vPlus ∧
        (∀ y : Fin 3, c ≤ ternaryMass a f V y) ∧
        ternaryExpectation a f V (fun y => (y - f) ^ 4) ≤ C4 := by
    let p : ℝ := v / (2 * a ^ 2)
    let q : ℝ := 1 - v / a ^ 2
    let c : ℝ := min p q / 2
    have hp : 0 < p := div_pos hv (by positivity)
    have hq : 0 < q := sub_pos.mpr ((div_lt_one (sq_pos_of_pos ha)).mpr hva)
    have hcp : c < p := by dsimp [c]; linarith [min_le_left p q]
    have hmass0 : ∀ y : Fin 3, c < ternaryMass a 0 v y := by
      intro y
      fin_cases y
      · simpa [ternaryMass, p] using hcp
      · simpa [ternaryMass, q] using (by dsimp [c]; linarith [min_le_right p q])
      · simpa [ternaryMass, p] using hcp
    have hmassCont : ∀ y : Fin 3,
        Continuous (fun x : ℝ × ℝ => ternaryMass a x.1 x.2 y) := by
      intro y
      fin_cases y <;> simp [ternaryMass] <;> fun_prop
    have hmassEvent : ∀ᶠ x : ℝ × ℝ in nhds (0, v),
        ∀ y : Fin 3, c < ternaryMass a x.1 x.2 y := by
      exact Filter.eventually_all.mpr (fun y =>
        continuousAt_const.eventually_lt (hmassCont y).continuousAt (hmass0 y))
    have hfourthCont : Continuous (fun x : ℝ × ℝ =>
        a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4) := by
      fun_prop
    have hfourth : ∀ᶠ x : ℝ × ℝ in nhds (0, v),
        a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4 < C4 := by
      apply hfourthCont.continuousAt.eventually_lt continuousAt_const
      simpa using hC4
    have hevent : ∀ᶠ x : ℝ × ℝ in nhds (0, v),
        vMinus < x.2 ∧ x.2 < vPlus ∧
        (∀ y : Fin 3, c < ternaryMass a x.1 x.2 y) ∧
        a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4 < C4 := by
      filter_upwards [continuousAt_const.eventually_lt continuous_snd.continuousAt hvMinus, (continuous_snd.continuousAt.eventually_lt continuousAt_const hvPlus), hmassEvent, hfourth] with x hm hp hq hf
      exact ⟨hm, hp, hq, hf⟩
    obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp hevent
    refine ⟨ε / 2, c, by positivity, div_pos (lt_min hp hq) (by norm_num), ?_⟩
    intro f V hf hV
    have hdist : dist (f, V) (0, v) < ε := by
      simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
      exact max_lt (by linarith) (by linarith)
    obtain ⟨hm, hp, hq, hfourth⟩ := hbound hdist
    refine ⟨hm, hp, fun y => (hq y).le, ?_⟩
    rw [ternary_fourth_central_moment a f V (ne_of_gt ha)]
    exact hfourth.le
  obtain ⟨ρ, c, hρ, hc, hlegal⟩ := h_ternary_admissible_neighborhood P.a C.varianceLower C.varianceUpper C.fourthBound P.a_pos hva hVl hVr hfourth
  exact ⟨⟨P.a, v, ρ, c, P.a_pos, hρ, hc, hlegal⟩⟩
namespace LowSmoothnessTernaryConstants
variable {d : ℕ} {C : ModelConstants d} (P : LowSmoothnessTernaryConstants C)
def variancePath (η t : ℝ) : ℝ := P.v - η ^ 2 * t
theorem variance_path_distance (η t ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |P.variancePath η t - P.v| ≤ η ^ 2 := by
  simp only [variancePath, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg η),
    abs_of_nonneg ht.1]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 (sq_nonneg η)
theorem path_legality (η t f ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hη : η ^ 2 ≤ P.ρ) (hf : |f| ≤ P.ρ) :
    C.varianceLower < P.variancePath η t ∧ P.variancePath η t < C.varianceUpper ∧
      (∀ y, P.c ≤ ternaryMass P.a f (P.variancePath η t) y) ∧
      ternaryExpectation P.a f (P.variancePath η t) (fun y => (y - f) ^ 4) ≤ C.fourthBound :=
  P.legal f (P.variancePath η t) hf ((P.variance_path_distance η t ht).trans hη)
def pathParameter (F : Covariate d → ℝ) (hF : Continuous F) (η t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hη : η ^ 2 ≤ P.ρ) (hf : ∀ x, |F x| ≤ P.ρ) :
    RegressionParameter d :=
  uniformTernaryParameter P.a (P.variancePath η t) F hF.measurable P.a_pos.ne'
    (fun x y => P.c_pos.le.trans ((P.path_legality η t (F x) ht hη (hf x)).2.2.1 y))
theorem pathParameter_admissible_order_zero (F hF η t ht hη hf)
    (horder : C.order = 0) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hbudget : M + H ≤ C.holderBound) (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |F x - F y| ≤ H * euclideanNorm (x - y) ^ C.smoothness) :
    Admissible C (P.pathParameter F hF η t ht hη hf) := by
  have hlegal (x : Covariate d) := P.path_legality η t (F x) ht hη (hf x)
  apply uniformTernaryParameter_admissible_order_zero C P.a (P.variancePath η t) F hF horder P.a_pos.ne'
    _ (hlegal 0).1.le (hlegal 0).2.1.le M H hM hH hbudget hsup hmod
  intro x
  have hf4 := (hlegal x).2.2.2
  rw [ternary_fourth_central_moment P.a (F x) (P.variancePath η t) P.a_pos.ne'] at hf4
  exact hf4
end LowSmoothnessTernaryConstants
end NearlyMinimax
