module

public import NearlyMinimax.OverlapVariance


@[expose] public section

/-! # Local support of the actual observable scores

The other likelihood factors cancel from a patch score. Consequently its
value depends only on responses inside the window's support, and actual
coordinate scores on disjoint supports are orthogonal.
-/

namespace NearlyMinimax

open MeasureTheory ProbabilityTheory

noncomputable section

attribute [local instance] Classical.propDecidable

section
variable {ι : Type*} [Fintype ι]

/-- Common cancellation of linear derivative scores for product likelihoods. -/
theorem product_erase_div_product [DecidableEq ι]
    (q : ι → ℝ) (i : ι) (d : ℝ) (hq : ∀ j, q j ≠ 0) :
    (d * ∏ j ∈ Finset.univ.erase i, q j) / (∏ j, q j) = d / q i := by
  rw [← Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)]
  exact mul_div_mul_right _ _ (Finset.prod_ne_zero_iff.mpr fun j _ => hq j)

/-- Ratios cancel at coordinates where the state is unchanged. -/
theorem prod_div_eq_prod_support (S : Finset ι) (f q : ι → ℝ)
    (h : ∀ i, i ∉ S → f i = q i) (hq : ∀ i, q i ≠ 0) :
    (∏ i, f i) / (∏ i, q i) = ∏ i ∈ S, f i / q i := by
  rw [← Finset.prod_div_distrib]
  exact (Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => by rw [h i hi, div_self (hq i)])).symm

end

section
variable (n : ℕ) (a V η z : ℝ) (g w : Fin n → ℝ)

section
variable (y : Fin n → Fin 3)

private theorem patch_variance_ratio (i : Fin n)
    (hp : ∀ k, 0 < ternaryMass a (g k + η * w k * z) V (y k)) :
    patchVarianceTerm n a V η g w y z i / patchResponseProduct n a V η g w y z =
      ternaryVarianceDerivative a (y i) / ternaryMass a (g i + η * w i * z) V (y i) :=
  product_erase_div_product _ i _ (fun j => (hp j).ne')

theorem patch_score_ratio_formula
    (hp : ∀ k, 0 < ternaryMass a (g k + η * w k * z) V (y k)) :
    patchObservableScore n a V η g w y z =
      symmetricDifference (patchResponseProduct n a V η g w y) /
        patchResponseProduct n a V η g w y z -
      η ^ 2 * ∑ i, (w i) ^ 2 *
        (ternaryVarianceDerivative a (y i) / ternaryMass a (g i + η * w i * z) V (y i)) := by
  unfold patchObservableScore patchScoreNumerator
  simp_all [sub_div, mul_div_assoc, Finset.sum_div, patch_variance_ratio n a V η z g w y _ hp]

end

/-- A patch score depends only on response coordinates in the support of its window. -/
theorem patch_score_depends_on_support
    (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    (y y' : Fin n → Fin 3) (hyy : ∀ i ∈ S, y i = y' i)
    (hp : ∀ i b, 0 < ternaryMass a (g i + η * w i * z) V b) :
    patchObservableScore n a V η g w y z = patchObservableScore n a V η g w y' z := by
  have hr (v : Fin n → Fin 3) (u : ℝ) :
      patchResponseProduct n a V η g w v u / patchResponseProduct n a V η g w v z =
      ∏ i ∈ S, ternaryMass a (g i + η * w i * u) V (v i) /
        ternaryMass a (g i + η * w i * z) V (v i) :=
    prod_div_eq_prod_support S _ _ (fun i hi => by simp [hw i hi]) (fun i => (hp i _).ne')
  have hratio (u : ℝ) : patchResponseProduct n a V η g w y u /
      patchResponseProduct n a V η g w y z =
      patchResponseProduct n a V η g w y' u / patchResponseProduct n a V η g w y' z := by
    rw [hr, hr]
    exact Finset.prod_congr rfl (fun i hi => by rw [hyy i hi])
  rw [patch_score_ratio_formula n a V η z g w y (fun i => hp i (y i)),
    patch_score_ratio_formula n a V η z g w y' (fun i => hp i (y' i))]
  congr 1
  · grind [symmetricDifference, patchResponseProduct]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · rw [hyy i hi]
    · simp [hw i hi]

end

section
variable (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)
    (j : Fin m)

/-- The actual coordinate score agrees with its one-dimensional patch representation. -/
theorem latent_coordinate_score_eq_patch (y : Fin n → Fin 3) :
    finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j =
      patchObservableScore n a V η (latentRegressionWithout m n η base w ξ j)
        (fun i => w i j) y (ternaryValue 1 (ξ j)) := by
  unfold finiteCoordinateScore finiteCoordinateScoreNumerator patchObservableScore patchScoreNumerator
  rw [latent_regression_likelihood_difference]
  simp_rw [latent_regression_variance_term m n a V η base w ξ j]
  have hL : finiteResponseLikelihood m n a V (latentRegression m n η base w) ξ y =
      patchResponseProduct n a V η (latentRegressionWithout m n η base w ξ j)
        (fun i => w i j) y (ternaryValue 1 (ξ j)) := by
    simp [finiteResponseLikelihood, patchResponseProduct,
      latent_regression_decomposition m n η base w ξ j]
  simp_all

/-- Exact locality of the actual full-field coordinate score. -/
theorem latent_coordinate_score_depends_on_support (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i j = 0)
    (y y' : Fin n → Fin 3) (hyy : ∀ i ∈ S, y i = y' i)
    (hp : ∀ i b, 0 < ternaryMass a (latentRegression m n η base w ξ i) V b) :
    finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j =
      finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y' j := by
  rw [latent_coordinate_score_eq_patch, latent_coordinate_score_eq_patch]
  apply patch_score_depends_on_support n a V η (ternaryValue 1 (ξ j))
    (latentRegressionWithout m n η base w ξ j) (fun i => w i j) S hw y y' hyy
  intro i b
  simpa [latent_regression_decomposition m n η base w ξ j] using hp i b

end

/-- Extend a local response tuple by the zero response index outside its support. -/
def extendPatchResponses (n : ℕ) (S : Finset (Fin n)) (y : S → Fin 3) : Fin n → Fin 3 :=
  fun i => if hi : i ∈ S then y ⟨i, hi⟩ else 1

/-- Product-law orthogonality from local response dependence and actual
conditional centering. This helper is used below only with properties proved
from the explicit signed density-response packet. -/
theorem local_response_scores_orthogonal {n : ℕ}
    (μ : Fin n → Measure (Fin 3)) [∀ i, IsProbabilityMeasure (μ i)]
    (r s : (Fin n → Fin 3) → ℝ) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hr : ∀ y y', (∀ i ∈ S, y i = y' i) → r y = r y')
    (hs : ∀ y y', (∀ i ∈ T, y i = y' i) → s y = s y')
    (hc : (∫ y, r y ∂Measure.pi μ) = 0) :
    (∫ y, r y * s y ∂Measure.pi μ) = 0 := by
  let R (y : S → Fin 3) := r (extendPatchResponses n S y)
  let Q (y : T → Fin 3) := s (extendPatchResponses n T y)
  have hR (y : Fin n → Fin 3) : r y = R (fun i : S => y i) := by
    apply hr
    intro i hi
    simp [extendPatchResponses, hi]
  have hQ (y : Fin n → Fin 3) : s y = Q (fun i : T => y i) := by
    apply hs
    intro i hi
    simp [extendPatchResponses, hi]
  have hcenter : (∫ y, R (fun i : S => y i) ∂Measure.pi μ) = 0 := by
    simpa only [← hR] using hc
  simp_rw [hR, hQ]
  exact finite_product_local_scores_orthogonal n μ S T hST R Q hcenter


section
variable (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)

/-- Actual coordinate scores on disjoint supports are orthogonal under the
actual conditional ternary response product measure. -/
theorem latent_coordinate_scores_orthogonal
    (j k : Fin m) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hwS : ∀ i, i ∉ S → w i j = 0) (hwT : ∀ i, i ∉ T → w i k = 0)
    (ha : a ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (latentRegression m n η base w ξ i) V b) :
    (∫ y : Fin n → Fin 3,
      finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j *
        finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y k
      ∂Measure.pi (fun i => ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha
        (fun b => (hp i b).le))) = 0 := by
  let r :=
    fun j y => finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j
  let μ : Fin n → Measure (Fin 3) := fun i =>
    ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha (fun b => (hp i b).le)
  apply local_response_scores_orthogonal μ (r j) (r k) S T hST
    (fun y y' h => latent_coordinate_score_depends_on_support m n a V η base w ξ j S hwS y y' h hp)
    (fun y y' h => latent_coordinate_score_depends_on_support m n a V η base w ξ k T hwT y y' h hp)
  exact ternary_coordinate_score_measure_centered m n a V η (latentRegression m n η base w)
    w ξ j ha (fun i b => (hp i b).le) (fun y => Finset.prod_pos fun i _ => hp i (y i))

section
variable (S : Fin m → Finset (Fin n)) (D : ℕ)
    (hw : ∀ j i, i ∉ S j → w i j = 0)
include hw

/-- Bounded-overlap aggregation for the actual full-field coordinate scores.
No orthogonality hypothesis is assumed: it follows from their local supports
and the actual conditional ternary response product measure. -/
theorem latent_coordinate_score_variance_bound
    (hdegree : ∀ j, (Finset.univ.filter fun k => ¬Disjoint (S j) (S k)).card ≤ D)
    (ha : a ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (latentRegression m n η base w ξ i) V b) :
    (∫ y : Fin n → Fin 3,
      (∑ j, finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j) ^ 2
      ∂Measure.pi (fun i => ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha
        (fun b => (hp i b).le))) ≤
      D * ∑ j, ∫ y : Fin n → Fin 3,
        (finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j) ^ 2
        ∂Measure.pi (fun i => ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha
          (fun b => (hp i b).le)) := by
  apply finite_overlap_variance_bound _ _ (fun j k => ¬Disjoint (S j) (S k)) D
  · intro j k
    exact not_congr disjoint_comm
  · intro j
    convert hdegree j using 1
    congr 1
    ext k
    simp
  · intro j k hjk
    exact latent_coordinate_scores_orthogonal m n a V η base w ξ j k (S j) (S k)
      (not_not.mp hjk) (hw j) (hw k) ha hp

/-- The full observable score inherits that bounded-overlap conditional energy bound. -/
theorem latent_full_score_variance_bound
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
  simp_rw [finite_experiment_score_decomposition m n a V η
    (latentRegression m n η base w) w ξ _ hsquares]
  apply latent_coordinate_score_variance_bound <;> assumption

end

end

end

end NearlyMinimax
