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
variable {n : ℕ} (a V η z : ℝ) (g w : Fin n → ℝ)

/-- A finite likelihood ratio only depends on responses where the numerator
and denominator kernels differ. No normalization of either kernel is needed. -/
theorem product_ratio_depends_on {ι Y : Type*} [Fintype ι] (f g : ι → Y → ℝ)
    {S : Finset ι} (he : ∀ i ∉ S, f i = g i) (hg : ∀ i y, g i y ≠ 0)
    {y y' : ι → Y} (hy : ∀ i ∈ S, y i = y' i) :
    (∏ i, f i (y i)) / (∏ i, g i (y i)) = (∏ i, f i (y' i)) / ∏ i, g i (y' i) := by
  simp [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · rw [hy i hi]
  · simp [he i hi, hg]

private theorem patch_variance_ratio {a V η z : ℝ} {g w : Fin n → ℝ}
    {y : TernaryVector n} (i : Fin n)
    (hp : ∀ k, 0 < ternaryMass a (g k + η * w k * z) V (y k)) :
    patchVarianceTerm a V η g w y z i / patchResponseProduct a V η g w y z =
      ternaryVarianceDerivative a (y i) / ternaryMass a (g i + η * w i * z) V (y i) := by
  unfold patchVarianceTerm patchResponseProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact mul_div_mul_right _ _ (ne_of_gt (Finset.prod_pos (fun k _ => hp k)))

private theorem patch_score_ratio_representation
    (y : TernaryVector n)
    (hp : ∀ k, 0 < ternaryMass a (g k + η * w k * z) V (y k)) :
    patchObservableScore a V η g w y z =
      symmetricDifference (patchResponseProduct a V η g w y) /
        patchResponseProduct a V η g w y z -
      η ^ 2 * ∑ i, (w i) ^ 2 *
        (ternaryVarianceDerivative a (y i) / ternaryMass a (g i + η * w i * z) V (y i)) := by
  unfold patchObservableScore patchScoreNumerator
  rw [sub_div]
  simp_rw [mul_div_assoc, Finset.sum_div, mul_div_assoc, patch_variance_ratio _ hp]

/-- A patch score depends only on response coordinates in the support of its window. -/
theorem patch_score_depends_on_support
    {S : Finset (Fin n)} (hw : ∀ i, i ∉ S → w i = 0)
    {y y' : TernaryVector n} (hyy : ∀ i ∈ S, y i = y' i)
    (hp : ∀ i b, 0 < ternaryMass a (g i + η * w i * z) V b) :
    patchObservableScore a V η g w y z = patchObservableScore a V η g w y' z := by
  let product := patchResponseProduct a V η g w
  have hratio u : product y u /
      product y z =
      product y' u / product y' z := by
    exact product_ratio_depends_on _ _ (fun i hi => by simp [hw i hi]) (fun i b => (hp i b).ne') hyy
  rw [patch_score_ratio_representation a V η z g w y (fun i => hp i (y i)),
    patch_score_ratio_representation a V η z g w y' (fun i => hp i (y' i))]
  congr 1
  · unfold symmetricDifference
    grind
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · rw [hyy i hi]
    · simp_all

end

/-- The actual coordinate score agrees with its one-dimensional patch representation. -/
theorem latent_coordinate_score_eq_patch (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : TernaryVector m)
    (j : Fin m) (y : TernaryVector n) :
    finiteCoordinateScore a V η (latentRegression η base w) w ξ y j =
      patchObservableScore a V η (latentRegressionWithout η base w ξ j)
        (fun i => w i j) y (ternaryValue 1 (ξ j)) := by
  unfold finiteCoordinateScore finiteCoordinateScoreNumerator patchObservableScore patchScoreNumerator
  rw [latent_regression_likelihood_difference]
  simp_rw [((by simp [finiteResponseVarianceTerm, patchVarianceTerm, latent_regression_decomposition η base w ξ j] : ∀ (y : TernaryVector n) (i : Fin n), finiteResponseVarianceTerm a V (latentRegression η base w) ξ y i = patchVarianceTerm a V η (latentRegressionWithout η base w ξ j) (fun k => w k j) y (ternaryValue 1 (ξ j)) i))]
  have hL : finiteResponseLikelihood a V (latentRegression η base w) ξ y =
      patchResponseProduct a V η (latentRegressionWithout η base w ξ j)
        (fun i => w i j) y (ternaryValue 1 (ξ j)) := by
    simp [finiteResponseLikelihood, patchResponseProduct,
      latent_regression_decomposition η base w ξ j]
  rw [hL]

variable {m n : ℕ} {a V η : ℝ} {base : Fin n → ℝ} {w : Fin n → Fin m → ℝ} {ξ : TernaryVector m}

/-- Exact locality of the actual full-field coordinate score. -/
theorem latent_coordinate_score_depends_on_support
    {j : Fin m} {S : Finset (Fin n)} (hw : ∀ i, i ∉ S → w i j = 0)
    (y y' : TernaryVector n) (hyy : ∀ i ∈ S, y i = y' i)
    (hp : ∀ i b, 0 < ternaryMass a (latentRegression η base w ξ i) V b) :
    finiteCoordinateScore a V η (latentRegression η base w) w ξ y j =
      finiteCoordinateScore a V η (latentRegression η base w) w ξ y' j := by
  rw [latent_coordinate_score_eq_patch, latent_coordinate_score_eq_patch]
  apply patch_score_depends_on_support a V η (ternaryValue 1 (ξ j))
    (latentRegressionWithout η base w ξ j) (fun i => w i j) hw hyy
  intro i b
  simpa [latent_regression_decomposition η base w ξ j] using hp i b

/-- Extend a local response tuple by the zero response index outside its support. -/
def extendPatchResponses (S : Finset (Fin n)) (y : S → Fin 3) : TernaryVector n :=
  fun i => if hi : i ∈ S then y ⟨i, hi⟩ else 1

/-- Actual coordinate scores on disjoint supports are orthogonal under the
actual conditional ternary response product measure. -/
theorem latent_coordinate_scores_orthogonal
    {j k : Fin m} {S T : Finset (Fin n)} (hST : Disjoint S T)
    (hwS : ∀ i, i ∉ S → w i j = 0) (hwT : ∀ i, i ∉ T → w i k = 0)
    (ha : a ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (latentRegression η base w ξ i) V b) :
    let score := finiteCoordinateScore a V η (latentRegression η base w) w ξ
    (∫ y,
      score y j *
        score y k
      ∂Measure.pi (fun i => ternaryIndexMeasure (latentRegression η base w ξ i) V ha
        (fun b => (hp i b).le))) = 0 := by
  intro score
  let r  :=
    fun j y => score y j
  let R  := fun y => r j (extendPatchResponses S y)
  let Q  := fun y => r k (extendPatchResponses T y)
  let μ  := fun i =>
    ternaryIndexMeasure (latentRegression η base w ξ i) V ha (fun b => (hp i b).le)
  have hR y : r j y = R (fun i => y i) := by
    apply latent_coordinate_score_depends_on_support hwS
      y (extendPatchResponses S (fun i => y i)) _ hp
    simp_all [extendPatchResponses]
  have hQ y : r k y = Q (fun i => y i) := by
    apply latent_coordinate_score_depends_on_support hwT
      y (extendPatchResponses T (fun i => y i)) _ hp
    simp_all [extendPatchResponses]
  have hL : ∀ y, 0 < finiteResponseLikelihood a V (latentRegression η base w) ξ y := by
    solve_by_elim [Finset.prod_pos]
  have hcenter : (∫ y, R (fun i => y i) ∂Measure.pi μ) = 0 := by
    simp_rw [← hR]
    solve_by_elim [ternary_coordinate_score_measure_centered]
  have horth := finite_product_local_scores_orthogonal hST Q hcenter
  grind

/-- Bounded-overlap aggregation for the actual full-field coordinate scores.
No orthogonality hypothesis is assumed: it follows from their local supports
and the actual conditional ternary response product measure. -/
theorem latent_coordinate_score_variance_bound (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : TernaryVector m)
    (S : Fin m → Finset (Fin n)) (D : ℕ)
    (hw : ∀ j i, i ∉ S j → w i j = 0)
    (hdegree : ∀ j, (Finset.univ.filter fun k => ¬Disjoint (S j) (S k)).card ≤ D)
    (ha : a ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (latentRegression η base w ξ i) V b) :
    let productLaw := Measure.pi (fun i => ternaryIndexMeasure (latentRegression η base w ξ i) V ha (fun b => (hp i b).le))
    (∫ y,
      (∑ j, finiteCoordinateScore a V η (latentRegression η base w) w ξ y j) ^ 2
      ∂productLaw) ≤
      D * ∑ j, ∫ y,
        (finiteCoordinateScore a V η (latentRegression η base w) w ξ y j) ^ 2
        ∂productLaw := by
  apply finite_overlap_variance_bound _ _ (fun j k => ¬Disjoint (S j) (S k)) D
  · tauto
  · intro j
    convert hdegree j using 1
    congr 1
    ext k
    simp
  · intro j k hjk
    exact latent_coordinate_scores_orthogonal
      (not_not.mp hjk) (hw j) (hw k) ha hp

/-- The full observable score inherits that bounded-overlap conditional energy bound. -/
theorem latent_full_score_variance_bound
    {S : Fin m → Finset (Fin n)} {D : ℕ}
    (hw : ∀ j i, i ∉ S j → w i j = 0)
    (hsquares : ∀ i, ∑ j, (w i j) ^ 2 = 1)
    (hdegree : ∀ j, (Finset.univ.filter fun k => ¬Disjoint (S j) (S k)).card ≤ D)
    (ha : a ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (latentRegression η base w ξ i) V b) :
    let productLaw := Measure.pi (fun i => ternaryIndexMeasure (latentRegression η base w ξ i) V ha (fun b => (hp i b).le))
    (∫ y,
      (finiteExperimentScore a V η (latentRegression η base w) ξ y) ^ 2
      ∂productLaw) ≤
      D * ∑ j, ∫ y,
        (finiteCoordinateScore a V η (latentRegression η base w) w ξ y j) ^ 2
        ∂productLaw := by
  simp_rw [finite_experiment_score_decomposition a V η
    (latentRegression η base w) ξ _ hsquares]
  solve_by_elim [latent_coordinate_score_variance_bound]

end

end NearlyMinimax
