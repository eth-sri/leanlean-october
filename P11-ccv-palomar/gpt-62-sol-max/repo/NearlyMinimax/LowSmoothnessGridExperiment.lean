module

public import NearlyMinimax.LowSmoothnessRestriction
public import NearlyMinimax.LowSmoothnessGridChoice
public import NearlyMinimax.LowMixtureDerivative
public import NearlyMinimax.LowSmoothnessWindows


@[expose] public section

/-! The actual grid prior's design-dependent conditional score energies. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace NearlyMinimax

attribute [local instance] Classical.propDecidable

def gridWindowCount (d k : ℕ) : ℕ := (k + 1) ^ d

def gridWindowIndexEquiv (d k : ℕ) : Fin (gridWindowCount d k) ≃ (Fin d → Fin (k + 1)) :=
  (Fintype.equivFinOfCardEq (by simp [gridWindowCount])).symm

def indexedGridWindow (d k : ℕ) (j : Fin (gridWindowCount d k)) : Covariate d → ℝ :=
  gridTensorWindow d k (gridWindowIndexEquiv d k j)

def indexedGridPatch (d k : ℕ) (j : Fin (gridWindowCount d k)) : Set (Covariate d) :=
  gridPatch d k (gridWindowIndexEquiv d k j)

def indexedGridField (d k : ℕ) (η : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (x : Covariate d) : ℝ := η * ∑ j, indexedGridWindow d k j x * ternaryValue 1 (ξ j)

section
variable (d k : ℕ) (η : ℝ)

section
variable (ξ : Fin (gridWindowCount d k) → Fin 3)

theorem indexedGridField_eq :
    indexedGridField d k η ξ =
      gridPriorField d k η (fun j => ξ ((gridWindowIndexEquiv d k).symm j)) := by
  funext x
  unfold indexedGridField gridPriorField
  congr 1
  exact Fintype.sum_equiv (gridWindowIndexEquiv d k) _ _ (fun j => by simp [indexedGridWindow])

theorem indexedGridField_continuous :
    Continuous (indexedGridField d k η ξ) := by
  rw [indexedGridField_eq]
  exact gridPriorField_continuous _ _ _ _

end

theorem indexedGridField_abs_bound (hη : 0 ≤ η)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (x : Covariate d) :
    |indexedGridField d k η ξ x| ≤ (2 : ℝ) ^ d * η := by
  rw [indexedGridField_eq]
  apply gridPriorField_abs_bound <;> assumption

end

def gridSampleWeights (d k n : ℕ) (x : Fin n → Covariate d) :
    Fin n → Fin (gridWindowCount d k) → ℝ := fun i j => indexedGridWindow d k j (x i)

section
variable (d k n : ℕ)

theorem grid_latent_regression_eq (η : ℝ) (x : Fin n → Covariate d)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (i : Fin n) :
    latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ i =
      indexedGridField d k η ξ (x i) := by
  simp [latentRegression, indexedGridField, gridSampleWeights]

theorem grid_sample_squared_partition (x : Fin n → Covariate d) (i : Fin n) :
    (∑ j, gridSampleWeights d k n x i j ^ 2) = 1 := by
  have h := Fintype.sum_equiv (gridWindowIndexEquiv d k)
    (fun j => indexedGridWindow d k j (x i) ^ 2) (fun j => gridTensorWindow d k j (x i) ^ 2)
    (fun _ => rfl)
  exact h.trans (gridTensorWindow_square_partition d k (x i))

theorem grid_modified_regression_abs_bound (η u : ℝ) (hη : 0 ≤ η)
    (x : Fin n → Covariate d) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (j : Fin (gridWindowCount d k)) (i : Fin n) (hu : u ∈ Icc (-1 : ℝ) 1) :
    |latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ j i +
      η * gridSampleWeights d k n x i j * u| ≤ ((2 : ℝ) ^ d + 2) * η := by
  let z := ternaryValue 1 (ξ j)
  have hz := ternaryValue_one_abs_le (ξ j)
  have hw : |gridSampleWeights d k n x i j| ≤ 1 := by
    change |gridTensorWindow d k (gridWindowIndexEquiv d k j) (x i)| ≤ 1
    rw [abs_of_nonneg (gridTensorWindow_nonneg d k (gridWindowIndexEquiv d k j) (x i))]
    exact gridTensorWindow_le_one _ _ _ _
  have hdiff : |u - z| ≤ 2 := by
    grind
  have heq : latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0)
      (gridSampleWeights d k n x) ξ j i + η * gridSampleWeights d k n x i j * u =
        indexedGridField d k η ξ (x i) + η * gridSampleWeights d k n x i j * (u - z) := by
    rw [← grid_latent_regression_eq, latent_regression_decomposition] <;> ring
  rw [heq]
  have hterm : |η * gridSampleWeights d k n x i j * (u - z)| ≤ 2 * η := by
    rw [abs_mul, abs_mul, abs_of_nonneg hη]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hw hη) hdiff (abs_nonneg _) (by positivity : 0 ≤ η * 1)
    grind
  exact (abs_add_le _ _).trans (by nlinarith [indexedGridField_abs_bound d k η hη ξ (x i)])

end

def gridCoordinateEnergy (d k n : ℕ) (a V η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (j : Fin (gridWindowCount d k))
    (x : Fin n → Covariate d) : ℝ :=
  patchExpectedScoreEnergy n a V η
    (latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0)
      (gridSampleWeights d k n x) ξ j)
    (fun i => gridSampleWeights d k n x i j) (ternaryValue 1 (ξ j))

section
variable (d k n : ℕ)

theorem grid_sample_weight_measurable (j : Fin (gridWindowCount d k)) (i : Fin n) :
    Measurable (fun x : Fin n → Covariate d => gridSampleWeights d k n x i j) :=
  ((gridTensorWindow_continuous d k (gridWindowIndexEquiv d k j)).comp
    (continuous_apply i)).measurable

theorem grid_excluded_field_measurable (η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (j : Fin (gridWindowCount d k)) (i : Fin n) :
    Measurable (fun x : Fin n → Covariate d =>
      latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ j i) := by
  exact measurable_const.add ((Finset.measurable_sum _
      (fun l _ => (grid_sample_weight_measurable d k n l i).mul_const _)).const_mul _)

end

private theorem grid_modified_field_le {d k n : ℕ} {η ρ : ℝ} (hamp : GridAmplitudeBounds d η ρ)
    (x : Fin n → Covariate d) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (j : Fin (gridWindowCount d k)) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) :
    |latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ j i +
      η * gridSampleWeights d k n x i j * u| ≤ ρ :=
  (grid_modified_regression_abs_bound d k n η u hamp.nonneg x ξ j i hu).trans hamp.field_le

/-- The field remains inside the interior neighborhood of the ternary model. -/
theorem indexedGridField_le_margin {d k : ℕ} {η ρ : ℝ} (hamp : GridAmplitudeBounds d η ρ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (x : Covariate d) :
    |indexedGridField d k η ξ x| ≤ ρ :=
  (indexedGridField_abs_bound d k η hamp.nonneg ξ x).trans hamp.base_le

/-- Actual coordinate score energy integrated over the complete uniform-design
sample. The observations outside the patch have already been cancelled. -/
private theorem grid_coordinate_design_energy {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (j : Fin (gridWindowCount d k))
    (hamp : GridAmplitudeBounds d η P.ρ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (gridCoordinateEnergy d k n P.a (P.variancePath η t) η ξ j)
        (Measure.pi (fun _ : Fin n => cubeVolume d)) ∧
      (0 < k → n * (2 / (k : ℝ)) ^ d ≤ 1 →
        (∫ x : Fin n → Covariate d, gridCoordinateEnergy d k n P.a (P.variancePath η t) η ξ j x
          ∂Measure.pi (fun _ : Fin n => cubeVolume d)) ≤
        ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
          Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * η ^ 4 *
            (n * (2 / (k : ℝ)) ^ d) ^ 2) := by
  let _ := cubeVolume_isProbability d
  let g := fun x =>
    latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ j
  let w := fun x i => gridSampleWeights d k n x i j
  let A := indexedGridPatch d k j
  let z := ternaryValue 1 (ξ j)
  have hz := abs_le.mp (ternaryValue_one_abs_le (ξ j))
  have hlegal (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) :=
    P.path_legality η t (g x i + η * w x i * u) ht hamp.sq_le (grid_modified_field_le hamp x ξ j hu i)
  have hp (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) (y : Fin 3) :=
    P.c_pos.trans_le ((hlegal x u hu i).2.2.1 y)
  obtain ⟨hi, hbound⟩ := iid_design_full_patch_score_energy (cubeVolume d) n A
    (gridPatch_measurable d k _) P.a (P.variancePath η t) η z P.ρ P.c g w
    (grid_excluded_field_measurable d k n η ξ j) (grid_sample_weight_measurable d k n j)
    P.a_pos P.ρ_pos.le P.c_pos hz
    (fun x i hi => gridTensorWindow_zero_outside_patch d k (gridWindowIndexEquiv d k j) (x i) hi)
    (fun x i _ => by
      change |gridTensorWindow d k (gridWindowIndexEquiv d k j) (x i)| ≤ 1
      rw [abs_of_nonneg (gridTensorWindow_nonneg d k _ _)]; exact gridTensorWindow_le_one d k _ _)
    (fun x u hu i _ => grid_modified_field_le hamp x ξ j hu i)
    (fun x u hu i _ y => ⟨(hp x u hu i y).le,
      ternary_mass_le_one P.a _ _ P.a_pos.ne' (fun b => (hp x u hu i b).le) y⟩)
    (fun x i _ y => (hlegal x z hz i).2.2.1 y) (fun x i y => hp x z hz i y)
  refine ⟨hi, fun hk hmean => ?_⟩
  have hvol : (cubeVolume d).real A ≤ (2 / (k : ℝ)) ^ d := gridPatch_cube_probability_bound d k _ hk
  apply (hbound ((mul_le_mul_of_nonneg_left hvol (Nat.cast_nonneg n)).trans hmean)).trans
  gcongr

def gridFullScoreEnergy (d k n : ℕ) (a V η : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (x : Fin n → Covariate d) : ℝ :=
  ∑ y, finiteResponseLikelihood (gridWindowCount d k) n a V
    (latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x)) ξ y *
    (finiteExperimentScore (gridWindowCount d k) n a V η
      (latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x)) ξ y) ^ 2

section
variable (d k n : ℕ)

theorem indexed_grid_observed_patch_degree (x : Fin n → Covariate d)
    (j : Fin (gridWindowCount d k)) :
    (Finset.univ.filter fun l : Fin (gridWindowCount d k) =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k j)
        (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k l)).card ≤ 5 ^ d := by
  have heq := Finset.card_equiv (gridWindowIndexEquiv d k) (s := Finset.univ.filter fun l =>
    ¬Disjoint (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k j)
      (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k l))
    (t := Finset.univ.filter fun l =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k (gridWindowIndexEquiv d k j))
        (Finset.univ.filter fun i => x i ∈ gridPatch d k l))
    (fun _ => by
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      rfl)
  rw [heq]
  apply grid_observed_patch_degree

theorem grid_full_score_conditional_energy_bound (a V η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (x : Fin n → Covariate d)
    (ha : a ≠ 0) (hp : ∀ i y, 0 < ternaryMass a (indexedGridField d k η ξ (x i)) V y) :
    gridFullScoreEnergy d k n a V η ξ x ≤ (5 : ℝ) ^ d *
      ∑ j, gridCoordinateEnergy d k n a V η ξ j x := by
  let f := latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x)
  let S :=
    fun j => Finset.univ.filter (fun i => x i ∈ indexedGridPatch d k j)
  have hpos : ∀ i y, 0 < ternaryMass a (f ξ i) V y := by
    intro i y
    simpa [f, grid_latent_regression_eq] using hp i y
  have h := latent_full_score_variance_bound (gridWindowCount d k) n a V η (fun _ => 0)
    (gridSampleWeights d k n x) ξ S (5 ^ d)
    (fun j i hi => gridTensorWindow_zero_outside_patch d k _ (x i) (by
      intro hmem
      apply hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmem⟩))
    (grid_sample_squared_partition d k n x)
    (indexed_grid_observed_patch_degree d k n x) ha hpos
  simp_rw [ternary_index_product_integral] at h
  change gridFullScoreEnergy d k n a V η ξ x ≤ (5 ^ d : ℕ) *
    ∑ j, ∑ y, finiteResponseLikelihood (gridWindowCount d k) n a V f ξ y *
      (finiteCoordinateScore (gridWindowCount d k) n a V η f (gridSampleWeights d k n x) ξ y j) ^ 2 at h
  have hcoord (j : Fin (gridWindowCount d k)) :
      (∑ y, finiteResponseLikelihood (gridWindowCount d k) n a V f ξ y *
        (finiteCoordinateScore (gridWindowCount d k) n a V η f (gridSampleWeights d k n x) ξ y j) ^ 2) =
        gridCoordinateEnergy d k n a V η ξ j x := by
    unfold gridCoordinateEnergy patchExpectedScoreEnergy
    apply Finset.sum_congr rfl
    intro y _
    rw [latent_coordinate_score_eq_patch]
    congr 1
    simp only [finiteResponseLikelihood, patchResponseProduct, f]
    simp_rw [latent_regression_decomposition (gridWindowCount d k) n η (fun _ => 0)
      (gridSampleWeights d k n x) ξ j]
  simp_rw [hcoord] at h
  grind

end

theorem grid_full_score_energy_measurable {α : Type*} [MeasurableSpace α]
    (d k n : ℕ) (a η : ℝ) (V : α → ℝ) (x : α → Fin n → Covariate d)
    (hV : Measurable V) (hx : Measurable x) (ξ : Fin (gridWindowCount d k) → Fin 3) :
    Measurable (fun z => gridFullScoreEnergy d k n a (V z) η ξ (x z)) := by
  have hf (ξ' : Fin (gridWindowCount d k) → Fin 3) (i : Fin n) :
      Measurable (fun z => latentRegression (gridWindowCount d k) n η (fun _ => 0)
        (gridSampleWeights d k n (x z)) ξ' i) := by
    simp_rw [grid_latent_regression_eq]
    exact (indexedGridField_continuous d k η ξ').measurable.comp ((measurable_pi_apply i).comp hx)
  exact Finset.measurable_sum _ (fun y _ =>
    (finiteResponseLikelihood_measurable_comp _ _ a V hV _ hf ξ y).mul
      ((finiteExperimentScore_measurable_comp _ _ a η V hV _ hf ξ y).pow_const 2))

section
variable {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3)

theorem grid_response_positive (x : Fin n → Covariate d)
    (hamp : GridAmplitudeBounds d η P.ρ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ i y, 0 < ternaryMass P.a (indexedGridField d k η ξ (x i)) (P.variancePath η t) y :=
  fun i y => P.c_pos.trans_le
    ((P.path_legality η t _ ht hamp.sq_le (indexedGridField_le_margin hamp ξ (x i))).2.2.1 y)

section
variable (hamp : GridAmplitudeBounds d η P.ρ) (ht : t ∈ Icc (0 : ℝ) 1)
include hamp ht

private theorem grid_full_score_design_energy :
    Integrable (gridFullScoreEnergy d k n P.a (P.variancePath η t) η ξ)
        (Measure.pi (fun _ : Fin n => cubeVolume d)) ∧
      (0 < k → n * (2 / (k : ℝ)) ^ d ≤ 1 →
        (∫ x : Fin n → Covariate d, gridFullScoreEnergy d k n P.a (P.variancePath η t) η ξ x
          ∂Measure.pi (fun _ : Fin n => cubeVolume d)) ≤
        (5 : ℝ) ^ d * gridWindowCount d k *
          (ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
            Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * η ^ 4 * (n * (2 / (k : ℝ)) ^ d) ^ 2)) := by
  let μ := Measure.pi (fun _ : Fin n => cubeVolume d)
  have hcoords j := grid_coordinate_design_energy C P k n η t ξ j hamp ht
  have hJ := (integrable_finsetSum Finset.univ (fun j _ => (hcoords j).1)).const_mul ((5 : ℝ) ^ d)
  have hp x := grid_response_positive C P k n η t ξ x hamp ht
  have hpoint x := grid_full_score_conditional_energy_bound d k n P.a (P.variancePath η t) η ξ x P.a_pos.ne' (hp x)
  have hI : Integrable (gridFullScoreEnergy d k n P.a (P.variancePath η t) η ξ) μ := by
    apply hJ.mono' (grid_full_score_energy_measurable d k n P.a η _ _ measurable_const measurable_id ξ).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpoint x
    · exact Finset.sum_nonneg (fun y _ => mul_nonneg
        (Finset.prod_nonneg (fun i _ => by simpa [grid_latent_regression_eq] using (hp x i (y i)).le))
        (sq_nonneg _))
  refine ⟨hI, fun hk hmean => ?_⟩
  calc
    _ ≤ ∫ x, (5 : ℝ) ^ d * ∑ j, gridCoordinateEnergy d k n P.a (P.variancePath η t) η ξ j x ∂μ :=
      integral_mono hI hJ hpoint
    _ = (5 : ℝ) ^ d * ∑ j, ∫ x, gridCoordinateEnergy d k n P.a (P.variancePath η t) η ξ j x ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => (hcoords j).1)]
    _ ≤ _ := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hcoords j).2 hk hmean)

theorem grid_full_score_energy_integrable :
    Integrable (gridFullScoreEnergy d k n P.a (P.variancePath η t) η ξ)
      (Measure.pi (fun _ : Fin n => cubeVolume d)) :=
  (grid_full_score_design_energy C P k n η t ξ hamp ht).1

end

end

/-- The actual latent-prior, design, and response score energy. -/
def gridPriorScoreEnergy (d k n : ℕ) (a v η t : ℝ) : ℝ :=
  ∑ ξ, activationProductPrior (gridWindowCount d k) t ξ *
    ∫ x : Fin n → Covariate d, gridFullScoreEnergy d k n a (v - η ^ 2 * t) η ξ x
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)

def lowSmoothnessScoreConstant {d : ℕ} {C : ModelConstants d}
    (P : LowSmoothnessTernaryConstants C) : ℝ :=
  (40 : ℝ) ^ d * ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
    Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c)

theorem lowSmoothnessScoreConstant_nonneg {d : ℕ} {C : ModelConstants d}
    (P : LowSmoothnessTernaryConstants C) : 0 ≤ lowSmoothnessScoreConstant P := by
  unfold lowSmoothnessScoreConstant
  positivity

def gridUniformScoreBudget {d : ℕ} {C : ModelConstants d}
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η : ℝ) : ℝ :=
  lowSmoothnessScoreConstant P * ((n : ℝ) ^ 2 * η ^ 4 / (k : ℝ) ^ d)

/-- Uniform full score budget for the actual prior and the actual IID design.
Every energy bound is derived from the ternary likelihood, count law, and
window support geometry. -/
theorem grid_prior_score_energy_bound {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ) (hk : 1 ≤ k)
    (hamp : GridAmplitudeBounds d η P.ρ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) :
    gridPriorScoreEnergy d k n P.a P.v η t ≤ gridUniformScoreBudget P k n η := by
  let K := ternaryScoreExponentialConstant P.a P.ρ P.c
  let B := (5 : ℝ) ^ d * gridWindowCount d k *
    (K ^ 2 * Real.exp K * η ^ 4 * (n * (2 / (k : ℝ)) ^ d) ^ 2)
  have hkp : 0 < k := by omega
  have hbudget : gridPriorScoreEnergy d k n P.a P.v η t ≤ B := by
    unfold gridPriorScoreEnergy
    calc
      _ ≤ ∑ ξ, activationProductPrior (gridWindowCount d k) t ξ * B := by
        apply Finset.sum_le_sum
        intro ξ _
        exact mul_le_mul_of_nonneg_left
          ((grid_full_score_design_energy C P k n η t ξ hamp ht).2 hkp hmean)
          (Finset.prod_nonneg (fun i _ => activation_prior_nonnegative t ht.1 ht.2 (ξ i)))
      _ = B := by rw [← Finset.sum_mul, activation_product_prior_normalized, one_mul]
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hkp
  have hm : (gridWindowCount d k : ℝ) ≤ (2 * (k : ℝ)) ^ d := by
    have hk1 : (k : ℝ) + 1 ≤ 2 * k := by exact_mod_cast (by omega : k + 1 ≤ 2 * k)
    simpa only [gridWindowCount, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ k + 1) hk1 d
  calc
    _ ≤ B := hbudget
    _ ≤ (5 : ℝ) ^ d * (2 * (k : ℝ)) ^ d *
        (K ^ 2 * Real.exp K * η ^ 4 * (n * (2 / (k : ℝ)) ^ d) ^ 2) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) (by positivity)
    _ = _ := by
      unfold gridUniformScoreBudget lowSmoothnessScoreConstant
      rw [show (40 : ℝ) = 5 * 2 ^ 3 by norm_num]
      have htwo : ((2 : ℝ) ^ 3) ^ d = ((2 : ℝ) ^ d) ^ 3 := by
        simp [← pow_mul, Nat.mul_comm 3 d]
      simp only [mul_pow, div_pow, htwo]
      dsimp [K]
      field_simp [ne_of_gt hkr]

/-- The actual model parameter in each latent state of the indexed grid prior. -/
def gridPathParameter {d : ℕ} (C : ModelConstants d) (P : LowSmoothnessTernaryConstants C)
    (k : ℕ) (η t : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (hamp : GridAmplitudeBounds d η P.ρ) (ht : t ∈ Icc (0 : ℝ) 1) :
    RegressionParameter d :=
  P.pathParameter (indexedGridField d k η ξ) (indexedGridField_continuous d k η ξ) η t ht hamp.sq_le
    (indexedGridField_le_margin hamp ξ)

theorem gridPathParameter_admissible {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η b t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1)
    (hb : 0 ≤ b) (hamp : GridAmplitudeBounds d η P.ρ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : gridHolderBudget d * b ≤ C.holderBound) :
    Admissible C (gridPathParameter C P k η t ξ hamp ht) := by
  have horder : C.order = 0 := by
    have ho := C.order_lt.trans_le hs1
    aesop
  have hηb : η ≤ b := by
    rw [hscale]
    exact div_le_self hb (Real.one_le_rpow (by exact_mod_cast hk) C.smoothness_pos.le)
  apply P.pathParameter_admissible_order_zero _ _ η t ht hamp.sq_le _ horder
    ((2 : ℝ) ^ d * b) (gridPriorSlope d * b)
    (by positivity) (mul_nonneg (gridPriorSlope_nonneg d) hb) (by simpa [gridHolderBudget, add_mul] using hholder)
  · intro x
    exact (indexedGridField_abs_bound d k η hamp.nonneg ξ x).trans (mul_le_mul_of_nonneg_left hηb (by positivity))
  · intro x y
    rw [hscale, indexedGridField_eq]
    exact gridPriorField_holder_bound d k C.smoothness b hk C.smoothness_pos.le hs1 hb _ x y

end NearlyMinimax
