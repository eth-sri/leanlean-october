module

public import NearlyMinimax.LowMixtureDerivative
public import NearlyMinimax.LowSmoothnessRestriction
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

section
variable {d k n : ℕ} (η : ℝ) (ξ : TernaryVector (gridWindowCount d k))

def indexedGridWindow (j : Fin (gridWindowCount d k)) : Covariate d → ℝ :=
  gridTensorWindow (gridWindowIndexEquiv d k j)

def indexedGridPatch (j : Fin (gridWindowCount d k)) : Set (Covariate d) :=
  gridPatch (gridWindowIndexEquiv d k j)

def indexedGridField
    (x : Covariate d) : ℝ := η * ∑ j, indexedGridWindow j x * ternaryValue 1 (ξ j)

theorem indexedGridField_eq (d k : ℕ) (η : ℝ) (ξ : TernaryVector (gridWindowCount d k)) :
    indexedGridField η ξ =
      gridPriorField η (fun j => ξ ((gridWindowIndexEquiv d k).symm j)) := by
  funext x
  unfold indexedGridField gridPriorField
  congr 1
  exact Fintype.sum_equiv (gridWindowIndexEquiv d k) _ _ (fun j => by simp [indexedGridWindow])

theorem indexedGridField_continuous :
    Continuous (indexedGridField η ξ) := by
  rw [indexedGridField_eq]
  exact (continuous_finsetSum _ (fun j _ => (gridTensorWindow_continuous j).mul_const _)).const_mul _

theorem indexedGridField_abs_bound {η : ℝ} (hη : 0 ≤ η)
    (ξ : TernaryVector (gridWindowCount d k)) (x : Covariate d) :
    |indexedGridField η ξ x| ≤ 2 ^ d * η := by
  rw [indexedGridField_eq]
  exact gridPriorField_abs_bound _ _ hη _ x

def gridSampleWeights (k : ℕ) {n : ℕ} (x : DesignSample d n) :
    Fin n → Fin (gridWindowCount d k) → ℝ := fun i j => indexedGridWindow j (x i)

theorem grid_latent_regression_eq (x : DesignSample d n)
    (ξ : TernaryVector (gridWindowCount d k)) (i : Fin n) :
    latentRegression η (fun _ => 0) (gridSampleWeights k x) ξ i =
      indexedGridField η ξ (x i) := by
  simp [latentRegression, indexedGridField, gridSampleWeights]

end

theorem grid_sample_squared_partition (d k n : ℕ) (x : DesignSample d n) (i : Fin n) :
    (∑ j, gridSampleWeights k x i j ^ 2) = 1 := by
  have h := Fintype.sum_equiv (gridWindowIndexEquiv d k) _ (fun j => gridTensorWindow j (x i) ^ 2) (fun _ => rfl)
  exact h.trans (gridTensorWindow_square_partition ..)

section
variable {d : ℕ} {C : ModelConstants d} {P : LowSmoothnessTernaryConstants C} {k n : ℕ}

theorem grid_modified_regression_abs_bound {η u : ℝ} (hη : 0 ≤ η)
    (x : DesignSample d n) (ξ : TernaryVector (gridWindowCount d k))
    (j : Fin (gridWindowCount d k)) (i : Fin n) (hu : u ∈ Icc (-1) 1) :
    let weights := gridSampleWeights k x i j
    |latentRegressionWithout η (fun _ => 0) (gridSampleWeights k x) ξ j i +
      η * weights * u| ≤ (2 ^ d + 2) * η := by
  intro weights
  let z := ternaryValue 1 (ξ j)
  have hz  := ternaryValue_one_abs_le (ξ j)
  have hw : |weights| ≤ 1 := by
    change |gridTensorWindow (gridWindowIndexEquiv d k j) (x i)| ≤ 1
    grind [gridTensorWindow_nonneg d k (gridWindowIndexEquiv d k j) (x i), gridTensorWindow_le_one ..]
  have hdiff : |u - z| ≤ 2 := by
    grind
  have heq : latentRegressionWithout η (fun _ => 0)
      (gridSampleWeights k x) ξ j i + η * weights * u =
        indexedGridField η ξ (x i) + η * weights * (u - z) := by
    rw [← grid_latent_regression_eq, latent_regression_decomposition]
    ring
  rw [heq]
  have hterm : |η * weights * (u - z)| ≤ 2 * η := by
    rw [abs_mul, abs_mul, abs_of_nonneg hη]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hw hη) hdiff (abs_nonneg _) (by positivity)
    linarith
  exact (abs_add_le _ _).trans (by nlinarith [indexedGridField_abs_bound hη ξ (x i)])

def gridCoordinateEnergy (a V η : ℝ)
    (ξ : TernaryVector (gridWindowCount d k)) (j : Fin (gridWindowCount d k))
    (x : DesignSample d n) : ℝ :=
  patchExpectedScoreEnergy a V η
    (latentRegressionWithout η (fun _ => 0)
      (gridSampleWeights k x) ξ j)
    (fun i => gridSampleWeights k x i j) (ternaryValue 1 (ξ j))

theorem grid_sample_weight_measurable (n : ℕ) (j : Fin (gridWindowCount d k)) (i : Fin n) :
    Measurable (fun x => gridSampleWeights k x i j) :=
  ((gridTensorWindow_continuous (gridWindowIndexEquiv d k j)).comp
    (continuous_apply i)).measurable

theorem grid_excluded_field_measurable (d k n : ℕ) (η : ℝ)
    (ξ : TernaryVector (gridWindowCount d k)) (j : Fin (gridWindowCount d k)) (i : Fin n) :
    Measurable (fun x =>
      latentRegressionWithout η (fun _ => 0) (gridSampleWeights k x) ξ j i) := measurable_const.add ((Finset.measurable_sum _
    (fun l _ => (grid_sample_weight_measurable n l i).mul_const _)).const_mul _)

/-- Actual coordinate score energy integrated over the complete uniform-design
sample. The observations outside the patch have already been cancelled. -/
theorem grid_coordinate_energy_control (k n : ℕ) {η t : ℝ}
    (ξ : TernaryVector (gridWindowCount d k)) (j : Fin (gridWindowCount d k))
    (hη : 0 ≤ η) (ht : t ∈ Icc 0 1)
    (hfield : (2 ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    Integrable (gridCoordinateEnergy P.a (P.variancePath η t) η ξ j)
      (Measure.pi (fun _ : Fin n => cubeVolume d)) ∧
      (0 < k → n * (2 / (k : ℝ)) ^ d ≤ 1 →
    (∫ x, gridCoordinateEnergy P.a (P.variancePath η t) η ξ j x
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)) ≤
      ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
        Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * η ^ 4 *
          (n * (2 / k) ^ d) ^ 2) := by
  let _ := cubeVolume_isProbability d
  let A := indexedGridPatch j
  let z := ternaryValue 1 (ξ j)
  have hz  := abs_le.mp (ternaryValue_one_abs_le (ξ j))
  have hreg x u (hu : u ∈ Icc (-1) 1) (i : Fin n)  :=
    (grid_modified_regression_abs_bound hη x ξ j i hu).trans hfield
  have hlegal x u hu i :=
    P.path_legality η t _ ht hvariance (hreg x u hu i)
  have hp x u hu i y  :=
    P.c_pos.trans_le ((hlegal x u hu i).2.2.1 y)
  have hw x i : |(fun x i => gridSampleWeights k (n := n) x i j) x i| ≤ 1 := by
    change |gridTensorWindow (gridWindowIndexEquiv d k j) (x i)| ≤ 1
    grind [gridTensorWindow_nonneg, gridTensorWindow_le_one]
  have hq x u hu i y := And.intro (hp x u hu i y).le
    (ternary_mass_le_one _ _ P.a_pos.ne' (fun b => (hp x u hu i b).le) y)
  have hl x i y := (hlegal x z hz i).2.2.1 y
  constructor
  · exact patch_expected_score_energy_integrable _ P.a (P.variancePath η t) η z P.ρ P.c
      (grid_excluded_field_measurable d k n η ξ j) (grid_sample_weight_measurable n j)
      P.a_pos P.ρ_pos.le P.c_pos hz
      hw hreg hq hl
  · intro hk hmean
    have hvol : (cubeVolume d).real A ≤ (2 / k) ^ d := gridPatch_cube_probability_bound d k _ hk
    have hbound := iid_design_full_patch_score_energy_bound (A := A)
      (gridPatch_measurable ..) P.a (P.variancePath η t) η z P.ρ P.c
      (grid_excluded_field_measurable d k n η ξ j) (grid_sample_weight_measurable n j)
      P.a_pos P.ρ_pos.le P.c_pos hz ((mul_le_mul_of_nonneg_left hvol (Nat.cast_nonneg n)).trans hmean)
      (fun x i hi => gridTensorWindow_zero_outside_patch d k _ hi)
      (fun x i _ => hw x i) (fun x u hu i _ => hreg x u hu i)
      (fun x u hu i _ => hq x u hu i) (fun x i _ => hl x i) (fun x i y => hp x z hz i y)
    apply hbound.trans
    gcongr

def gridFullScoreEnergy (a V η : ℝ) (ξ : TernaryVector (gridWindowCount d k))
    (x : DesignSample d n) : ℝ :=
  ∑ y, finiteResponseLikelihood a V
    (latentRegression η (fun _ => 0) (gridSampleWeights k x)) ξ y *
    (finiteExperimentScore a V η
      (latentRegression η (fun _ => 0) (gridSampleWeights k x)) ξ y) ^ 2

theorem indexed_grid_observed_patch_degree (d k n : ℕ) (x : DesignSample d n)
    (j : Fin (gridWindowCount d k)) :
    (Finset.univ.filter fun l : Fin (gridWindowCount d k) =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ indexedGridPatch j)
        (Finset.univ.filter fun i => x i ∈ indexedGridPatch l)).card ≤ 5 ^ d := by
  have heq := Finset.card_equiv (gridWindowIndexEquiv d k) (s := Finset.univ.filter fun l =>
    ¬Disjoint (Finset.univ.filter fun i => x i ∈ indexedGridPatch j)
      (Finset.univ.filter fun i => x i ∈ indexedGridPatch l))
    (t := Finset.univ.filter fun l =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch (gridWindowIndexEquiv d k j))
        (Finset.univ.filter fun i => x i ∈ gridPatch l))
    (fun _ => by
      aesop)
  rw [heq]
  exact grid_observed_patch_degree ..

theorem grid_full_score_conditional_energy_bound {a V η : ℝ}
    {ξ : TernaryVector (gridWindowCount d k)} {x : DesignSample d n}
    (ha : a ≠ 0) (hp : ∀ i y, 0 < ternaryMass a (indexedGridField η ξ (x i)) V y) :
    gridFullScoreEnergy a V η ξ x ≤ 5 ^ d *
      ∑ j, gridCoordinateEnergy a V η ξ j x := by
  let f := latentRegression η (fun _ => 0) (gridSampleWeights k x)
  have hpos : ∀ i y, 0 < ternaryMass a (f ξ i) V y := by
    intro i y
    simpa [f, grid_latent_regression_eq] using hp i y
  have h := latent_full_score_variance_bound
    (fun j i hi => gridTensorWindow_zero_outside_patch d k (x i) (by
      aesop))
    (grid_sample_squared_partition d k n x)
    (indexed_grid_observed_patch_degree d k n x) ha hpos
  simp_rw [ternary_index_product_integral] at h
  change gridFullScoreEnergy .. ≤ _ *
    ∑ j, ∑ y, finiteResponseLikelihood a V f ξ y *
      (finiteCoordinateScore a V η f (gridSampleWeights k x) ξ y j) ^ 2 at h
  have hcoord j :
      (∑ y, finiteResponseLikelihood a V f ξ y *
        (finiteCoordinateScore a V η f (gridSampleWeights k x) ξ y j) ^ 2) =
        gridCoordinateEnergy a V η ξ j x := by
    apply Finset.sum_congr rfl
    intro y _
    rw [latent_coordinate_score_eq_patch]
    congr 1
    simp only [finiteResponseLikelihood, patchResponseProduct, f]
    simp_rw [latent_regression_decomposition η (fun _ => 0)
      (gridSampleWeights k x) ξ j]
  grind

/-- Measurability for both fixed variances and measurable paths through the experiment. -/
theorem grid_score_energy_measurable_comp {Ω : Type*} [MeasurableSpace Ω] {d k n : ℕ} (a η : ℝ)
    (ξ : TernaryVector (gridWindowCount d k)) {V : Ω → ℝ} {X : Ω → DesignSample d n}
    (hV : Measurable V) (hX : Measurable X) :
    Measurable (fun s => gridFullScoreEnergy a (V s) η ξ (X s)) := by
  let f s := latentRegression η (fun _ => 0) (gridSampleWeights k (X s))
  have hf ξ' i : Measurable (fun s => f s ξ' i) := by
    simpa only [f, grid_latent_regression_eq, Function.comp_def] using
      (indexedGridField_continuous η ξ').measurable.comp ((measurable_pi_apply i).comp hX)
  exact Finset.measurable_sum _ fun y _ => (finiteResponseLikelihood_measurable_comp _ _ a hV f hf ξ y).mul
    ((finiteExperimentScore_measurable_comp _ _ a hV f hf η ξ y).pow_const 2)

theorem grid_response_positive {η t : ℝ}
    (ξ : TernaryVector (gridWindowCount d k)) (x : DesignSample d n)
    (hη : 0 ≤ η) (ht : t ∈ Icc 0 1)
    (hfield : (2 ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    ∀ i y, 0 < ternaryMass P.a (indexedGridField η ξ (x i)) (P.variancePath η t) y := fun i y => P.c_pos.trans_le ((P.path_legality η t _ ht hvariance ((indexedGridField_abs_bound hη ξ (x i)).trans (by nlinarith))).2.2.1 y)

theorem grid_full_score_energy_control (k n : ℕ) {η t : ℝ}
    (ξ : TernaryVector (gridWindowCount d k))
    (hη : 0 ≤ η) (ht : t ∈ Icc 0 1)
    (hfield : (2 ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    let energy := gridFullScoreEnergy P.a (P.variancePath η t) η ξ
    Integrable (energy)
      (Measure.pi (fun _ : Fin n => cubeVolume d)) ∧
      (0 < k → n * (2 / (k : ℝ)) ^ d ≤ 1 →
    (∫ x, energy x
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)) ≤
      5 ^ d * gridWindowCount d k *
        (ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
          Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * η ^ 4 * (n * (2 / k) ^ d) ^ 2)) := by
  intro energy
  let μ := Measure.pi (fun _ : Fin n => cubeVolume d)
  have hcoords j :=
    grid_coordinate_energy_control k n ξ j hη ht hfield hvariance
  have hi := (integrable_finsetSum Finset.univ (fun j _ => (hcoords j).1)).const_mul (5 ^ d)
  have hp (x : DesignSample d n) := grid_response_positive ξ x hη ht hfield hvariance
  have hbound x := grid_full_score_conditional_energy_bound P.a_pos.ne' (hp x)
  have hfull : Integrable (energy) μ := by
    apply hi.mono' (grid_score_energy_measurable_comp P.a η ξ measurable_const measurable_id).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hbound x
    · exact Finset.sum_nonneg (fun y _ => mul_nonneg
        (Finset.prod_nonneg (fun i _ => by simpa [grid_latent_regression_eq] using (hp x i (y i)).le))
        (sq_nonneg _))
  refine ⟨hfull, fun hk hmean => ?_⟩
  calc
    _ ≤ _ :=
      integral_mono hfull hi hbound
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => (hcoords j).1)]
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ _ := Finset.sum_le_sum (fun j _ =>
          (hcoords j).2 hk hmean)
        _ = _ := by simp

/-- The actual latent-prior, design, and response score energy. -/
def gridPriorScoreEnergy (d k n : ℕ) (a v η t : ℝ) : ℝ :=
  ∑ ξ, activationProductPrior t ξ *
    ∫ x, gridFullScoreEnergy (k := k) a (v - η ^ 2 * t) η ξ x
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)

/-- Uniform full score budget for the actual prior and the actual IID design.
Every energy bound is derived from the ternary likelihood, count law, and
window support geometry. -/
theorem grid_prior_score_energy_bound {η t : ℝ} (hk : 1 ≤ k)
    (hη : 0 ≤ η) (ht : t ∈ Icc 0 1)
    (hfield : (2 ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) :
    gridPriorScoreEnergy d k n P.a P.v η t ≤
      40 ^ d * ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
        Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * n ^ 2 * η ^ 4 / k ^ d := by
  let K := ternaryScoreExponentialConstant P.a P.ρ P.c
  let B := 5 ^ d * gridWindowCount d k *
    (K ^ 2 * Real.exp K * η ^ 4 * (n * (2 / k) ^ d) ^ 2)
  have hkp : 0 < k := by omega
  have hbudget : gridPriorScoreEnergy d k n P.a P.v η t ≤ B := by
    calc
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro ξ _
        exact mul_le_mul_of_nonneg_left
          ((grid_full_score_energy_control k n ξ hη ht hfield hvariance).2 hkp hmean)
          (Finset.prod_nonneg (fun i _ => activation_prior_nonnegative ht.1 ht.2 _))
      _ = B := by rw [← Finset.sum_mul, activation_product_prior_normalized, one_mul]
  have hm : (gridWindowCount d k) ≤ (2 * (k : ℝ)) ^ d := by
    simpa only [gridWindowCount, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by omega)) d
  calc
    _ ≤ B := hbudget
    _ ≤ 5 ^ d * (2 * k) ^ d *
        (K ^ 2 * Real.exp K * η ^ 4 * (n * (2 / k) ^ d) ^ 2) := by
      bound
    _ = _ := by
      rw [show (40 : ℝ) = 5 * 2 ^ 3 by norm_num]
      have htwo : (2 ^ 3) ^ d = ((2 : ℝ) ^ d) ^ 3 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 d]
      simp only [mul_pow, div_pow, htwo]
      field_simp <;> ring

end

variable {d : ℕ} {C : ModelConstants d} {P : LowSmoothnessTernaryConstants C} {k : ℕ} {η b t : ℝ}
    (ξ : TernaryVector (gridWindowCount d k)) (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ)
    (hvariance : η ^ 2 ≤ P.ρ)
include hfield

/-- The actual model parameter in each latent state of the indexed grid prior. -/
def gridPathParameter :
    RegressionParameter d :=
  P.pathParameter (indexedGridField η ξ) (indexedGridField_continuous η ξ) η t ht hvariance
    (fun x => (indexedGridField_abs_bound hη ξ x).trans (by nlinarith))

include hk hs1 hb in
theorem gridPathParameter_admissible
    (hscale : η = b / k ^ C.smoothness)
    (hholder : (2 ^ d + 68 * 2 ^ d * (d + 1)) * b ≤ C.holderBound) :
    Admissible C (gridPathParameter ξ hη ht hfield hvariance) := by
  have horder : C.order = 0 := by
    have hnat : C.order < 1 := by exact_mod_cast (C.order_lt.trans_le hs1)
    omega
  have hηb : η ≤ b := by
    rw [hscale]
    exact div_le_self hb (Real.one_le_rpow (by exact_mod_cast hk) C.smoothness_pos.le)
  apply P.pathParameter_admissible_order_zero _ _ η t ht hvariance _ horder
    (2 ^ d * b) ((68 * 2 ^ d * (d + 1)) * b)
    (by positivity) (by positivity) (by nlinarith [hholder])
  · intro x
    exact (indexedGridField_abs_bound hη ξ x).trans (mul_le_mul_of_nonneg_left hηb (by positivity))
  · intro x y
    rw [hscale, indexedGridField_eq]
    exact gridPriorField_holder_bound hk C.smoothness_pos.le hs1 hb ..

end NearlyMinimax
