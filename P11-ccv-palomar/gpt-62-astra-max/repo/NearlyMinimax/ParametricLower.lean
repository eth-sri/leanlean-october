module

public import NearlyMinimax.Clipping
public import NearlyMinimax.RiskIdentity
public import RoughRegime.LowerMeasure
public import NearlyMinimax.ParametricConstants


@[expose] public section

/-! Two-point testing for the actual ternary-response regression submodel.
This file constructs probability densities and transfers testing to the
original observation space.  No minimax rate is an assumed premise.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
open RoughRegime.GeneralTesting RoughRegime.LowerMeasure

def labelBase : Measure (Fin 3) := ENNReal.ofReal (1 / 3) • Measure.count

instance labelBase_isProbability : IsProbabilityMeasure labelBase := by
  constructor
  simp [labelBase, Measure.smul_apply, Measure.count_univ]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

def ternaryDensityLaw {a V : ℝ} (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) : DensityLaw labelBase where
  density y := 3 * ternaryMass a 0 V y
  measurable := measurable_of_countable _
  integrable := Integrable.of_finite
  nonneg := Filter.Eventually.of_forall (fun y => mul_nonneg (by norm_num) (hp y))
  integral_one := by
    rw [labelBase, integral_smul_measure, integral_count]
    norm_num only [ENNReal.toReal_ofReal, smul_eq_mul]
    rw [← Finset.mul_sum, ternary_normalized 0 V ha]
    norm_num

section
variable {d n : ℕ} (a V : ℝ) (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a 0 V y)

theorem ternaryDensityLaw_measure :
    (ternaryDensityLaw ha hp).measure =
      Measure.count.withDensity (fun y => ENNReal.ofReal (ternaryMass a 0 V y)) := by
  unfold DensityLaw.measure ternaryDensityLaw labelBase
  rw [withDensity_smul_measure, ← withDensity_smul]
  · congr 1
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by norm_num)]
    ring
  · fun_prop

theorem ternaryDensityLaw_map :
    (ternaryDensityLaw ha hp).measure.map (ternaryValue a) = ternaryMeasure a 0 V := by
  rw [ternaryDensityLaw_measure, count_withDensity,
    Measure.map_sum (measurable_of_countable _).aemeasurable, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro y _
  rw [Measure.map_smul _ (measurable_of_countable _).aemeasurable, Measure.map_dirac]


def encodeResponse :
    (TernaryVector n) × (DesignSample d n) → (Fin n → Observation d) :=
  fun z i => (z.2 i, ternaryValue a (z.1 i))

theorem encodeResponse_measurable :
    Measurable (encodeResponse (d := d) (n := n) a) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply i).comp measurable_snd).prodMk
    ((measurable_of_countable (ternaryValue a)).comp
      ((measurable_pi_apply i).comp measurable_fst))

end

section
variable {d n : ℕ} {a V : ℝ} (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a 0 V y)

theorem ternary_label_design_map :
    let jointLaw := ((ternaryDensityLaw ha hp).measure).prod (cubeVolume d)
    (jointLaw).map
      (fun z => (z.2, ternaryValue a z.1)) =
        observationLaw (uniformZeroParameter d ha hp) := by
  intro jointLaw
  let _ := cubeVolume_isProbability d
  let _ := ternaryMeasure_isProbability ha hp
  rw [uniformZeroParameter_observationLaw]
  have h := Measure.map_prod_map (ternaryDensityLaw ha hp).measure (cubeVolume d)
    (measurable_of_countable (ternaryValue a)) measurable_id
  rw [ternaryDensityLaw_map, Measure.map_id] at h
  calc
    _ = ((jointLaw).map
        (Prod.map (ternaryValue a) id)).map Prod.swap := by
      rw [Measure.map_map measurable_swap
        ((measurable_of_countable (ternaryValue a)).prodMap measurable_id)]
      rfl
    _ = _ := by rw [← h]
    _ = _ := Measure.prod_swap

theorem encodeResponse_measurePreserving :
    MeasurePreserving (encodeResponse a)
      ((Measure.pi (fun _ => (ternaryDensityLaw ha hp).measure)).prod
        (Measure.pi (fun _ => cubeVolume d)))
      (sampleLaw (uniformZeroParameter d ha hp) n) := by
  let _ := cubeVolume_isProbability d
  let _ := ternaryMeasure_isProbability ha hp
  let _ : IsProbabilityMeasure (observationLaw (uniformZeroParameter d ha hp)) := by
    rw [uniformZeroParameter_observationLaw]
    infer_instance
  have he := (measurePreserving_arrowProdEquivProdArrow (Fin 3) (Covariate d) (Fin n)
    (fun _ => (ternaryDensityLaw ha hp).measure) (fun _ => cubeVolume d)).symm (MeasurableEquiv.arrowProdEquivProdArrow (Fin 3) (Covariate d) (Fin n))
  exact (measurePreserving_pi _ _ (fun _ => (⟨by fun_prop, ternary_label_design_map ha hp⟩))).comp he

end

variable (a : ℝ) {d : ℕ}

def ternaryDensitySlope : Fin 3 → ℝ :=
  ![3 / (2 * a ^ 2), -3 / a ^ 2, 3 / (2 * a ^ 2)]

theorem ternary_density_affine (V : ℝ) (y : Fin 3) :
    3 * ternaryMass a 0 V y = ![0, 3, 0] y + V * ternaryDensitySlope a y := by
  fin_cases y <;> simp [ternaryMass, ternaryDensitySlope, div_eq_mul_inv] <;> ring

/-- Actual two-point testing lower bound for the original regression minimax
problem.  The premises are numerical legality and one-observation mass bounds,
not statistical risk or estimator assumptions. -/
theorem ternary_two_point_minimax_lower {C : ModelConstants d} {n : ℕ}
    {a V₀ V₁ cf Cf : ℝ} (ha : 0 < a) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (hV₀ : C.varianceLower ≤ V₀) (hV₀upper : V₀ ≤ C.varianceUpper)
    (hV₁ : C.varianceLower ≤ V₁) (hV₁upper : V₁ ≤ C.varianceUpper)
    (hVa₀ : V₀ < a ^ 2) (hVa₁ : V₁ < a ^ 2)
    (hfourth₀ : a ^ 2 * V₀ ≤ C.fourthBound)
    (hfourth₁ : a ^ 2 * V₁ ≤ C.fourthBound)
    (hmass₀ : ∀ y, cf ≤ 3 * ternaryMass a 0 V₀ y)
    (hmass₁ : ∀ y, cf ≤ 3 * ternaryMass a 0 V₁ y)
    (hslope : ∀ y, |ternaryDensitySlope a y| ≤ Cf)
    (hsmall : n * Cf ^ 2 * (V₀ - V₁) ^ 2 / (4 * cf) ≤ 1 / 4) :
    ENNReal.ofReal (|V₁ - V₀| / 4) ≤ minimaxRMS C n := by
  have hp₀ : ∀ y, 0 ≤ ternaryMass a 0 V₀ y := by
    intro y
    linarith [hmass₀ y]
  have hp₁ : ∀ y, 0 ≤ ternaryMass a 0 V₁ y := by
    intro y
    linarith [hmass₁ y]
  let θ₀ := uniformZeroParameter d ha.ne' hp₀
  let θ₁ := uniformZeroParameter d ha.ne' hp₁
  have hθ₀  :=
    ternary_submodel_admissible ha hV₀ hV₀upper hfourth₀ hp₀
  have hθ₁  :=
    ternary_submodel_admissible ha hV₁ hV₁upper hfourth₁ hp₁
  let P₀ := ternaryDensityLaw ha.ne' hp₀
  let P₁ := ternaryDensityLaw ha.ne' hp₁
  let ν := Measure.pi (fun _ : Fin n => cubeVolume d)
  let _ := cubeVolume_isProbability d
  let _ : IsProbabilityMeasure ν := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ => cubeVolume d)))
  let L := densityLawWithSeed ν (iidDensityLaw P₀ n)
  let R := densityLawWithSeed ν (iidDensityLaw P₁ n)
  have hH : hellingerSquared L R ≤ 1 / 4 := by
    have hone := affine_hellinger_bound (L := P₀) (R := P₁) hcf hCf
      (Filter.Eventually.of_forall (ternary_density_affine a V₀))
      (Filter.Eventually.of_forall (ternary_density_affine a V₁))
      (Filter.Eventually.of_forall (fun y => by rw [← ternary_density_affine]; exact hmass₀ y))
      (Filter.Eventually.of_forall (fun y => by rw [← ternary_density_affine]; exact hmass₁ y))
      (Filter.Eventually.of_forall hslope)
    rw [hellinger_with_seed]
    exact (hellinger_iid_le P₀ P₁ n).trans
      ((mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg n)).trans (by
        convert hsmall using 1; ring))
  have hL : L.measure = (Measure.pi (fun _ => P₀.measure)).prod ν := by
    rw [densityLawWithSeed_measure, iidDensityLaw_measure]
  have hR : R.measure = (Measure.pi (fun _ => P₁.measure)).prod ν := by
    rw [densityLawWithSeed_measure, iidDensityLaw_measure]
  rw [minimaxRMS_eq_inf_sup_eLpNorm]
  apply le_iInf
  intro T
  have ht := two_point_rmse_lower
    (T.property.comp (encodeResponse_measurable a)) V₀ V₁ hH
  rw [hL, hR] at ht
  have he₀ : eLpNorm (fun z => T.val (encodeResponse a z) - V₀) 2
      ((Measure.pi (fun _ => P₀.measure)).prod ν) =
      eLpNorm (fun z => T.val z - θ₀.variance) 2 (sampleLaw θ₀ n) := eLpNorm_comp_measurePreserving (T.property.sub measurable_const).aestronglyMeasurable
      (encodeResponse_measurePreserving ha.ne' hp₀)
  have he₁ : eLpNorm (fun z => T.val (encodeResponse a z) - V₁) 2
      ((Measure.pi (fun _ => P₁.measure)).prod ν) =
      eLpNorm (fun z => T.val z - θ₁.variance) 2 (sampleLaw θ₁ n) := eLpNorm_comp_measurePreserving (T.property.sub measurable_const).aestronglyMeasurable
      (encodeResponse_measurePreserving ha.ne' hp₁)
  change _ ≤ eLpNorm (fun z => T.val (encodeResponse a z) - V₀) 2 _ ∨
    _ ≤ eLpNorm (fun z => T.val (encodeResponse a z) - V₁) 2 _ at ht
  rw [he₀, he₁] at ht
  rcases ht with ht | ht
  · exact ht.trans (le_iSup (fun θ : {θ // Admissible C θ} =>
      eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n)) ⟨θ₀, hθ₀⟩)
  · exact ht.trans (le_iSup (fun θ : {θ // Admissible C θ} =>
      eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n)) ⟨θ₁, hθ₁⟩)

theorem ternaryDensitySlope_eq (y : Fin 3) :
    ternaryDensitySlope a y = 3 * ternaryVarianceDerivative a y := by
  fin_cases y <;> simp [ternaryDensitySlope, ternaryVarianceDerivative] <;> ring

/-- The original statistical class has a positive root-n minimax RMS lower
bound for every sample size n>=1 and every smoothness/dimension regime.
The constants and the actual iid submodel are constructed, not assumed. -/
theorem parametric_minimax_lower (C : ModelConstants d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * n ^ (-(1 / 2 : ℝ))) ≤ minimaxRMS C n := by
  obtain ⟨P⟩ := parametricTernaryConstants_exists C
  refine ⟨P.delta / 2, div_pos P.delta_pos (by norm_num), ?_⟩
  intro n hn
  have hm := P.varianceMinus_mem n hn
  have hp := P.variancePlus_mem n hn
  have hb₀ := P.model_variance_bounds _ hm
  have hb₁ := P.model_variance_bounds _ hp
  have htest := ternary_two_point_minimax_lower P.a_pos P.cf_pos P.Cf_pos.le
    hb₀.1 hb₀.2 hb₁.1 hb₁.2
    (P.variance_lt_square_of_mem _ hm) (P.variance_lt_square_of_mem _ hp)
    (P.fourth_le_of_mem _ hm) (P.fourth_le_of_mem _ hp)
    (P.density_lower _ hm) (P.density_lower _ hp)
    (fun y => by rw [ternaryDensitySlope_eq]; exact P.derivative_bound y)
    (by convert P.score_budget n hn using 1 <;> ring)
  have hinv : n ^ (-(1 / 2 : ℝ)) = (Real.sqrt n)⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
  have hscale : |P.variancePlus n - P.varianceMinus n| / 4 =
      (P.delta / 2) * n ^ (-(1 / 2 : ℝ)) := by
    rw [abs_of_pos (by rw [P.separation]; exact div_pos (mul_pos (by norm_num) P.delta_pos) (by positivity)), P.separation n, hinv]
    ring
  rw [hscale] at htest
  exact htest

end NearlyMinimax
