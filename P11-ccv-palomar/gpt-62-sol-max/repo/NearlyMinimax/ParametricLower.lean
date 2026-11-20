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

def labelBase : Measure (Fin 3) := ENNReal.ofReal (1 / 3 : ℝ) • Measure.count

instance labelBase_isProbability : IsProbabilityMeasure labelBase := by
  constructor
  simp [labelBase, Measure.smul_apply, Measure.count_univ]
  apply ENNReal.inv_mul_cancel <;> simp_all

def ternaryDensityLaw (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) : DensityLaw labelBase where
  density y := 3 * ternaryMass a 0 V y
  measurable := measurable_of_countable _
  integrable := Integrable.of_finite
  nonneg := Filter.Eventually.of_forall (fun y => mul_nonneg (by norm_num) (hp y))
  integral_one := by
    simp [labelBase, integral_smul_measure, integral_count, ← Finset.mul_sum, ternary_normalized a 0 V]

section
variable (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y)

theorem ternaryDensityLaw_measure :
    (ternaryDensityLaw a V ha hp).measure =
      Measure.count.withDensity (fun y => ENNReal.ofReal (ternaryMass a 0 V y)) := by
  unfold DensityLaw.measure ternaryDensityLaw labelBase
  rw [withDensity_smul_measure, ← withDensity_smul]
  · congr 1
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    simp
  fun_prop

theorem ternaryDensityLaw_map :
    (ternaryDensityLaw a V ha hp).measure.map (ternaryValue a) = ternaryMeasure a 0 V := by
  rw [ternaryDensityLaw_measure, count_withDensity,
    Measure.map_sum (measurable_of_countable _).aemeasurable, Measure.sum_fintype]
  simp [ternaryMeasure, weightedAtomMeasure, Measure.map_smul _ (measurable_of_countable _).aemeasurable, Measure.map_dirac]

end

def encodeResponse {d n : ℕ} (a : ℝ) :
    (Fin n → Fin 3) × (Fin n → Covariate d) → ObservedSample d n :=
  fun z i => (z.2 i, ternaryValue a (z.1 i))

theorem encodeResponse_measurable {d n : ℕ} (a : ℝ) :
    Measurable (encodeResponse (d := d) (n := n) a) := by
  fun_prop [Covariate, ObservedSample, encodeResponse, Observation]

theorem ternary_label_design_map {d : ℕ} (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) :
    (((ternaryDensityLaw a V ha hp).measure).prod (cubeVolume d)).map
      (fun z => (z.2, ternaryValue a z.1)) =
        observationLaw (uniformZeroParameter d a V ha hp) := by
  let _ := cubeVolume_isProbability d
  let _ := ternaryMeasure_isProbability a 0 V ha hp
  rw [uniformZeroParameter_observationLaw]
  have h := Measure.map_prod_map (ternaryDensityLaw a V ha hp).measure (cubeVolume d)
    (measurable_of_countable (ternaryValue a)) measurable_id
  rw [ternaryDensityLaw_map, Measure.map_id] at h
  calc
    _ = ((((ternaryDensityLaw a V ha hp).measure).prod (cubeVolume d)).map
        (Prod.map (ternaryValue a) id)).map Prod.swap := by
      rw [Measure.map_map measurable_swap
        ((measurable_of_countable (ternaryValue a)).prodMap measurable_id)]
      rfl
    _ = ((ternaryMeasure a 0 V).prod (cubeVolume d)).map Prod.swap := by simp_all
    _ = _ := Measure.prod_swap

theorem encodeResponse_measurePreserving {d n : ℕ} (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) :
    MeasurePreserving (encodeResponse (d := d) (n := n) a)
      ((Measure.pi (fun _ : Fin n => (ternaryDensityLaw a V ha hp).measure)).prod
        (Measure.pi (fun _ : Fin n => cubeVolume d)))
      (sampleLaw (uniformZeroParameter d a V ha hp) n) := by
  let _ := cubeVolume_isProbability d
  let _ := ternaryMeasure_isProbability a 0 V ha hp
  let _ : IsProbabilityMeasure (observationLaw (uniformZeroParameter d a V ha hp)) := by
    rw [uniformZeroParameter_observationLaw]
    infer_instance
  have hsingle : MeasurePreserving (fun z : Fin 3 × Covariate d =>
      (z.2, ternaryValue a z.1))
      (((ternaryDensityLaw a V ha hp).measure).prod (cubeVolume d))
      (observationLaw (uniformZeroParameter d a V ha hp)) :=
    ⟨measurable_snd.prodMk ((measurable_of_countable _).comp measurable_fst),
      ternary_label_design_map a V ha hp⟩
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin 3) (Covariate d) (Fin n)
  have he := (measurePreserving_arrowProdEquivProdArrow (Fin 3) (Covariate d) (Fin n)
    (fun _ => (ternaryDensityLaw a V ha hp).measure) (fun _ => cubeVolume d)).symm e
  have hm := (measurePreserving_pi _ _ (fun _ : Fin n => hsingle)).comp he
  assumption

abbrev ternaryDensitySlope (a : ℝ) (y : Fin 3) : ℝ := 3 * ternaryVarianceDerivative a y

theorem ternary_density_affine (a V : ℝ) (y : Fin 3) :
    3 * ternaryMass a 0 V y = ![0, 3, 0] y + V * ternaryDensitySlope a y := by
  fin_cases y <;> simp [ternaryMass, ternaryDensitySlope, ternaryVarianceDerivative] <;> ring

section
variable {d : ℕ} (C : ModelConstants d)

/-- Actual two-point testing lower bound for the original regression minimax
problem.  The premises are numerical legality and one-observation mass bounds,
not statistical risk or estimator assumptions. -/
theorem ternary_two_point_minimax_lower (n : ℕ)
    (a V₀ V₁ cf Cf : ℝ) (ha : 0 < a) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (hV₀ : C.varianceLower ≤ V₀) (hV₀upper : V₀ ≤ C.varianceUpper)
    (hV₁ : C.varianceLower ≤ V₁) (hV₁upper : V₁ ≤ C.varianceUpper)
    (hfourth₀ : a ^ 2 * V₀ ≤ C.fourthBound)
    (hfourth₁ : a ^ 2 * V₁ ≤ C.fourthBound)
    (hmass₀ : ∀ y, cf ≤ 3 * ternaryMass a 0 V₀ y)
    (hmass₁ : ∀ y, cf ≤ 3 * ternaryMass a 0 V₁ y)
    (hslope : ∀ y, |ternaryDensitySlope a y| ≤ Cf)
    (hsmall : (n : ℝ) * Cf ^ 2 * (V₀ - V₁) ^ 2 / (4 * cf) ≤ 1 / 4) :
    ENNReal.ofReal (|V₁ - V₀| / 4) ≤ minimaxRMS C n := by
  have hp₀ : ∀ y, 0 ≤ ternaryMass a 0 V₀ y := by
    intro y <;> grind
  have hp₁ : ∀ y, 0 ≤ ternaryMass a 0 V₁ y := by
    intro y
    linarith [hmass₁ y]
  have hθ₀ :=
    uniformZeroParameter_legal C a V₀ ha hV₀ hV₀upper hfourth₀ hp₀
  have hθ₁ :=
    uniformZeroParameter_legal C a V₁ ha hV₁ hV₁upper hfourth₁ hp₁
  let P₀ := ternaryDensityLaw a V₀ ha.ne' hp₀
  let P₁ := ternaryDensityLaw a V₁ ha.ne' hp₁
  let ν := Measure.pi (fun _ : Fin n => cubeVolume d)
  let _ := cubeVolume_isProbability d
  let _ : IsProbabilityMeasure ν := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => cubeVolume d)))
  let L := densityLawWithSeed ν (iidDensityLaw P₀ n)
  let R := densityLawWithSeed ν (iidDensityLaw P₁ n)
  have hH : hellingerSquared L R ≤ 1 / 4 := by
    have hone := affine_hellinger_bound P₀ P₁ ![0, 3, 0] (ternaryDensitySlope a)
      V₀ V₁ cf Cf hcf hCf
      (Filter.Eventually.of_forall (ternary_density_affine a V₀))
      (Filter.Eventually.of_forall (ternary_density_affine a V₁))
      (Filter.Eventually.of_forall (fun y => by simp_all [← ternary_density_affine]))
      (Filter.Eventually.of_forall (fun y => by simp_all [← ternary_density_affine]))
      (Filter.Eventually.of_forall hslope)
    change hellingerSquared (densityLawWithSeed ν (iidDensityLaw P₀ n))
      (densityLawWithSeed ν (iidDensityLaw P₁ n)) ≤ _
    rw [hellinger_with_seed]
    exact (hellinger_iid_le P₀ P₁ n).trans
      ((mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg n)).trans (by
        convert hsmall using 1; ring))
  rw [minimaxRMS_eq_inf_sup_eLpNorm]
  apply le_iInf
  intro T
  have ht := two_point_rmse_lower L R (T.val ∘ encodeResponse (d := d) (n := n) a)
    (T.property.comp (encodeResponse_measurable a)) V₀ V₁ hH
  simp only [L, R, densityLawWithSeed_measure, iidDensityLaw_measure] at ht
  have lift (V : ℝ) (hp : ∀ y, 0 ≤ ternaryMass a 0 V y)
      (hθ : Admissible C (uniformZeroParameter d a V ha.ne' hp)) :
      eLpNorm (fun z => T.val (encodeResponse a z) - V) 2
        ((Measure.pi (fun _ : Fin n => (ternaryDensityLaw a V ha.ne' hp).measure)).prod ν) ≤
        ⨆ θ : {θ // Admissible C θ}, eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n) :=
    (eLpNorm_comp_measurePreserving (T.property.sub measurable_const).aestronglyMeasurable
      (encodeResponse_measurePreserving a V ha.ne' hp)).trans_le
        (le_iSup (fun θ : {θ // Admissible C θ} =>
          eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n)) ⟨_, hθ⟩)
  exact ht.elim (fun h => h.trans (lift V₀ hp₀ hθ₀)) (fun h => h.trans (lift V₁ hp₁ hθ₁))

/-- The original statistical class has a positive root-n minimax RMS lower
bound for every sample size n>=1 and every smoothness/dimension regime.
The constants and the actual iid submodel are constructed, not assumed. -/
theorem parametric_minimax_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ minimaxRMS C n := by
  obtain ⟨P⟩ := parametricTernaryConstants_exists C
  refine ⟨P.delta / 2, div_pos P.delta_pos (by norm_num), ?_⟩
  intro n hn
  have hm := P.varianceMinus_mem n hn
  have hp := P.variancePlus_mem n hn
  have hb₀ := P.model_variance_bounds _ hm
  have hb₁ := P.model_variance_bounds _ hp
  have htest := ternary_two_point_minimax_lower C n P.a (P.varianceMinus n)
    (P.variancePlus n) P.cf P.Cf P.a_pos P.cf_pos P.Cf_pos.le
    hb₀.1 hb₀.2 hb₁.1 hb₁.2
    (P.fourth_le_of_mem _ hm) (P.fourth_le_of_mem _ hp)
    (P.density_lower _ hm) (P.density_lower _ hp)
    P.derivative_bound
    (P.score_budget_reverse n hn)
  have hinv : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
  have hscale : |P.variancePlus n - P.varianceMinus n| / 4 =
      (P.delta / 2) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [abs_of_pos (P.separation_pos n hn), P.separation n, hinv]
    ring
  simpa [hscale] using htest

end

end NearlyMinimax
