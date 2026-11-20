module

public import NearlyMinimax.FinePairRows
public import NearlyMinimax.FinePairTimeCost


@[expose] public section

/-! Nondegeneracy and exact activity costs of the actual fine-pair rows. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

theorem response_absolute_cost_ge_one {q : ℕ} (hq : 1 ≤ q) :
    (1 : ℝ) ≤ ∑ j : Fin (2*q+2), |responseWeight j| := by
  calc
    _ = _ := by
      rw [(response_rule_moments q 2 (by omega))]; norm_num
    _ ≤ _ :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (2*q+2), |responseWeight j| := by
      apply Finset.sum_le_sum
      intro j _
      have he : |responseNode j ^ 2| = responseNode j ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [abs_mul, he]
      apply mul_le_of_le_one_right (abs_nonneg _)
      have hj := responseNode_mem_unit q j
      nlinarith [hj.1, hj.2, sq_nonneg (responseNode j)]

section
variable {a b : ℝ} (ha : 0 < a) (hab : a < b) (d D M q : ℕ)

include ha hab in
theorem ordinary_density_absolute_cost_pos :
    0 < ∑ h : HighDensityMarkIndex D 2 D, |densityPacketWeight a b D 2 D h| := by
  rw [densityPacketWeight_variation a b ha hab D 2 D (by norm_num)]
  have hb  := (ha.trans hab).ne'
  have hθ := densityMargin_zero_ne a b ha hab
  have hp : densityPacketPrefactor a b 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (div_ne_zero hb hθ))
  unfold derivativeOrder <;> positivity

include ha hab in
theorem fine_density_absolute_cost_pos :
    0 < ∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h| := by
  rw [finePairDensityWeight_variation ha hab M]
  have hp : finePairDensityPrefactor a b ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (ha.trans hab).ne') (pow_ne_zero _ (densityMargin_zero_ne a b ha hab))
  positivity

theorem finePairRowMass_unit (a b C T₀ N : ℝ) :
    finePairRowMass d D M q a b C T₀ N .unit =
      (∑ h : HighDensityMarkIndex D 2 D, |densityPacketWeight a b D 2 D h|) *
      responseVariation q * (2*C^2) *
      (∑ i, ∑ j, |finePairUnitMatrix d D i j|) := by
  rw [finePairRowMass, highPacketMarkMass_eq_variation a b D 2 D q C
      (A := (fun _ => finePairUnitMatrix d D))
      (fun _ _ => measurable_const) (integrable_const _),
    highPacketSignedMeasure_totalVariation a b D 2 D q C
      (A := (fun _ => finePairUnitMatrix d D))
      (fun _ _ => measurable_const) (integrable_const _)]
  simp [separatedMatrixCost]

end

variable (d : ℕ) [NeZero d] (D M q : ℕ) (a b C T₀ N : ℝ) (hT : 0 ≤ T₀)
include hT

theorem finePairRowMass_coarse :
    finePairRowMass d D M q a b C T₀ N .coarse =
      (∑ h : HighDensityMarkIndex D 2 D, |densityPacketWeight a b D 2 D h|) *
      responseVariation q * (2*C^2) *
      ((∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * (T₀^2/2)) := by
  rw [finePairRowMass, highPacketMarkMass_eq_variation _ _ _ _ _ _ _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _),
    highPacketSignedMeasure_totalVariation _ _ _ _ _ _ _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _),
    finePairTimeMatrix_cost_integral d le_rfl hT]
  simp

theorem finePairRowMass_fine (hTN : T₀ ≤ N) :
    finePairRowMass d D M q a b C T₀ N .fine =
      (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) *
      responseVariation q * (2*C^2) *
      ((∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * ((N^2-T₀^2)/2)) := by
  rw [finePairRowMass, finePairPacketMarkMass]
  rw [signedMarkMass_eq_variation (tensorWeight_integrable (finePairDensityWeight a b M) q C
    (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _))]
  change ((finePairPacketSignedMeasure _ a b M q C _).variation univ).toReal = _
  rw [finePairPacketSignedMeasure_totalVariation a b M q C
    (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _),
    finePairTimeMatrix_cost_integral d hT hTN]

end NearlyMinimax
