module

public import NearlyMinimax.HighCenteredRowUnion
public import NearlyMinimax.HighScoreOrthogonality

@[expose] public section

/-! The actual full local signed-generator score. A genuine mark law acts
on the reset density and coefficient vector. The variance derivative occurs
exactly once, after the ordinary and fine-pair row actions are combined. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

section
variable {n : ℕ} (π : Measure E) (activation : E → ℝ) (a V η : ℝ) (p : Fin n → ℝ)
    (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ) (hc : ∀ γ, Measurable (fun e => cReset e γ))
    (ha : a ≠ 0) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : TernaryVector n)

def highMarkedResponseAction : ℝ :=
  ∫ e, activation e * (∏ i, pReset e i) *
    highResponseProduct a V η g w φ (cReset e) y ∂π

def highMarkedLocalScore : ℝ :=
  (highMarkedResponseAction π activation a V η pReset cReset g w φ y -
    η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
    ((∏ i, p i) * highResponseProduct a V η g w φ c y)

include hc in
theorem highMarkedResponseProduct_measurable :
    Measurable (fun e => highResponseProduct a V η g w φ (cReset e) y) := by
  apply Finset.measurable_fun_prod
  intro i _
  apply ternaryMass_measurable_comp
  unfold coefficientRegression
  fun_prop

include ha in
theorem highMarkedResponseProduct_abs_le_one {φ : Fin n → ι → ℝ} (v : ι → ℝ)
    (hp : ∀ i b, 0 ≤ ternaryMass a (coefficientRegression η g w φ v i) V b)
    (y : TernaryVector n) : |highResponseProduct a V η g w φ v y| ≤ 1 := by
  unfold highResponseProduct
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro i _
    positivity
  · intro i _
    rw [abs_of_nonneg (hp i (y i))]
    solve_by_elim [ternary_mass_le_one]

theorem highResponseProduct_ball_abs_le_one
    {n : ℕ} {C a V η ρ : ℝ} (ha : a ≠ 0) (hη : 0 ≤ η) (hηρ : η ≤ ρ/2)
    {g w : Fin n → ℝ} {φ : Fin n → ι → ℝ}
    (hg : ∀ u, |g u| ≤ ρ/2) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ u, |∑ γ, φ u γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    {v : ι → ℝ} (hv : ∑ γ, |v γ| ≤ C⁻¹) (y : TernaryVector n) :
    |highResponseProduct a V η g w φ v y| ≤ 1 :=
  highMarkedResponseProduct_abs_le_one a V η ha g w v
    (fun i => hp _ (coefficientRegression_abs_le hη hηρ (hg i) (hw i) (hφ v hv i))) y

end

variable {n : ℕ} {π : Measure E} {activation : E → ℝ} (hAct : Integrable activation π) {a V η : ℝ}
    (ha : a ≠ 0) {p : Fin n → ℝ} {pPlus : ℝ} (hpPlus : 0 ≤ pPlus) {pReset : E → Fin n → ℝ}
    (hReset : ∀ i, Measurable (fun e => pReset e i)) (hBound : ∀ e i, |pReset e i| ≤ pPlus)
    {cReset : E → ι → ℝ} (hc : ∀ γ, Measurable (fun e => cReset e γ)) {g w : Fin n → ℝ}
    {φ : Fin n → ι → ℝ} {c : ι → ℝ} (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hInt : ∀ y, Integrable (fun e => activation e * (∏ i, pReset e i) * highResponseProduct a V η g w φ (cReset e) y) π)

include hAct ha hpPlus hReset hBound hc in
/-- Integrability follows from the actual integrable activation, Borel
legal resets, and normalized nonnegative response masses. -/
theorem highMarkedResponseAction_integrable
    (hp : ∀ e i b, 0 ≤ ternaryMass a (coefficientRegression η g w φ (cReset e) i) V b)
    (y : TernaryVector n) :
    Integrable (fun e => activation e * (∏ i, pReset e i) *
      highResponseProduct a V η g w φ (cReset e) y) π := by
  have hDensity := hAct.mul_bdd
    (Finset.measurable_fun_prod _ (fun i _ => hReset i)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      exact finite_density_product_abs_bound (pReset e) hpPlus (hBound e)))
  exact hDensity.mul_bdd (highMarkedResponseProduct_measurable a V η cReset hc g w φ y).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      exact highMarkedResponseProduct_abs_le_one a V η ha g w (cReset e) (hp e) y))

include ha hInt in
/-- Response normalization identifies the actual total action with the
conditional density action, rather than assuming score centering. -/
theorem highMarkedResponseAction_sum :
    (∑ y : TernaryVector n, highMarkedResponseAction π activation a V η pReset cReset g w φ y) =
      ∫ e, activation e * ∏ i, pReset e i ∂π := by
  unfold highMarkedResponseAction
  rw [← integral_finsetSum Finset.univ (fun y _ => hInt y)]
  simp_rw [← Finset.mul_sum, high_response_product_normalized a V η ha, mul_one]

include hpd hInt in
/-- The full marked score is conditionally centered whenever the actual
signed density action vanishes. For the source row union this primitive
comes from each row's proved conditional zero-mass rule. -/
theorem highMarkedLocalScore_centered
    (hDensity : (∫ e, activation e * ∏ i, pReset e i ∂π) = 0) :
    (∫ y, highMarkedLocalScore π activation a V η p pReset cReset g w φ c y
      ∂Measure.pi (fun i => ternaryIndexMeasure (coefficientRegression η g w φ c i) V
        ha (fun b => (hp i b).le))) = 0 := by
  rw [ternary_index_product_integral]
  change (∑ y, highResponseProduct a V η g w φ c y *
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y) = 0
  have hB : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hpd i)
  have he (y : TernaryVector n) :
      highResponseProduct a V η g w φ c y *
        highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      (highMarkedResponseAction π activation a V η pReset cReset g w φ y -
        η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 *
          highResponseVarianceTerm a V η g w φ c y i) / (∏ i, p i) := by
    have hL : highResponseProduct a V η g w φ c y ≠ 0 :=
      ne_of_gt (Finset.prod_pos (fun i _ => hp i (y i)))
    unfold highMarkedLocalScore
    field_simp [hB, hL]
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    highMarkedResponseAction_sum ha hInt,
    hDensity, ← Finset.mul_sum, Finset.sum_comm]
  simp [← Finset.mul_sum, high_response_variance_term_sum_zero,
    mul_zero, Finset.sum_const_zero, sub_zero, zero_div]

theorem highMarkedLocalScore_depends_on_support (π : Measure E)
    (activation : E → ℝ) (a V η : ℝ) (p : Fin n → ℝ) (pReset : E → Fin n → ℝ)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    (y y' : TernaryVector n) (hyy : ∀ i ∈ S, y i = y' i)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      highMarkedLocalScore π activation a V η p pReset cReset g w φ c y' := by
  have hB : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hpd i)
  have hLy : highResponseProduct a V η g w φ c y ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hp i (y i)))
  have hLy' : highResponseProduct a V η g w φ c y' ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hp i (y' i)))
  have hfirst : highMarkedResponseAction π activation a V η pReset cReset g w φ y /
      highResponseProduct a V η g w φ c y =
    highMarkedResponseAction π activation a V η pReset cReset g w φ y' /
      highResponseProduct a V η g w φ c y' := by
    unfold highMarkedResponseAction
    rw [← integral_div, ← integral_div]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro e
    simp only [mul_div_assoc]
    rw [high_response_ratio_depends_on_support c (cReset e) hw hyy hp]
  have hvar :
      (∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
        highResponseProduct a V η g w φ c y =
      (∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y' i) /
        highResponseProduct a V η g w φ c y' := by
    simp_rw [Finset.sum_div, mul_div_assoc,
      high_response_variance_ratio a V η g w φ c y _ (fun i => hp i (y i)),
      high_response_variance_ratio a V η g w φ c y' _ (fun i => hp i (y' i))]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · rw [hyy i hi]
    · simp [hw i hi]
  have hrep (z : TernaryVector n) (hL : highResponseProduct a V η g w φ c z ≠ 0) :
      highMarkedLocalScore π activation a V η p pReset cReset g w φ c z =
      (highMarkedResponseAction π activation a V η pReset cReset g w φ z /
        highResponseProduct a V η g w φ c z) / (∏ i, p i) -
      η ^ 2 * ((∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c z i) /
        highResponseProduct a V η g w φ c z) := by
    unfold highMarkedLocalScore
    field_simp [hB, hL]
  grind

end

section RowUnion
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  {E : J → Type*} [∀ j, MeasurableSpace (E j)]

end RowUnion
end NearlyMinimax
