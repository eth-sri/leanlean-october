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
variable {n : ℕ}

section
variable (π : Measure E)
include π

def highMarkedResponseAction   (activation : E → ℝ)
    a V η (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) φ y  :=
  ∫ e, activation e * (∏ i, pReset e i) *
    highResponseProduct a V η g w φ (cReset e) y ∂π

def highMarkedLocalScore   activation
    a V η (p : Fin n → ℝ) pReset
    cReset (g w : Fin n → ℝ) φ
    (c : ι → ℝ) y  :=
  (highMarkedResponseAction π activation a V η pReset cReset g w φ y -
    η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
    ((∏ i, p i) * highResponseProduct a V η g w φ c y)
end


theorem highMarkedResponseProduct_measurable  a V η
    (cReset : E → ι → ℝ) (hc : ∀ γ, Measurable (fun e => cReset e γ))
    (g w : Fin n → ℝ) φ y :
    Measurable (fun e => highResponseProduct a V η g w φ (cReset e) y) := by
  
  apply Finset.measurable_fun_prod
  intro i _
  apply ternaryMass_measurable_comp
  unfold coefficientRegression
  fun_prop

theorem highMarkedResponseProduct_abs_le_one  a V η (ha : a ≠ 0)
    (g w : Fin n → ℝ) φ (v : ι → ℝ)
    (hp : ∀ i b, 0 ≤ ternaryMass a (coefficientRegression η g w φ v i) V b)
    y : |highResponseProduct a V η g w φ v y| ≤ 1 := by
  unfold highResponseProduct
  rw [Finset.abs_prod]
  simp_all [Finset.prod_le_one₀, abs_of_nonneg, ternary_mass_le_one]

section
variable (π : Measure E)

/-- Integrability follows from the actual integrable activation, Borel
legal resets, and normalized nonnegative response masses. -/
theorem highMarkedResponseAction_integrable  
    activation (hAct : Integrable activation π)
    a V η (ha : a ≠ 0) pPlus (hpPlus : 0 ≤ pPlus)
    (pReset : E → Fin n → ℝ) (hReset : ∀ i, Measurable (fun e => pReset e i))
    (hBound : ∀ e i, |pReset e i| ≤ pPlus) (cReset : E → ι → ℝ)
    (hc : ∀ γ, Measurable (fun e => cReset e γ))
    (g w : Fin n → ℝ) φ
    (hp : ∀ e i b, 0 ≤ ternaryMass a (coefficientRegression η g w φ (cReset e) i) V b)
    y :
    Integrable (fun e => activation e * (∏ i, pReset e i) *
      highResponseProduct a V η g w φ (cReset e) y) π := by
  have hDensity := hAct.mul_bdd
    (Finset.measurable_fun_prod _ (fun i _ => hReset i)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      solve_by_elim [finite_density_product_abs_bound]))
  exact hDensity.mul_bdd (highMarkedResponseProduct_measurable a V η cReset hc g w φ y).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      solve_by_elim [highMarkedResponseProduct_abs_le_one]))

/-- Response normalization identifies the actual total action with the
conditional density action, rather than assuming score centering. -/
theorem highMarkedResponseAction_sum   activation
    a V η (ha : a ≠ 0) pReset (cReset : E → ι → ℝ)
    g w φ
    (hInt : ∀ y, Integrable (fun e => activation e * (∏ i, pReset e i) *
      highResponseProduct a V η g w φ (cReset e) y) π) :
    (∑ y : Fin n → Fin 3, highMarkedResponseAction π activation a V η pReset cReset g w φ y) =
      ∫ e, activation e * ∏ i, pReset e i ∂π := by
  unfold highMarkedResponseAction
  rw [← integral_finsetSum Finset.univ (fun y _ => hInt y)]
  simp_rw [← Finset.mul_sum, high_response_product_normalized a V η ha, mul_one]

/-- The full marked score is conditionally centered whenever the actual
signed density action vanishes. For the source row union this primitive
comes from each row's proved conditional zero-mass rule. -/
theorem highMarkedLocalScore_centered   activation
    a V η ha p pReset
    cReset (g w : Fin n → ℝ) φ (c : ι → ℝ)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hInt : ∀ y, Integrable (fun e => activation e * (∏ i, pReset e i) *
      highResponseProduct a V η g w φ (cReset e) y) π)
    (hDensity : (∫ e, activation e * ∏ i, pReset e i ∂π) = 0) :
    (∫ y, highMarkedLocalScore π activation a V η p pReset cReset g w φ c y
      ∂Measure.pi (fun i => ternaryIndexMeasure a (coefficientRegression η g w φ c i) V
        ha (fun b => (hp i b).le))) = 0 := by
  rw [ternary_index_product_integral]
  change (∑ y, highResponseProduct a V η g w φ c y *
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y) = 0
  have hB : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hpd i)
  have he (y : Fin n → Fin 3) :
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
    highMarkedResponseAction_sum π activation a V η ha pReset cReset g w φ hInt,
    hDensity, ← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, high_response_variance_term_sum_zero,
    mul_zero, Finset.sum_const_zero, sub_zero, zero_div]

theorem highMarkedLocalScore_depends_on_support  
    activation a V η p pReset
    cReset g w φ (c : ι → ℝ)
    (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    y y' (hyy : ∀ i ∈ S, y i = y' i)
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
    rw [high_response_ratio_depends_on_support a V η g w φ c (cReset e) S hw y y' hyy hp]
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
  have hrep (z : Fin n → Fin 3) (hL : highResponseProduct a V η g w φ c z ≠ 0) :
      highMarkedLocalScore π activation a V η p pReset cReset g w φ c z =
      (highMarkedResponseAction π activation a V η pReset cReset g w φ z /
        highResponseProduct a V η g w φ c z) / (∏ i, p i) -
      η ^ 2 * ((∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c z i) /
        highResponseProduct a V η g w φ c z) := by
    unfold highMarkedLocalScore
    field_simp [hB, hL]
  rw [hrep y hLy, hrep y' hLy', hfirst, hvar]
end

end


end

section RowUnion
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  {E : J → Type*} [∀ j, MeasurableSpace (E j)]

end RowUnion
end NearlyMinimax
