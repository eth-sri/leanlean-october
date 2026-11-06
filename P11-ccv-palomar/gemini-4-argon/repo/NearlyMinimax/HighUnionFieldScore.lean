module
public import NearlyMinimax.HighCenteredRowUnion
public import NearlyMinimax.HighLocalFrame
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {n : ℕ}
section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
def highMarkedResponseAction  (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  ∫ e, activation e * (∏ i, pReset e i) *
    highResponseProduct a V η g w φ (cReset e) y ∂π
def highMarkedLocalScore  (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : Fin n → ℝ) (pReset : E → Fin n → ℝ)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  (highMarkedResponseAction π activation a V η pReset cReset g w φ y -
    η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
    ((∏ i, p i) * highResponseProduct a V η g w φ c y)
theorem highMarkedResponseProduct_measurable  (a V η : ℝ)
    (cReset : E → ι → ℝ) (hc : ∀ γ, Measurable (fun e => cReset e γ))
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (y : Fin n → Fin 3) :
    Measurable (fun e => highResponseProduct a V η g w φ (cReset e) y) := by
  apply Finset.measurable_fun_prod
  intro i _
  apply ternaryMass_measurable_comp
  unfold coefficientRegression
  fun_prop
theorem highMarkedResponseProduct_abs_le_one  (a V η ) (ha : a ≠ 0)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (v : ι → ℝ)
    (hp : ∀ i b, 0 ≤ ternaryMass a (coefficientRegression η g w φ v i) V b)
    (y : Fin n → Fin 3) : |highResponseProduct a V η g w φ v y| ≤ 1 := by
  unfold highResponseProduct
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [abs_of_nonneg (hp i (y i))]
    exact ternary_mass_le_one a _ V ha (hp i) (y i)
theorem highMarkedResponseAction_integrable  (π : Measure E)
    (activation : E → ℝ) (hAct : Integrable activation π)
    (a V η : ℝ) (ha : a ≠ 0) (pPlus : ℝ) (hpPlus : 0 ≤ pPlus)
    (pReset : E → Fin n → ℝ) (hReset : ∀ i, Measurable (fun e => pReset e i))
    (hBound : ∀ e i, |pReset e i| ≤ pPlus) (cReset : E → ι → ℝ)
    (hc : ∀ γ, Measurable (fun e => cReset e γ))
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (hp : ∀ e i b, 0 ≤ ternaryMass a (coefficientRegression η g w φ (cReset e) i) V b)
    (y : Fin n → Fin 3) :
    Integrable (fun e => activation e * (∏ i, pReset e i) *
      highResponseProduct a V η g w φ (cReset e) y) π := by
  have hDensity := hAct.mul_bdd
    (Finset.measurable_fun_prod _ (fun i _ => hReset i)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      simpa only [Real.norm_eq_abs] using
        finite_density_product_abs_bound (pReset e) pPlus hpPlus (hBound e)))
  exact hDensity.mul_bdd (highMarkedResponseProduct_measurable a V η cReset hc g w φ y).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      simpa only [Real.norm_eq_abs] using
        highMarkedResponseProduct_abs_le_one a V η ha g w φ (cReset e) (hp e) y))
theorem highMarkedLocalScore_centered  (π activation a V η ha p pReset)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
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
  have he (y : Fin n → Fin 3) :
      highResponseProduct a V η g w φ c y *
        highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      (highMarkedResponseAction π activation a V η pReset cReset g w φ y -
        η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 *
          highResponseVarianceTerm a V η g w φ c y i) / (∏ i, p i) := by
    have hL : highResponseProduct a V η g w φ c y ≠ 0 :=
      ne_of_gt (Finset.prod_pos (fun i _ => hp i (y i)))
    unfold highMarkedLocalScore
    field_simp [Finset.prod_ne_zero_iff.mpr (fun i _ => hpd i), hL]
  simp_rw [he]
  have h_highMarkedResponseAction_sum : (∑ y : Fin n → Fin 3, highMarkedResponseAction π activation a V η pReset cReset g w φ y) =
      ∫ e, activation e * ∏ i, pReset e i ∂π := by
    unfold highMarkedResponseAction
    have h_high_response_product_normalized (g : Fin n → ℝ) (w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) : ∑ y : Fin n → Fin 3, highResponseProduct a V η g w φ c y = 1 := by
      unfold highResponseProduct
      rw [← Fintype.prod_sum]
      simp [ternary_normalized a _ V ha]
    rw [← integral_finsetSum Finset.univ (fun y _ => hInt y)]
    simp_rw [← Finset.mul_sum, h_high_response_product_normalized, mul_one]
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    h_highMarkedResponseAction_sum,
    hDensity, ← Finset.mul_sum, Finset.sum_comm]
  have h_high_response_variance_term_sum_zero (i : Fin n) : ∑ y : Fin n → Fin 3, highResponseVarianceTerm a V η g w φ c y i = 0 := by
    simpa only [highResponseVarianceTerm, patchVarianceTerm, zero_mul, add_zero] using
      patch_variance_term_sum_zero n a V 0 (coefficientRegression η g w φ c) (fun _ => 0) 0 i
  simp only [← Finset.mul_sum, h_high_response_variance_term_sum_zero,
    mul_zero, Finset.sum_const_zero, sub_zero, zero_div]
theorem highMarkedLocalScore_depends_on_support  (π activation a V η p pReset)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    (y y' : Fin n → Fin 3) (hyy : ∀ i ∈ S, y i = y' i)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      highMarkedLocalScore π activation a V η p pReset cReset g w φ c y' := by
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
    have h_high_response_ratio_depends_on_support : highResponseProduct a V η g w φ (cReset e) y / highResponseProduct a V η g w φ c y =
      highResponseProduct a V η g w φ (cReset e) y' / highResponseProduct a V η g w φ c y' := by
      let outside (z : Fin n → Fin 3) : ℝ :=
        ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, ternaryMass a (g i) V (z i)
      let inside (z : Fin n → Fin 3) (u : ι → ℝ) : ℝ :=
        ∏ i ∈ S, ternaryMass a (coefficientRegression η g w φ u i) V (z i)
      have hfactor (z : Fin n → Fin 3) (u : ι → ℝ) :
          highResponseProduct a V η g w φ u z = outside z * inside z u := by
        unfold highResponseProduct
        rw [← Finset.prod_sdiff (Finset.subset_univ S)]
        dsimp [outside, inside]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        simp [coefficientRegression, hw i (Finset.mem_sdiff.mp hi).2]
      have hout (z : Fin n → Fin 3) : outside z ≠ 0 := by
        apply ne_of_gt
        apply Finset.prod_pos
        intro i hi
        simpa [coefficientRegression, hw i (Finset.mem_sdiff.mp hi).2] using hp i (z i)
      have hin (z : Fin n → Fin 3) : inside z c ≠ 0 :=
        ne_of_gt (Finset.prod_pos (fun i _ => hp i (z i)))
      have hs (u : ι → ℝ) : inside y u = inside y' u := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hyy i hi]
      rw [hfactor y (cReset e), hfactor y c, hfactor y' (cReset e), hfactor y' c, hs (cReset e), hs c]
      field_simp [hout y, hout y', hin y']
    rw [h_high_response_ratio_depends_on_support]
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
    field_simp [Finset.prod_ne_zero_iff.mpr (fun i _ => hpd i), hL]
  rw [hrep y (ne_of_gt (Finset.prod_pos (fun i _ => hp i (y i)))), hrep y' hLy', hfirst, hvar]
end
section RowUnion
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  {E : J → Type*} [∀ j, MeasurableSpace (E j)]
end RowUnion
section GenericFamily
variable {J ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
theorem highMarkedLocalScores_orthogonal 
    (π : J → Measure E) (activation : J → E → ℝ) (a V η : ℝ) (ha : a ≠ 0)
    (p : Fin n → ℝ) (pReset : J → E → Fin n → ℝ)
    (cReset : J → E → ι → ℝ) (g w : J → Fin n → ℝ)
    (φ : J → Fin n → ι → ℝ) (c : J → ι → ℝ) (f : Fin n → ℝ)
    (hreg : ∀ j, coefficientRegression η (g j) (w j) (φ j) (c j) = f)
    (S : J → Finset (Fin n)) (hw : ∀ j i, i ∉ S j → w j i = 0)
    (hpd : ∀ i, p i ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (f i) V b)
    (hInt : ∀ j y, Integrable (fun e => activation j e * (∏ i, pReset j e i) *
      highResponseProduct a V η (g j) (w j) (φ j) (cReset j e) y) (π j))
    (hDensity : ∀ j, (∫ e, activation j e * ∏ i, pReset j e i ∂π j) = 0)
    (j l : J) (hST : Disjoint (S j) (S l)) :
    (∫ y, highMarkedLocalScore (π j) (activation j) a V η p (pReset j) (cReset j)
      (g j) (w j) (φ j) (c j) y *
      highMarkedLocalScore (π l) (activation l) a V η p (pReset l) (cReset l)
        (g l) (w l) (φ l) (c l) y
      ∂Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (fun b => (hp i b).le))) = 0 := by
  let μ : Fin n → Measure (Fin 3) := fun i =>
    ternaryIndexMeasure a (f i) V ha (fun b => (hp i b).le)
  have hp' (j : J) (i : Fin n) (b : Fin 3) :
      0 < ternaryMass a (coefficientRegression η (g j) (w j) (φ j) (c j) i) V b := by
    rw [hreg j]
    exact hp i b
  apply local_response_scores_orthogonal μ _ _ (S j) (S l) hST
  · intro y y' hyy
    exact highMarkedLocalScore_depends_on_support (π j) (activation j) a V η p
      (pReset j) (cReset j) (g j) (w j) (φ j) (c j) (S j) (hw j) y y' hyy hpd (hp' j)
  · intro y y' hyy
    exact highMarkedLocalScore_depends_on_support (π l) (activation l) a V η p
      (pReset l) (cReset l) (g l) (w l) (φ l) (c l) (S l) (hw l) y y' hyy hpd (hp' l)
  · have h := highMarkedLocalScore_centered (π j) (activation j) a V η ha p
      (pReset j) (cReset j) (g j) (w j) (φ j) (c j) hpd (hp' j) (hInt j) (hDensity j)
    simpa only [hreg j] using h
end GenericFamily
section ActualField
variable {E : Type*} [MeasurableSpace E]
def highFrameMarkedScore (d k D n : ℕ) [NeZero k]
    (π : HighWindowLabels d k → Measure E)
    (activation : HighWindowLabels d k → E → ℝ) (a V η : ℝ) (p : Fin n → ℝ)
    (pReset : HighWindowLabels d k → E → Fin n → ℝ)
    (cReset : HighWindowLabels d k → E → HighFrameIndex d D → ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (x : Fin n → Covariate d)
    (j : HighWindowLabels d k) (y : Fin n → Fin 3) : ℝ :=
  highMarkedLocalScore (π j) (activation j) a V η p (pReset j) (cReset j)
    (fun i => highLocalFieldWithout d k D η c j (x i))
    (fun i => highPeriodicTensor d k j (x i))
    (fun i => highLocalFrameFeature k j (x i)) (c j) y
end ActualField
end NearlyMinimax
