module

public import NearlyMinimax.HighPacketBalancing

@[expose] public section

/-! A genuine finite tagged union of centered row references. Row selection
is weighted by its actual variation budget, preserving the source constant
and the signed generator action. Distinct zero-activation corrective tags are
allowed by the source and do not change the signed measure. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

section
variable {J : Type*} [Fintype J] {E : J → Type*} [∀ j, MeasurableSpace (E j)]

section
variable (π : (j : J) → Measure (E j)) (B : J → ℝ) (w : (j : J) → E j → ℝ) (hB : ∀ j, 0 ≤ B j)
    {F : Sigma E → ℝ} (hF : Measurable F) (hInt : ∀ j, Integrable (fun e => F ⟨j, e⟩) (π j))

def highRowTotalMass : ℝ := ∑ j, B j

def highRowSelectionProbability (j : J) : ℝ := B j / highRowTotalMass B

theorem highRowSelectionProbability_nonneg {B : J → ℝ} (hB : ∀ j, 0 ≤ B j) (j : J) :
    0 ≤ highRowSelectionProbability B j :=
  div_nonneg (hB j) (Finset.sum_nonneg (fun j _ => hB j))

theorem highRowSelectionProbability_pos {B : J → ℝ} (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (j : J) : 0 < highRowSelectionProbability B j :=
  div_pos (hB j) hTotal

theorem highRowSelectionProbability_sum {B : J → ℝ} (hTotal : highRowTotalMass B ≠ 0) :
    (∑ j, highRowSelectionProbability B j) = 1 := by
  unfold highRowSelectionProbability
  rw [← Finset.sum_div]
  exact div_self hTotal

/-- The actual positive reference law on the finite tagged mark union. -/
def highRowReferenceUnion : Measure (Sigma E) :=
  ∑ j, ENNReal.ofReal (highRowSelectionProbability B j) • (π j).map (Sigma.mk j)

theorem highRowReferenceUnion_probability
    [∀ j, IsProbabilityMeasure (π j)] {B : J → ℝ} (hB : ∀ j, 0 ≤ B j)
    (hTotal : 0 < highRowTotalMass B) : IsProbabilityMeasure (highRowReferenceUnion π B) := by
  constructor
  rw [highRowReferenceUnion, Measure.finsetSum_apply]
  simp
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => highRowSelectionProbability_nonneg hB j),
    highRowSelectionProbability_sum hTotal.ne']
  norm_num

include hF hInt in
theorem highRowReferenceUnion_integrable :
    Integrable F (highRowReferenceUnion π B) := by
  apply integrable_finsetSum_measure.mpr
  intro j _
  have h := (integrable_map_measure hF.aestronglyMeasurable (measurable_sigma_mk_actual j).aemeasurable).mpr
    (hInt j)
  exact h.smul_measure ENNReal.ofReal_ne_top

include hB hF hInt in
theorem highRowReferenceUnion_integral :
    (∫ e, F e ∂highRowReferenceUnion π B) =
      ∑ j, highRowSelectionProbability B j * ∫ e, F ⟨j, e⟩ ∂π j := by
  unfold highRowReferenceUnion
  rw [integral_finsetSum_measure (fun j _ =>
    ((integrable_map_measure hF.aestronglyMeasurable (measurable_sigma_mk_actual j).aemeasurable).mpr
      (hInt j)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_smul_measure, integral_map (measurable_sigma_mk_actual j).aemeasurable hF.aestronglyMeasurable,
    ENNReal.toReal_ofReal (highRowSelectionProbability_nonneg hB j), smul_eq_mul]

def highRowUnionActivation (e : Sigma E) : ℝ :=
  w e.1 e.2 / highRowSelectionProbability B e.1

end

section
variable {π : (j : J) → Measure (E j)} (B : J → ℝ) {w : (j : J) → E j → ℝ} (hw : ∀ j, Measurable (w j))
include hw

theorem highRowUnionActivation_measurable : Measurable (highRowUnionActivation B w) :=
  sigma_uncurry_measurable (fun j => (hw j).div_const _)

theorem highRowUnionActivation_integrable
    (hInt : ∀ j, Integrable (w j) (π j)) :
    Integrable (highRowUnionActivation B w) (highRowReferenceUnion π B) :=
  highRowReferenceUnion_integrable π B (highRowUnionActivation_measurable B hw)
    (fun j => by simpa only [highRowUnionActivation] using
      (hInt j).div_const (highRowSelectionProbability B j))

end

variable {π : (j : J) → Measure (E j)} {B : J → ℝ} (hB : ∀ j, 0 ≤ B j)

include hB in
/-- Every row is genuinely centered; hence so is the combined activation. -/
theorem highRowUnionActivation_centered {w : (j : J) → E j → ℝ}
    (hw : ∀ j, Measurable (w j)) (hInt : ∀ j, Integrable (w j) (π j))
    (hCenter : ∀ j, (∫ e, w j e ∂π j) = 0) :
    (∫ e, highRowUnionActivation B w e ∂highRowReferenceUnion π B) = 0 := by
  rw [highRowReferenceUnion_integral π B hB (highRowUnionActivation_measurable B hw)
    (fun j => by simpa only [highRowUnionActivation] using
      (hInt j).div_const (highRowSelectionProbability B j))]
  simp only [highRowUnionActivation, integral_div, hCenter, zero_div, mul_zero, Finset.sum_const_zero]

/-- The exact source activation budget is retained by the finite mixture. -/
theorem highRowUnionActivation_bound (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (δ : ℝ) (hδ : 0 < δ)
    (w : (j : J) → E j → ℝ) (hw : ∀ j e, |w j e| ≤ B j / δ) (e : Sigma E) :
    |highRowUnionActivation B w e| ≤ highRowTotalMass B / δ := by
  have hα := highRowSelectionProbability_pos hB hTotal e.1
  unfold highRowUnionActivation
  rw [abs_div, abs_of_pos hα]
  apply (div_le_iff₀ hα).mpr
  have he : highRowTotalMass B / δ * highRowSelectionProbability B e.1 = B e.1 / δ := by
    unfold highRowSelectionProbability
    field_simp
  rw [he]
  exact hw e.1 e.2

/-- The signed action of all row tags is exactly the sum of their genuine
row actions; the mixture weights cancel and no signed action premise is used. -/
theorem highRowUnionActivation_action (π : (j : J) → Measure (E j))
    {B : J → ℝ} (hB : ∀ j, 0 < B j) (hTotal : 0 < highRowTotalMass B)
    {w : (j : J) → E j → ℝ} (hw : ∀ j, Measurable (w j))
    {F : Sigma E → ℝ} (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => w j e * F ⟨j, e⟩) (π j)) :
    (∫ e, highRowUnionActivation B w e * F e ∂highRowReferenceUnion π B) =
      ∑ j, ∫ e, w j e * F ⟨j, e⟩ ∂π j := by
  have he (j : J) : (fun e : E j => highRowUnionActivation B w ⟨j,e⟩ * F ⟨j,e⟩) =
      (fun e => (w j e * F ⟨j,e⟩) / highRowSelectionProbability B j) := by
    funext e
    unfold highRowUnionActivation
    ring
  rw [highRowReferenceUnion_integral π B (fun j => (hB j).le)
    (F := (fun e => highRowUnionActivation B w e * F e))
    ((highRowUnionActivation_measurable B hw).mul hF)
    (fun j => by rw [he j]; exact (hInt j).div_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [he j, integral_div]
  exact mul_div_cancel₀ _ (highRowSelectionProbability_pos hB hTotal j).ne'

include hB in
theorem highRowReferenceUnion_integral_common_mean (hTotal : 0 < highRowTotalMass B)
    {F : (j : J) → E j → ℝ} (hF : ∀ j, Measurable (F j))
    (hInt : ∀ j, Integrable (F j) (π j)) {m : ℝ}
    (hMean : ∀ j, (∫ e, F j e ∂π j) = m) :
    (∫ e : Sigma E, F e.1 e.2 ∂highRowReferenceUnion π B) = m := by
  rw [highRowReferenceUnion_integral π B hB (sigma_uncurry_measurable hF) hInt]
  simp [hMean]
  rw [← Finset.sum_mul, highRowSelectionProbability_sum hTotal.ne', one_mul]

end
end NearlyMinimax
