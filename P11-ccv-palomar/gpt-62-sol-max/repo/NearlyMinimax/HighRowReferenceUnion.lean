module

public import NearlyMinimax.HighPacketBalancing
public import NearlyMinimax.FiniteSigmaProbability

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

theorem rowSigmaFunction_measurable (F : (j : J) → E j → ℝ)
    (hF : ∀ j, Measurable (F j)) : Measurable (fun e : Sigma E => F e.1 e.2) :=
  measurable_sigma_of_fibers _ hF


def highRowTotalMass (B : J → ℝ) : ℝ := ∑ j, B j

def highRowSelectionProbability (B : J → ℝ) (j : J) : ℝ := B j / highRowTotalMass B

section
variable (B : J → ℝ)

theorem highRowSelectionProbability_nonneg (hB : ∀ j, 0 ≤ B j) (j : J) :
    0 ≤ highRowSelectionProbability B j :=
  div_nonneg (hB j) (Finset.sum_nonneg (fun j _ => hB j))

theorem highRowSelectionProbability_pos (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (j : J) : 0 < highRowSelectionProbability B j :=
  by solve_by_elim [div_pos]

theorem highRowSelectionProbability_sum (hTotal : highRowTotalMass B ≠ 0) :
    (∑ j, highRowSelectionProbability B j) = 1 := by
  unfold highRowSelectionProbability
  rw [← Finset.sum_div]
  exact div_self hTotal

end

/-- The actual positive reference law on the finite tagged mark union. -/
def highRowReferenceUnion (π : (j : J) → Measure (E j)) (B : J → ℝ) : Measure (Sigma E) :=
  ∑ j, (ENNReal.ofReal (highRowSelectionProbability B j) • π j).map (Sigma.mk j)

section
variable (π : (j : J) → Measure (E j))

theorem highRowReferenceUnion_probability
    [∀ j, IsProbabilityMeasure (π j)] (B : J → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hTotal : 0 < highRowTotalMass B) : IsProbabilityMeasure (highRowReferenceUnion π B) := by
  constructor
  rw [highRowReferenceUnion, Measure.finsetSum_apply]
  simp_rw [Measure.map_smul _ (measurable_sigma_mk_actual _).aemeasurable]
  simp_all [← ENNReal.ofReal_sum_of_nonneg (fun j _ => highRowSelectionProbability_nonneg B hB j), highRowSelectionProbability_sum B hTotal.ne']

section
variable (B : J → ℝ)

private theorem highRowReferenceUnion_moments (B : J → ℝ)
    (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => F ⟨j, e⟩) (π j)) :
    Integrable F (highRowReferenceUnion π B) ∧
    (∫ e, F e ∂highRowReferenceUnion π B) =
      ∑ j, ∫ e, F ⟨j, e⟩ ∂(ENNReal.ofReal (highRowSelectionProbability B j) • π j) :=
  finite_map_mixture_moments Sigma.mk measurable_sigma_mk_actual
    (fun j => ENNReal.ofReal (highRowSelectionProbability B j) • π j) hF
    (fun j => (hInt j).smul_measure ENNReal.ofReal_ne_top)

theorem highRowReferenceUnion_integrable
    (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => F ⟨j, e⟩) (π j)) :
    Integrable F (highRowReferenceUnion π B) := (highRowReferenceUnion_moments π B F hF hInt).1

theorem highRowReferenceUnion_integral
    (hB : ∀ j, 0 ≤ B j) (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => F ⟨j, e⟩) (π j)) :
    (∫ e, F e ∂highRowReferenceUnion π B) =
      ∑ j, highRowSelectionProbability B j * ∫ e, F ⟨j, e⟩ ∂π j := by
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal (highRowSelectionProbability_nonneg B hB _),
    smul_eq_mul] using (highRowReferenceUnion_moments π B F hF hInt).2

end

end

def highRowUnionActivation (B : J → ℝ) (w : (j : J) → E j → ℝ) (e : Sigma E) : ℝ :=
  w e.1 e.2 / highRowSelectionProbability B e.1

theorem highRowUnionActivation_measurable (B : J → ℝ) (w : (j : J) → E j → ℝ)
    (hw : ∀ j, Measurable (w j)) : Measurable (highRowUnionActivation B w) :=
  rowSigmaFunction_measurable _ (fun j => (hw j).div_const _)

section
variable (π : (j : J) → Measure (E j))
    (B : J → ℝ)

theorem highRowUnionActivation_integrable (w : (j : J) → E j → ℝ) (hw : ∀ j, Measurable (w j))
    (hInt : ∀ j, Integrable (w j) (π j)) :
    Integrable (highRowUnionActivation B w) (highRowReferenceUnion π B) :=
  highRowReferenceUnion_integrable π B _ (highRowUnionActivation_measurable B w hw)
    (fun j => by simpa only [highRowUnionActivation] using
      (hInt j).div_const (highRowSelectionProbability B j))

/-- Every row is genuinely centered; hence so is the combined activation. -/
theorem highRowUnionActivation_centered (hB : ∀ j, 0 ≤ B j) (w : (j : J) → E j → ℝ)
    (hw : ∀ j, Measurable (w j)) (hInt : ∀ j, Integrable (w j) (π j))
    (hCenter : ∀ j, (∫ e, w j e ∂π j) = 0) :
    (∫ e, highRowUnionActivation B w e ∂highRowReferenceUnion π B) = 0 := by
  rw [highRowReferenceUnion_integral π B hB _ (highRowUnionActivation_measurable B w hw)
    (fun j => by simpa only [highRowUnionActivation] using
      (hInt j).div_const (highRowSelectionProbability B j))]
  simp only [highRowUnionActivation, integral_div, hCenter, zero_div, mul_zero, Finset.sum_const_zero]

end

/-- The exact source activation budget is retained by the finite mixture. -/
theorem highRowUnionActivation_bound (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (δ : ℝ) (hδ : 0 < δ)
    (w : (j : J) → E j → ℝ) (hw : ∀ j e, |w j e| ≤ B j / δ) (e : Sigma E) :
    |highRowUnionActivation B w e| ≤ highRowTotalMass B / δ := by
  have hα := highRowSelectionProbability_pos B hB hTotal e.1
  unfold highRowUnionActivation
  rw [abs_div, abs_of_pos hα]
  apply (div_le_iff₀ hα).mpr
  have he : highRowTotalMass B / δ * highRowSelectionProbability B e.1 = B e.1 / δ := by
    unfold highRowSelectionProbability
    field_simp
  grind

section
variable (π : (j : J) → Measure (E j))
    (B : J → ℝ)

/-- The signed action of all row tags is exactly the sum of their genuine
row actions; the mixture weights cancel and no signed action premise is used. -/
theorem highRowUnionActivation_action (hB : ∀ j, 0 < B j) (hTotal : 0 < highRowTotalMass B)
    (w : (j : J) → E j → ℝ) (hw : ∀ j, Measurable (w j))
    (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => w j e * F ⟨j, e⟩) (π j)) :
    (∫ e, highRowUnionActivation B w e * F e ∂highRowReferenceUnion π B) =
      ∑ j, ∫ e, w j e * F ⟨j, e⟩ ∂π j := by
  have he (j : J) : (fun e : E j => highRowUnionActivation B w ⟨j,e⟩ * F ⟨j,e⟩) =
      (fun e => (w j e * F ⟨j,e⟩) / highRowSelectionProbability B j) := by
    funext e
    unfold highRowUnionActivation
    ring
  rw [highRowReferenceUnion_integral π B (fun j => (hB j).le)
    (fun e => highRowUnionActivation B w e * F e)
    ((highRowUnionActivation_measurable B w hw).mul hF)
    (fun j => by simp [he j] <;> fun_prop)]
  apply Finset.sum_congr rfl
  intro j _
  rw [he j, integral_div]
  exact mul_div_cancel₀ _ (highRowSelectionProbability_pos B hB hTotal j).ne'

theorem highRowReferenceUnion_integral_common_mean (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B)
    (F : (j : J) → E j → ℝ) (hF : ∀ j, Measurable (F j))
    (hInt : ∀ j, Integrable (F j) (π j)) (m : ℝ)
    (hMean : ∀ j, (∫ e, F j e ∂π j) = m) :
    (∫ e : Sigma E, F e.1 e.2 ∂highRowReferenceUnion π B) = m := by
  simp_all [highRowReferenceUnion_integral π B hB _ (rowSigmaFunction_measurable F hF) hInt, ← Finset.sum_mul, highRowSelectionProbability_sum B hTotal.ne', one_mul]

end

end
end NearlyMinimax
