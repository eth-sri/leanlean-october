module

public import NearlyMinimax.ActualSeparatedPacket
public import NearlyMinimax.HistoryPriorDensity

@[expose] public section

/-! Actual absolute reference laws and bounded centered activation marks for
the high-smoothness signed packets. This concerns the mark law; density-reset
mean-one balancing is a separate reference-law condition. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section AbsoluteMark
variable {E : Type*} [MeasurableSpace E]

section
variable (μ : Measure E) (w : E → ℝ)

def signedMarkMass : ℝ := ∫ e, |w e| ∂μ

def absoluteMarkLaw : Measure E :=
  μ.withDensity (fun e => ENNReal.ofReal (|w e| / signedMarkMass μ w))

def absoluteActivation (e : E) : ℝ :=
  signedMarkMass μ w * (w e / |w e|)

theorem signedMarkMass_nonneg :
    0 ≤ signedMarkMass μ w := integral_nonneg (fun _ => abs_nonneg _)

end

variable {μ : Measure E} {w : E → ℝ} (hw : Integrable w μ) (hmw : Measurable w)
    (hpos : 0 < signedMarkMass μ w)

include hw in
theorem signedMarkMass_eq_variation :
    signedMarkMass μ w = ((μ.withDensityᵥ w).variation univ).toReal := by
  rw [Measure.variation_withDensityᵥ hw, withDensity_apply _ MeasurableSet.univ]
  simp
  rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable]
  simp [signedMarkMass]

include hw hpos in
theorem absoluteMarkLaw_probability :
    IsProbabilityMeasure (absoluteMarkLaw μ w) := by
  constructor
  rw [absoluteMarkLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hw.abs.div_const _)
      (Filter.Eventually.of_forall (fun e => div_nonneg (abs_nonneg (w e)) hpos.le)),
    integral_div]
  change ENNReal.ofReal (signedMarkMass μ w / signedMarkMass μ w) = 1
  simp [div_self hpos.ne', ENNReal.ofReal_one]

theorem absoluteActivation_measurable (μ : Measure E) {w : E → ℝ} (hw : Measurable w) :
    Measurable (absoluteActivation μ w) :=
  (hw.div hw.abs).const_mul _

theorem absoluteActivation_bound (μ : Measure E) (w : E → ℝ) (e : E) :
    |absoluteActivation μ w e| ≤ signedMarkMass μ w := by
  rw [absoluteActivation, abs_mul, abs_of_nonneg (signedMarkMass_nonneg μ w)]
  have hb : |w e / (|w e|)| ≤ 1 := by
    by_cases he : w e = 0
    · simp [he]
    · rw [abs_div, abs_abs, div_self (abs_ne_zero.mpr he)]
  exact (mul_le_mul_of_nonneg_left hb (signedMarkMass_nonneg μ w)).trans_eq (mul_one _)

include hmw hpos in
theorem absoluteMarkLaw_activation_integral (F : E → ℝ) :
    (∫ e, absoluteActivation μ w e * F e ∂absoluteMarkLaw μ w) =
      ∫ e, w e * F e ∂μ := by
  rw [absoluteMarkLaw, integral_withDensity_eq_integral_toReal_smul
    (hmw.abs.div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro e
  dsimp only
  rw [ENNReal.toReal_ofReal (div_nonneg (abs_nonneg (w e)) hpos.le), smul_eq_mul,
    absoluteActivation]
  by_cases he : w e = 0
  · simp [he]
  · field_simp

include hw hmw hpos in
theorem absoluteMarkLaw_signed_action
    {F : E → ℝ} (hF : Measurable F) {M : ℝ} (hbound : ∀ e, ‖F e‖ ≤ M) :
    (∫ e, absoluteActivation μ w e * F e ∂absoluteMarkLaw μ w) =
      ∫ᵛ e, F e ∂<•(μ.withDensityᵥ w) := by
  rw [absoluteMarkLaw_activation_integral hmw hpos F,
    signedDensity_integral μ hw hmw hF M hbound]

end AbsoluteMark

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

section
variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {σ : Measure Z} [IsFiniteMeasure σ] (w : I → ℝ) (q : ℕ) (C : ℝ) {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
include hA hcost

theorem tensorActivation_density_zero (hpos : 0 < signedMarkMass (σ.prod Measure.count) (responseTensorWeight w q C A))
    {F : Z × I → ℝ} (hF : Measurable F) {K : ℝ} (hb : ∀ e, ‖F e‖ ≤ K) :
    (∫ e, absoluteActivation (σ.prod Measure.count) (responseTensorWeight w q C A) e * F (e.1,e.2.1)
      ∂absoluteMarkLaw (σ.prod Measure.count) (responseTensorWeight w q C A)) = 0 := by
  have hm : Measurable (fun e : Z × (I × HighResponseMarkIndex ι q) => F (e.1,e.2.1)) := by fun_prop
  have hi := (tensorWeight_integrable w q C hA hcost).mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => hb (e.1,e.2.1)))
  have hz (ζ : Z) : (∑ h : HighResponseMarkIndex ι q, highResponseMarkWeight C (A ζ) h) = 0 := by
    simpa only [mul_one, responseMatrixAction_zero_mass] using highResponseMark_action q C (A ζ) (fun _ => 0) (fun _ => 1)
  rw [absoluteMarkLaw_activation_integral (tensorWeight_measurable w q C hA) hpos, integral_prod _ hi]
  simp only [integral_count, Fintype.sum_prod_type (f := fun h : I × HighResponseMarkIndex ι q => _), responseTensorWeight]
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hz, zero_mul, mul_zero, Finset.sum_const_zero, integral_zero]

end

section
variable (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)

def highPacketMarkMass : ℝ :=
  signedMarkMass (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

def highPacketAbsoluteLaw : Measure (Z × HighPacketMarkIndex ι m r D q) :=
  absoluteMarkLaw (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

def highPacketActivation : Z × HighPacketMarkIndex ι m r D q → ℝ :=
  absoluteActivation (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

end

section
variable {σ : Measure Z} [IsFiniteMeasure σ] (a b : ℝ) (m r D q : ℕ) (C : ℝ) {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
include hA hcost

theorem highPacketMarkMass_eq_variation :
    highPacketMarkMass σ a b m r D q C A =
      ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal :=
  signedMarkMass_eq_variation (tensorWeight_integrable (densityPacketWeight a b m r D) q C hA hcost)

end

section
variable {σ : Measure Z} [IsFiniteMeasure σ] {a b : ℝ} {m r D q : ℕ} {C : ℝ} {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
include hA hcost hpos

theorem highPacketAbsoluteLaw_probability :
    IsProbabilityMeasure (highPacketAbsoluteLaw σ a b m r D q C A) :=
  absoluteMarkLaw_probability (tensorWeight_integrable (densityPacketWeight a b m r D) q C hA hcost) hpos

theorem highPacketActivation_centered :
    (∫ e, highPacketActivation σ a b m r D q C A e
      ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 := by
  have h := tensorActivation_density_zero (densityPacketWeight a b m r D) q C hA hcost hpos
    (F := fun _ => 1) measurable_const (fun _ => le_rfl)
  simp at h
  exact h

end

end Packet
end NearlyMinimax
