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
include μ w

def signedMarkMass   := ∫ e, |w e| ∂μ

def absoluteMarkLaw   :=
  μ.withDensity (fun e => ENNReal.ofReal (|w e| / signedMarkMass μ w))

def absoluteActivation  (e : E)  :=
  signedMarkMass μ w * (w e / |w e|)

theorem signedMarkMass_nonneg  :
    0 ≤ signedMarkMass μ w := integral_nonneg (fun _ => abs_nonneg _)

section
variable (hw : Integrable w μ)
include hw

theorem signedMarkMass_eq_variation   :
    signedMarkMass μ w = ((μ.withDensityᵥ w).variation univ).toReal := by
  rw [Measure.variation_withDensityᵥ hw, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable]
  simp only [signedMarkMass, Real.norm_eq_abs]

theorem absoluteMarkLaw_probability 
     (hpos : 0 < signedMarkMass μ w) :
    IsProbabilityMeasure (absoluteMarkLaw μ w) := by
  constructor
  rw [absoluteMarkLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hw.abs.div_const _)
      (Filter.Eventually.of_forall (fun e => div_nonneg (abs_nonneg (w e)) hpos.le)),
    integral_div]
  change ENNReal.ofReal (signedMarkMass μ w / signedMarkMass μ w) = 1
  measurability
end


theorem absoluteActivation_measurable  (hw : Measurable w) :
    Measurable (absoluteActivation μ w) :=
  (hw.div hw.abs).const_mul _

theorem absoluteActivation_bound  (e : E) :
    |absoluteActivation μ w e| ≤ signedMarkMass μ w := by
  rw [absoluteActivation, abs_mul, abs_of_nonneg (signedMarkMass_nonneg μ w)]
  have hb : |w e / (|w e|)| ≤ 1 := by
    grind
  exact (mul_le_mul_of_nonneg_left hb (signedMarkMass_nonneg μ w)).trans_eq (mul_one _)

section
variable (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w)
include hmw hpos

theorem absoluteMarkLaw_activation_integral 
     (F : E → ℝ) :
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

theorem absoluteActivation_centered 
    
    (hzero : ∫ e, w e ∂μ = 0) :
    (∫ e, absoluteActivation μ w e ∂absoluteMarkLaw μ w) = 0 := by
  have h := absoluteMarkLaw_activation_integral μ w hmw hpos (fun _ => 1)
  simp only [mul_one] at h
  exact h.trans hzero
end


theorem absoluteMarkLaw_signed_action 
    (hw : Integrable w μ) (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w)
    F (hF : Measurable F) M (hbound : ∀ e, ‖F e‖ ≤ M) :
    (∫ e, absoluteActivation μ w e * F e ∂absoluteMarkLaw μ w) =
      ∫ᵛ e, F e ∂<•(μ.withDensityᵥ w) := by
  rw [absoluteMarkLaw_activation_integral μ w hmw hpos F,
    signedDensity_integral μ w hw hmw F hF M hbound]
end


end AbsoluteMark

section History
variable {E J : Type*} [MeasurableSpace E] [Fintype J] [LinearOrder J]

end History

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

section
variable (σ : Measure Z)
include σ

section
variable (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
include a b m r D q C A

def highPacketMarkMass    :=
  signedMarkMass (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

def highPacketAbsoluteLaw   : Measure (Z × HighPacketMarkIndex ι m r D q) :=
  absoluteMarkLaw (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

def highPacketActivation    :=
  absoluteActivation (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)
end


section
variable [IsFiniteMeasure σ] (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
include hA hcost

theorem highPacketMarkMass_eq_variation   :
    highPacketMarkMass σ a b m r D q C A =
      ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal :=
  signedMarkMass_eq_variation _ _ (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost)

theorem highPacketMarkWeight_integral_zero   :
    (∫ e, highPacketMarkWeight a b m r D q C A e ∂σ.prod Measure.count) = 0 := by
  have h := highPacketSignedMeasure_zero_mass σ a b m r D q C A hA hcost
  rw [highPacketSignedMeasure, withDensityᵥ_apply
    (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost) MeasurableSet.univ,
    Measure.restrict_univ] at h
  exact h

section
variable (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
include hpos

theorem highPacketAbsoluteLaw_probability  
     :
    IsProbabilityMeasure (highPacketAbsoluteLaw σ a b m r D q C A) :=
  absoluteMarkLaw_probability _ _ (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost) hpos

theorem highPacketActivation_centered  
     :
    (∫ e, highPacketActivation σ a b m r D q C A e
      ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 :=
  absoluteActivation_centered _ _ (highPacketMarkWeight_measurable a b m r D q C A hA)
    hpos (highPacketMarkWeight_integral_zero σ a b m r D q C A hA hcost)
end

end


theorem highPacketActivation_bound  a b m r D q C
    (A : Z → ι → ι → ℝ) e :
    |highPacketActivation σ a b m r D q C A e| ≤ highPacketMarkMass σ a b m r D q C A :=
  absoluteActivation_bound _ _ _
end


end Packet
end NearlyMinimax
