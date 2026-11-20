module

public import NearlyMinimax.ActualSeparatedPacket
public import NearlyMinimax.RealDensity
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

def signedMarkMass (μ : Measure E) (w : E → ℝ) : ℝ := ∫ e, |w e| ∂μ

def absoluteMarkLaw (μ : Measure E) (w : E → ℝ) : Measure E :=
  μ.withDensity (fun e => ENNReal.ofReal (|w e| / signedMarkMass μ w))

def absoluteActivation (μ : Measure E) (w : E → ℝ) (e : E) : ℝ :=
  signedMarkMass μ w * (w e / |w e|)

section
variable (μ : Measure E) (w : E → ℝ)

theorem signedMarkMass_nonneg :
    0 ≤ signedMarkMass μ w := integral_nonneg (fun _ => abs_nonneg _)

section
variable (hw : Integrable w μ)
include hw

theorem signedMarkMass_eq_variation :
    signedMarkMass μ w = ((μ.withDensityᵥ w).variation univ).toReal := by
  rw [Measure.variation_withDensityᵥ hw, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable] <;> rfl

theorem absoluteMarkLaw_probability (hpos : 0 < signedMarkMass μ w) :
    IsProbabilityMeasure (absoluteMarkLaw μ w) := realDensity_probability hw.abs (.of_forall fun _ => abs_nonneg _) hpos

end

theorem absoluteActivation_measurable (hw : Measurable w) :
    Measurable (absoluteActivation μ w) :=
  (hw.div hw.abs).const_mul _

theorem absoluteActivation_bound (e : E) :
    |absoluteActivation μ w e| ≤ signedMarkMass μ w := by
  rw [absoluteActivation, abs_mul, abs_of_nonneg (signedMarkMass_nonneg μ w)]
  have hb : |w e / (|w e|)| ≤ 1 := by
    grind
  exact (mul_le_mul_of_nonneg_left hb (signedMarkMass_nonneg μ w)).trans_eq (mul_one _)

section
variable (hmw : Measurable w)
include hmw

theorem absoluteMarkLaw_integral
    (hpos : 0 ≤ signedMarkMass μ w) (F : E → ℝ) :
    (∫ e, F e ∂absoluteMarkLaw μ w) = (∫ e, |w e| * F e ∂μ) / signedMarkMass μ w :=
  integral_realDensity_div hmw.abs (fun _ => abs_nonneg _) hpos F

theorem absoluteMarkLaw_activation_integral (hpos : 0 < signedMarkMass μ w) (F : E → ℝ) :
    (∫ e, absoluteActivation μ w e * F e ∂absoluteMarkLaw μ w) =
      ∫ e, w e * F e ∂μ := by
  rw [absoluteMarkLaw_integral μ w hmw hpos.le, ← integral_div]
  refine integral_congr_ae (.of_forall fun e => ?_)
  unfold absoluteActivation
  by_cases he : w e = 0
  · simp [he]
  · field_simp

theorem absoluteActivation_centered (hpos : 0 < signedMarkMass μ w)
    (hzero : ∫ e, w e ∂μ = 0) :
    (∫ e, absoluteActivation μ w e ∂absoluteMarkLaw μ w) = 0 := by
  have h := absoluteMarkLaw_activation_integral μ w hmw hpos (fun _ => 1)
  simp_all

end

theorem absoluteMarkLaw_signed_action
    (hw : Integrable w μ) (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w)
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hbound : ∀ e, ‖F e‖ ≤ M) :
    (∫ e, absoluteActivation μ w e * F e ∂absoluteMarkLaw μ w) =
      ∫ᵛ e, F e ∂<•(μ.withDensityᵥ w) := by
  rw [absoluteMarkLaw_activation_integral μ w hmw hpos F,
    signedDensity_integral μ w hw hmw F hF M hbound]

end

end AbsoluteMark

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

section
variable {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I]
    (σ : Measure Z) [IsFiniteMeasure σ] (w : I → ℝ) (q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : SeparatedMatrixIntegrable σ A)
include hA

theorem responsePacket_mass_eq :
    signedMarkMass (σ.prod Measure.count) (responsePacketWeight w q C A) =
      (∑ i, |w i|) * (∑ h : Fin (2*q+2), |responseWeight q h|) *
      (2*C^2) * ∫ ζ, separatedMatrixCost A ζ ∂σ :=
  (signedMarkMass_eq_variation _ _ (responsePacketWeight_integrable _ _ _ _ _ hA)).trans
    (responsePacket_signed_variation _ _ _ _ _ hA)

theorem responsePacket_activated_signed_action
    (hpos : 0 < signedMarkMass (σ.prod Measure.count) (responsePacketWeight w q C A))
    (F : Z × (I × HighResponseMarkIndex ι q) → ℝ) (hF : Measurable F)
    (L : ℝ) (hbound : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, absoluteActivation (σ.prod Measure.count) (responsePacketWeight w q C A) e * F e
      ∂absoluteMarkLaw (σ.prod Measure.count) (responsePacketWeight w q C A)) =
      ∫ᵛ e, F e ∂<•((σ.prod Measure.count).withDensityᵥ (responsePacketWeight w q C A)) :=
  absoluteMarkLaw_signed_action _ _ (responsePacketWeight_integrable w q C A σ hA)
    (responsePacketWeight_measurable w q C A hA.meas) hpos F hF L hbound

theorem responsePacket_absolute_density_zero
    (hpos : 0 < signedMarkMass (σ.prod Measure.count) (responsePacketWeight w q C A))
    (F : Z × I → ℝ) (hF : Measurable F) (L : ℝ) (hbound : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, absoluteActivation (σ.prod Measure.count) (responsePacketWeight w q C A) e * F (e.1,e.2.1)
      ∂absoluteMarkLaw (σ.prod Measure.count) (responsePacketWeight w q C A)) = 0 := by
  have hm : Measurable (fun e : Z × (I × HighResponseMarkIndex ι q) => F (e.1,e.2.1)) :=
    hF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hi := (responsePacketWeight_integrable w q C A σ hA).mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => hbound (e.1,e.2.1)))
  rw [absoluteMarkLaw_activation_integral _ _ (responsePacketWeight_measurable w q C A hA.meas)
    hpos, integral_prod _ hi]
  have hz (ζ : Z) := responsePacketWeight_density_sum_zero w q C A (fun i => F (ζ,i)) ζ
  simp only [integral_count, hz, integral_zero]

end

def highPacketMarkMass (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : ℝ :=
  signedMarkMass (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

def highPacketAbsoluteLaw (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Measure (Z × HighPacketMarkIndex ι m r D q) :=
  absoluteMarkLaw (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

def highPacketActivation (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Z × HighPacketMarkIndex ι m r D q → ℝ :=
  absoluteActivation (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

section
variable (σ : Measure Z)

section
variable [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : SeparatedMatrixIntegrable σ A)
include hA

theorem highPacketMarkMass_eq_variation :
    highPacketMarkMass σ a b m r D q C A =
      ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal :=
  signedMarkMass_eq_variation _ _ (highPacketMarkWeight_integrable σ a b m r D q C A hA)

theorem highPacketMarkWeight_integral_zero :
    (∫ e, highPacketMarkWeight a b m r D q C A e ∂σ.prod Measure.count) = 0 :=
  responsePacketWeight_integral_zero _ q C A σ hA

theorem highPacketAbsoluteLaw_probability
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A) :
    IsProbabilityMeasure (highPacketAbsoluteLaw σ a b m r D q C A) :=
  absoluteMarkLaw_probability _ _ (highPacketMarkWeight_integrable σ a b m r D q C A hA) hpos

theorem highPacketActivation_centered
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A) :
    (∫ e, highPacketActivation σ a b m r D q C A e
      ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 :=
  absoluteActivation_centered _ _ (highPacketMarkWeight_measurable a b m r D q C A hA.meas)
    hpos (highPacketMarkWeight_integral_zero σ a b m r D q C A hA)

end

theorem highPacketActivation_bound (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (e : Z × HighPacketMarkIndex ι m r D q) :
    |highPacketActivation σ a b m r D q C A e| ≤ highPacketMarkMass σ a b m r D q C A :=
  absoluteActivation_bound _ _ _

end

end Packet

/-- Separate the variable carrier and density indices from the common response coordinates. -/
structure MarkPacketSpace where
  Carrier : Type
  Index : Type
  [carrierMeas : MeasurableSpace Carrier]
  [indexMeas : MeasurableSpace Index]
  [indexFinite : Fintype Index]
  [indexSingleton : MeasurableSingletonClass Index]
  [carrierBorel : StandardBorelSpace Carrier]
  [indexBorel : StandardBorelSpace Index]

attribute [instance] MarkPacketSpace.carrierMeas MarkPacketSpace.indexMeas MarkPacketSpace.indexFinite
  MarkPacketSpace.indexSingleton MarkPacketSpace.carrierBorel MarkPacketSpace.indexBorel

namespace MarkPacketSpace

def of (Z I : Type) [MeasurableSpace Z] [MeasurableSpace I] [Fintype I]
    [MeasurableSingletonClass I] [StandardBorelSpace Z] [StandardBorelSpace I] : MarkPacketSpace where
  Carrier := Z
  Index := I

variable (S : MarkPacketSpace)

abbrev Mark (ι : Type) (q : ℕ) := S.Carrier × (S.Index × HighResponseMarkIndex ι q)
abbrev DensityMark := S.Carrier × S.Index

def density {ι : Type} {q : ℕ} (e : S.Mark ι q) : S.DensityMark := (e.1,e.2.1)

def withResponse {ι : Type} {q : ℕ} (r : HighResponseMarkIndex ι q)
    (e : S.DensityMark) : S.Mark ι q := (e.1,(e.2,r))

theorem withResponse_measurable {ι : Type} [MeasurableSpace ι] {q : ℕ}
    (r : HighResponseMarkIndex ι q) : Measurable (S.withResponse r) :=
  measurable_fst.prodMk (measurable_snd.prodMk measurable_const)

end MarkPacketSpace

structure MarkPacketData (S : MarkPacketSpace) (ι : Type) where
  carrier : Measure S.Carrier
  weights : S.Index → ℝ
  amplitude : S.Carrier → ι → ι → ℝ

namespace MarkPacketData
section
variable {S : MarkPacketSpace} {ι : Type} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (P : MarkPacketData S ι) (q : ℕ) (C : ℝ)

abbrev base : Measure (S.Mark ι q) := P.carrier.prod Measure.count
abbrev weight : S.Mark ι q → ℝ := responsePacketWeight P.weights q C P.amplitude
abbrev mass : ℝ := signedMarkMass (P.base q) (P.weight q C)
abbrev law : Measure (S.Mark ι q) := absoluteMarkLaw (P.base q) (P.weight q C)
abbrev activation : S.Mark ι q → ℝ := absoluteActivation (P.base q) (P.weight q C)
abbrev signed : SignedMeasure (S.Mark ι q) := (P.base q).withDensityᵥ (P.weight q C)

end
end MarkPacketData
end NearlyMinimax
