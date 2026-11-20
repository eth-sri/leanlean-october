module

public import NearlyMinimax.CardinalFactorJoint
public import NearlyMinimax.PacketRowData
public import NearlyMinimax.HighLocalFrame

@[expose] public section

/-! Actual ordinary target-r rows from the positive separated cardinal
and cardinal-band measures, with their real finite density/response atoms. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def HigherBandCarrier (d r : ℕ) : Bool → Type
  | false => CardinalSeparatedMark d r
  | true => CardinalBandMark d r

instance higherBandCarrier_measurable (d r : ℕ) (fine : Bool) :
    MeasurableSpace (HigherBandCarrier d r fine) := by
  cases fine <;> dsimp [HigherBandCarrier] <;> infer_instance

instance higherBandCarrier_standardBorel (d r : ℕ) (fine : Bool) :
    StandardBorelSpace (HigherBandCarrier d r fine) := by
  cases fine
  · exact cardinal_separated_mark_standardBorel d r
  · exact cardinal_band_mark_standardBorel d r

def higherBandCarrierMeasure (d r : ℕ) (L T : ℝ) :
    (fine : Bool) → Measure (HigherBandCarrier d r fine)
  | false => cardinalSeparatedMeasure d r T
  | true => cardinalBandMeasure d r L T

def higherBandCarrierAmplitude (d r D : ℕ) (lam : ℝ) :
    (fine : Bool) → HigherBandCarrier d r fine → HighFrameIndex d D → HighFrameIndex d D → ℝ
  | false => cardinalSeparatedAmplitude lam
  | true => cardinalBandAmplitude lam

def higherBandCarrierFactor (d r : ℕ) (lam : ℝ) :
    (fine : Bool) → HigherBandCarrier d r fine → Fin r → Covariate d → ℝ
  | false => cardinalSeparatedFactor lam
  | true => cardinalBandFactor lam

theorem higherBandCarrierMeasure_finite (d r : ℕ) (L T : ℝ) (hT : 1 ≤ T) (fine : Bool) :
    IsFiniteMeasure (higherBandCarrierMeasure d r L T fine) := by
  cases fine
  · exact cardinal_separated_measure_finite d r hT
  · exact cardinal_band_measure_finite d r L hT

section
variable (d r D : ℕ)

theorem higherBandCarrierAmplitude_measurable (lam : ℝ) (fine : Bool)
    (i j : HighFrameIndex d D) : Measurable (fun ζ => higherBandCarrierAmplitude d r D lam fine ζ i j) := by
  cases fine
  · exact cardinal_separated_amplitude_measurable lam i j
  · exact cardinal_band_amplitude_measurable lam i j

theorem higherBandCarrierAmplitude_cost_integrable (lam L T : ℝ) (hT : 1 ≤ T)
    (fine : Bool) : Integrable (separatedMatrixCost (higherBandCarrierAmplitude d r D lam fine))
      (higherBandCarrierMeasure d r L T fine) := by
  cases fine
  · exact cardinal_separated_cost_integrable lam hT
  · exact cardinal_band_cost_integrable lam L hT

theorem higherBandCarrierAmplitude_integrable (d r D : ℕ) (lam L T : ℝ)
    (hT : 1 ≤ T) (fine : Bool) : SeparatedMatrixIntegrable (higherBandCarrierMeasure d r L T fine)
      (higherBandCarrierAmplitude d r D lam fine) :=
  ⟨higherBandCarrierAmplitude_measurable d r D lam fine,
    higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine⟩

end

section
variable (d r : ℕ) (lam : ℝ) (fine : Bool)

theorem higherBandCarrierFactor_joint_measurable (l : Fin r) :
    Measurable (fun ζx : HigherBandCarrier d r fine × Covariate d =>
      higherBandCarrierFactor d r lam fine ζx.1 l ζx.2) := by
  cases fine
  · exact cardinal_separated_factor_joint_measurable lam l
  · exact cardinal_band_factor_joint_measurable lam l

theorem higherBandCarrierFactor_bound
    (ζ : HigherBandCarrier d r fine) (l : Fin r) (x : Covariate d) (hx : ∀ i, |x i| ≤ 2) :
    |higherBandCarrierFactor d r lam fine ζ l x| ≤ 1 := by
  cases fine
  · apply cardinal_separated_factor_abs_le_one <;> assumption
  · apply cardinal_band_factor_abs_le_one <;> assumption

end

abbrev HigherBandRowMark (d r m D q : ℕ) (fine : Bool) :=
  HigherBandCarrier d r fine × HighPacketMarkIndex (HighFrameIndex d D) m r D q

def higherBandSignedRow (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) :
    SignedMeasure (HigherBandRowMark d r m D q fine) :=
  highPacketSignedMeasure (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)

def higherBandRowMass (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) : ℝ :=
  highPacketMarkMass (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)

def higherBandRowData (d k r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) :
    HighUnionRowData d k D Unit (fun _ => HigherBandRowMark d r m D q fine) :=
  highPacketRowData d k m r D q a b C (higherBandCarrierMeasure d r L T fine)
    (higherBandCarrierAmplitude d r D lam fine)
    (fun j ζ x l => higherBandCarrierFactor d r lam fine ζ l (highLocalCoordinates d k j x))

section
variable (d r m D q : ℕ) (a b C lam L T : ℝ)

theorem higherBandRowMass_eq_variation
    (hT : 1 ≤ T) (fine : Bool) : higherBandRowMass d r m D q a b C lam L T fine =
      ((higherBandSignedRow d r m D q a b C lam L T fine).variation univ).toReal := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  exact highPacketMarkMass_eq_variation _ a b m r D q C _
    (higherBandCarrierAmplitude_integrable d r D lam L T hT fine)

theorem higherBandRowMass_nonneg (fine : Bool) :
    0 ≤ higherBandRowMass d r m D q a b C lam L T fine := signedMarkMass_nonneg _ _

end

end NearlyMinimax
