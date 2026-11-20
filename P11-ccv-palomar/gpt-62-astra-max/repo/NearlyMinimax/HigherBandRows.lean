module

public import NearlyMinimax.CardinalFactorJoint
public import NearlyMinimax.HighUnionReset
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

section
variable (d r D : ℕ) (lam L : ℝ) {T : ℝ}

def HigherBandCarrier : Bool → Type
  | false => CardinalSeparatedMark d r
  | true => CardinalBandMark d r

instance higherBandCarrier_measurable (fine : Bool) :
    MeasurableSpace (HigherBandCarrier d r fine) := by
  cases fine <;> dsimp [HigherBandCarrier] <;> infer_instance

instance higherBandCarrier_standardBorel (fine : Bool) :
    StandardBorelSpace (HigherBandCarrier d r fine) := by
  cases fine
  · exact cardinal_separated_mark_standardBorel d r
  · exact cardinal_band_mark_standardBorel d r

def higherBandCarrierMeasure (T : ℝ) :
    (fine : Bool) → Measure (HigherBandCarrier d r fine)
  | false => cardinalSeparatedMeasure d r T
  | true => cardinalBandMeasure d r L T

def higherBandCarrierAmplitude :
    (fine : Bool) → HigherBandCarrier d r fine → HighFrameIndex d D → HighFrameVector d D
  | false => cardinalSeparatedAmplitude lam
  | true => cardinalBandAmplitude lam

def higherBandCarrierFactor {d r : ℕ} (lam : ℝ) :
    (fine : Bool) → HigherBandCarrier d r fine → Fin r → Covariate d → ℝ
  | false => cardinalSeparatedFactor lam
  | true => cardinalBandFactor lam

theorem higherBandCarrierMeasure_finite (hT : 1 ≤ T) (fine : Bool) :
    IsFiniteMeasure (higherBandCarrierMeasure d r L T fine) := by
  cases fine
  · exact cardinal_separated_measure_finite d r hT
  · exact cardinal_band_measure_finite d r L hT

theorem higherBandCarrierAmplitude_measurable (fine : Bool)
    (i j : HighFrameIndex d D) : Measurable (fun ζ => higherBandCarrierAmplitude d r D lam fine ζ i j) := by
  cases fine
  · exact cardinal_separated_amplitude_measurable ..
  · exact cardinal_band_amplitude_measurable ..

theorem higherBandCarrierAmplitude_cost_integrable (hT : 1 ≤ T)
    (fine : Bool) : Integrable (separatedMatrixCost (higherBandCarrierAmplitude d r D lam fine))
      (higherBandCarrierMeasure d r L T fine) := by
  cases fine
  · exact cardinal_separated_cost_integrable lam hT
  · exact cardinal_band_cost_integrable lam L hT

end

variable (d k r m D q : ℕ) (a b C lam L T : ℝ) (hT : 1 ≤ T) (fine : Bool)

theorem higherBandCarrierFactor_joint_measurable (l : Fin r) :
    Measurable (fun ζx : HigherBandCarrier d r fine × Covariate d =>
      higherBandCarrierFactor lam fine ζx.1 l ζx.2) := by
  cases fine
  · exact cardinal_separated_factor_joint_measurable lam l
  · exact cardinal_band_factor_joint_measurable lam l

theorem higherBandCarrierFactor_bound {d r : ℕ} (lam : ℝ) {fine : Bool}
    (ζ : HigherBandCarrier d r fine) (l : Fin r) {x : Covariate d} (hx : ∀ i, |x i| ≤ 2) :
    |higherBandCarrierFactor lam fine ζ l x| ≤ 1 := by
  cases fine
  · exact cardinal_separated_factor_abs_le_one lam ζ l hx
  · exact by apply cardinal_separated_factor_abs_le_one <;> assumption

abbrev HigherBandRowMark :=
  HigherBandCarrier d r fine × HighPacketMarkIndex (HighFrameIndex d D) m r D q

def higherBandSignedRow :
    SignedMeasure (HigherBandRowMark d r m D q fine) :=
  highPacketSignedMeasure (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)

def higherBandRowMass : ℝ :=
  highPacketMarkMass (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)

def higherBandRowLaw :
    Measure (HigherBandRowMark d r m D q fine) :=
  highPacketAbsoluteLaw (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)

def higherBandRowActivation :
    HigherBandRowMark d r m D q fine → ℝ :=
  highPacketActivation (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)

def higherBandRowData :
    HighUnionRowData d k D Unit (fun _ => HigherBandRowMark d r m D q fine) where
  rowLaw := fun _ => higherBandRowLaw d r m D q a b C lam L T fine
  rowMass := fun _ => higherBandRowMass d r m D q a b C lam L T fine
  rowActivation := fun _ => higherBandRowActivation d r m D q a b C lam L T fine
  rowIntercept := fun _ => highPacketIntercept a b m r D q
  rowSlope := fun j _ e x => highPacketSlope a b
    (fun ζ l => higherBandCarrierFactor lam fine ζ l (highLocalCoordinates j x)) e
  rowVector := fun _ e => (highResponseMarkAtom C e.2.2).2
  rowTime := fun _ e => (highResponseMarkAtom 0 e.2.2).1

include hT in
theorem higherBandRowMass_eq_variation : higherBandRowMass d r m D q a b C lam L T fine =
      ((higherBandSignedRow d r m D q a b C lam L T fine).variation univ).toReal := by
  letI := higherBandCarrierMeasure_finite d r L hT fine
  solve_by_elim [highPacketMarkMass_eq_variation, higherBandCarrierAmplitude_measurable, higherBandCarrierAmplitude_cost_integrable]

theorem higherBandRowMass_nonneg :
    0 ≤ higherBandRowMass d r m D q a b C lam L T fine := signedMarkMass_nonneg _ _

end NearlyMinimax
