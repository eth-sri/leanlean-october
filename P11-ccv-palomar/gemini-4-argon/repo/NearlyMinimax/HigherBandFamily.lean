module
public import NearlyMinimax.CardinalSeparatedBand
public import NearlyMinimax.HighUnionReset
public import NearlyMinimax.HighLocalFrame
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {d n : ℕ}
theorem gaussianPrimitiveLeft_continuous  (lam t : ℝ) (e : GaussianPrimitiveMark d) :
    Continuous (gaussianPrimitiveLeft lam t e) := by
  unfold gaussianPrimitiveLeft gaussianTrig
  split_ifs <;> unfold gaussianPhase <;> fun_prop
theorem gaussianPrimitiveRight_continuous  (lam t : ℝ) (e : GaussianPrimitiveMark d) :
    Continuous (gaussianPrimitiveRight lam t e) := by
  unfold gaussianPrimitiveRight gaussianTrig gaussianAffineFactor
  split_ifs <;> unfold gaussianPhase <;> fun_prop
theorem cardinal_separated_factor_continuous  (lam : ℝ)
    (z : CardinalSeparatedMark d n) (l : Fin n) : Continuous (cardinalSeparatedFactor lam z l) :=
  have h_centered_cardinal_factor_continuous {d} (i : Fin n) (z : CenteredCardinalMark d n i) : Continuous (centeredCardinalFactor i lam z l) := by
    unfold centeredCardinalFactor
    split_ifs
    · exact gaussianPrimitiveRight_continuous _ _ _
    · exact continuous_finset_prod _ (fun _ _ => gaussianPrimitiveLeft_continuous _ _ _)
  (h_centered_cardinal_factor_continuous z.1 z.2)
theorem cardinal_band_factor_continuous  (lam : ℝ)
    (z : CardinalBandMark d n) (l : Fin n) : Continuous (cardinalBandFactor lam z l) :=
  cardinal_separated_factor_continuous lam z.2 l
theorem cardinal_separated_factor_joint_measurable  (lam l) :
    Measurable (fun zx : CardinalSeparatedMark d n × Covariate d =>
      cardinalSeparatedFactor lam zx.1 l zx.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Covariate d) (z : CardinalSeparatedMark d n) => cardinalSeparatedFactor lam z l x)
    (fun z => cardinal_separated_factor_continuous lam z l)
    (fun x => cardinal_separated_factor_measurable lam l x)
  exact h.comp measurable_swap
theorem cardinal_band_factor_joint_measurable  (lam l) :
    Measurable (fun zx : CardinalBandMark d n × Covariate d =>
      cardinalBandFactor lam zx.1 l zx.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Covariate d) (z : CardinalBandMark d n) => cardinalBandFactor lam z l x)
    (fun z => cardinal_band_factor_continuous lam z l)
    (fun x => cardinal_band_factor_measurable lam l x)
  exact h.comp measurable_swap
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
theorem higherBandCarrierMeasure_finite (d r L T) (hT : 1 ≤ T) (fine ) :
    IsFiniteMeasure (higherBandCarrierMeasure d r L T fine) := by
  cases fine
  · exact cardinal_separated_measure_finite d r hT
  have h_cardinal_band_measure_finite : IsFiniteMeasure (cardinalBandMeasure d r L T) := by
    letI := cardinal_separated_measure_finite d r hT
    letI := cardinal_separated_measure_finite d r (le_max_left 1 L)
    unfold cardinalBandMeasure
    infer_instance
  · exact h_cardinal_band_measure_finite
theorem higherBandCarrierAmplitude_measurable (d r D lam fine i j) : Measurable (fun ζ => higherBandCarrierAmplitude d r D lam fine ζ i j) := by
  cases fine
  · exact cardinal_separated_amplitude_measurable lam i j
  · exact cardinal_band_amplitude_measurable lam i j
theorem higherBandCarrierAmplitude_cost_integrable (d r D lam L T) (hT : 1 ≤ T)
    (fine ) : Integrable (separatedMatrixCost (higherBandCarrierAmplitude d r D lam fine))
      (higherBandCarrierMeasure d r L T fine) := by
  cases fine
  · exact cardinal_separated_cost_integrable lam hT
  have h_cardinal_band_cost_integrable {n : ℕ} : Integrable (separatedMatrixCost (cardinalBandAmplitude (D := D) lam)) (cardinalBandMeasure d n L T) := by
    have hm : Measurable (separatedMatrixCost (cardinalBandAmplitude (d := d) (n := n) (D := D) lam)) :=
      Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
        (fun β' _ => (cardinal_band_amplitude_measurable lam β β').abs))
    apply cardinal_band_integrable_of_copies L T _ hm
    · simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable (D := D) lam hT
    · simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable (D := D) lam (le_max_left 1 L)
  · exact h_cardinal_band_cost_integrable
theorem higherBandCarrierFactor_joint_measurable (d r lam fine l) :
    Measurable (fun ζx : HigherBandCarrier d r fine × Covariate d =>
      higherBandCarrierFactor d r lam fine ζx.1 l ζx.2) := by
  cases fine
  · exact cardinal_separated_factor_joint_measurable lam l
  · exact cardinal_band_factor_joint_measurable lam l
theorem higherBandCarrierFactor_bound (d r lam fine ζ l x) (hx : ∀ i, |x i| ≤ 2) :
    |higherBandCarrierFactor d r lam fine ζ l x| ≤ 1 := by
  cases fine
  · exact cardinal_separated_factor_abs_le_one lam ζ l x hx
  · exact cardinal_separated_factor_abs_le_one lam ζ.2 l x hx
abbrev HigherBandRowMark (d r m D q : ℕ) (fine : Bool) :=
  HigherBandCarrier d r fine × HighPacketMarkIndex (HighFrameIndex d D) m r D q
def higherBandSignedRow (d r m D q ) (a b C lam L T : ℝ) (fine ) :
    SignedMeasure (HigherBandRowMark d r m D q fine) :=
  highPacketSignedMeasure (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)
def higherBandRowMass (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) : ℝ :=
  highPacketMarkMass (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)
def higherBandRowActivation (d r m D q ) (a b C lam L T : ℝ) (fine ) :
    HigherBandRowMark d r m D q fine → ℝ :=
  highPacketActivation (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)
def higherBandRowData (d k r m D q ) (a b C lam L T : ℝ) (fine ) :
    HighUnionRowData d k D Unit (fun _ => HigherBandRowMark d r m D q fine) where
  rowLaw := fun _ => (highPacketAbsoluteLaw (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine))
  rowMass := fun _ => higherBandRowMass d r m D q a b C lam L T fine
  rowActivation := fun _ => higherBandRowActivation d r m D q a b C lam L T fine
  rowIntercept := fun _ => highPacketIntercept a b m r D q
  rowSlope := fun j _ e x => highPacketSlope a b m r D q
    (fun ζ l => higherBandCarrierFactor d r lam fine ζ l (highLocalCoordinates d k j x)) e
  rowVector := fun _ e => (highResponseMarkAtom C q e.2.2).2
  rowTime := fun _ e => (highResponseMarkAtom 0 q e.2.2).1
theorem higherBandRowMass_eq_variation (d r m D q a b C lam L T)
    (hT : 1 ≤ T) (fine ) : higherBandRowMass d r m D q a b C lam L T fine =
      ((higherBandSignedRow d r m D q a b C lam L T fine).variation univ).toReal := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  exact highPacketMarkMass_eq_variation _ a b m r D q C _
    (higherBandCarrierAmplitude_measurable d r D lam fine)
    (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine)
theorem higherBandRowMass_nonneg (d r m D q a b C lam L T fine) :
    0 ≤ higherBandRowMass d r m D q a b C lam L T fine := signedMarkMass_nonneg _ _
theorem higherBandRowActivation_bound (d r m D q a b C lam L T fine e) :
    |higherBandRowActivation d r m D q a b C lam L T fine e| ≤ higherBandRowMass d r m D q a b C lam L T fine :=
  absoluteActivation_bound _ _ _
def higherBandInterpolationCap (d r : ℕ) (lam T : ℝ) : ℝ :=
  2 * r * (1024 * |lam| * d^2)^(r-1) * T^2 * (1+Real.log T)^(r-2)
def ordinaryDensityActivityBase (a b : ℝ) : ℝ :=
  Real.exp (1 + exteriorTau ((a+b)/(b-a))) * |b / densityMargin a b 0|
def higherBandRowActivityCap (d r m D q : ℕ) (a b C lam T : ℝ) : ℝ :=
  (ordinaryDensityActivityBase a b)^r * D^r *
    Real.exp (m * exteriorTau ((a+b)/(b-a))) *
    (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) * higherBandInterpolationCap d r lam T
def higherBandTargetScale (d r : ℕ) (N μ : ℝ) : ℝ :=
  N * (μ * (1 + Real.log N))^(((r : ℝ)-2)/d)
def higherBandFamilyTarget  (i : Fin (D-2) × Bool) : ℕ := i.1.val + 3
def higherBandFamilyGuardDegree  (M : ℕ) (i : Fin (D-2) × Bool) : ℕ :=
  if i.2 then M else D
def higherBandFamilyUpper (d : ℕ) {D : ℕ} (ℓ N μ : ℝ) (i : Fin (D-2) × Bool) : ℝ :=
  if i.2 then higherBandTargetScale d (higherBandFamilyTarget i) N μ
  else min ℓ (higherBandTargetScale d (higherBandFamilyTarget i) N μ)
def HigherBandFamilySelected (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (i : Fin (D-2) × Bool) : Prop :=
  1 ≤ higherBandFamilyUpper d ℓ N μ i ∧
  (i.2 = true → ℓ < higherBandTargetScale d (higherBandFamilyTarget i) N μ) ∧
  higherBandFamilyTarget i ≤ higherBandFamilyGuardDegree M i ∧
  0 < higherBandRowMass d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q
    a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i) i.2
abbrev HigherBandFamilyIndex (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :=
  {i : Fin (D-2) × Bool // HigherBandFamilySelected d D M q a b C lam ℓ N μ i}
instance higherBandFamilyIndex_fintype (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    Fintype (HigherBandFamilyIndex d D M q a b C lam ℓ N μ) := by
  classical
  infer_instance
def HigherBandFamilyMark (d D M q a b C lam ℓ N μ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) : Type :=
  HigherBandRowMark d (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q i.val.2
instance higherBandFamilyMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    MeasurableSpace (HigherBandFamilyMark d D M q a b C lam ℓ N μ i) := by
  dsimp [HigherBandFamilyMark]
  infer_instance
instance higherBandFamilyMark_standardBorel (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    StandardBorelSpace (HigherBandFamilyMark d D M q a b C lam ℓ N μ i) := by
  letI : StandardBorelSpace (HigherBandCarrier d (higherBandFamilyTarget i.val) i.val.2) :=
    higherBandCarrier_standardBorel _ _ _
  letI : StandardBorelSpace (HighPacketMarkIndex (HighFrameIndex d D)
      (higherBandFamilyGuardDegree M i.val) (higherBandFamilyTarget i.val) D q) := by infer_instance
  dsimp [HigherBandFamilyMark, higherBandFamilyMark_measurable]
  infer_instance
def higherBandFamilyComponent (d k D M q a b C lam ℓ N μ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    HighUnionRowData d k D Unit (fun _ => HigherBandFamilyMark d D M q a b C lam ℓ N μ i) :=
  higherBandRowData d k (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q
    a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2
def higherBandFamilyData (d k D M q a b C lam ℓ N μ) :
    HighUnionRowData d k D (HigherBandFamilyIndex d D M q a b C lam ℓ N μ)
      (HigherBandFamilyMark d D M q a b C lam ℓ N μ) where
  rowLaw := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowLaw ()
  rowMass := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowMass ()
  rowActivation := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowActivation ()
  rowIntercept := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowIntercept ()
  rowSlope := fun j i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowSlope j ()
  rowVector := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowVector ()
  rowTime := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowTime ()
theorem higherBandFamily_target_bounds (d D M q a b C lam ℓ N μ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    3 ≤ higherBandFamilyTarget i.val ∧ higherBandFamilyTarget i.val ≤ D := by
  dsimp [higherBandFamilyTarget]
  omega
theorem higherBandFamily_mass_positive (d k D M q a b C lam ℓ N μ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    0 < (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass i := i.property.2.2.2
theorem higherBand_zero_mass_signed_zero (d r m D q a b C lam L T)
    (hT : 1 ≤ T) (fine ) (hz : higherBandRowMass d r m D q a b C lam L T fine = 0) :
    higherBandSignedRow d r m D q a b C lam L T fine = 0 := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  rw [higherBandRowMass_eq_variation d r m D q a b C lam L T hT fine] at hz
  have hi := highPacketMarkWeight_integrable (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)
    (higherBandCarrierAmplitude_measurable d r D lam fine)
    (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine)
  exact VectorMeasure.variation_eq_zero.mp ((Measure.measure_univ_eq_zero).mp ((ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (by rw [higherBandSignedRow, highPacketSignedMeasure, Measure.variation_withDensityᵥ hi]; rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact ne_of_lt hi.hasFiniteIntegral)))
end NearlyMinimax
