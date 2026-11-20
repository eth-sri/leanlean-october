module

public import NearlyMinimax.HigherBandFamily
public import NearlyMinimax.SingletonRow
public import NearlyMinimax.FinePairRowNondegenerate

@[expose] public section

/-! The complete finite source row family: singleton, three genuine pair
rows, and all selected ordinary higher-target coarse/fine bands. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

def highUnionRowRestrict {d k D : ℕ} {I : Type*} {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    (R : HighUnionRowData d k D I E) (i : I) : HighUnionRowData d k D Unit (fun _ => E i) where
  rowLaw := fun _ => R.rowLaw i
  rowMass := fun _ => R.rowMass i
  rowActivation := fun _ => R.rowActivation i
  rowIntercept := fun _ => R.rowIntercept i
  rowSlope := fun j _ => R.rowSlope j i
  rowVector := fun _ => R.rowVector i
  rowTime := fun _ => R.rowTime i

abbrev SourceRowIndex (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :=
  FinePairRowTag ⊕ (Unit ⊕ HigherBandFamilyIndex d D M q a b C lam ℓ N μ)

def sourceRowSpace (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    SourceRowIndex d D M q a b C lam ℓ N μ → MarkPacketSpace
  | .inl p => finePairRowSpace d D M p
  | .inr (.inl _) => .of Unit (HighDensityMarkIndex D 1 D)
  | .inr (.inr i) =>
    letI := higherBandCarrier_standardBorel d (higherBandFamilyTarget i.val) i.val.2
    .of (HigherBandCarrier d (higherBandFamilyTarget i.val) i.val.2)
      (HighDensityMarkIndex (higherBandFamilyGuardDegree M i.val) (higherBandFamilyTarget i.val) D)

abbrev SourceRowMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (i : SourceRowIndex d D M q a b C lam ℓ N μ) :=
  (sourceRowSpace d D M q a b C lam ℓ N μ i).Mark (HighFrameIndex d D) q

instance sourceRowMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) : MeasurableSpace (SourceRowMark d D M q a b C lam ℓ N μ i) :=
  inferInstance

instance sourceRowMark_standardBorel (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) : StandardBorelSpace (SourceRowMark d D M q a b C lam ℓ N μ i) := by
  letI : StandardBorelSpace (HighResponseMarkIndex (HighFrameIndex d D) q) := by infer_instance
  infer_instance

def sourceRowPacket (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      MarkPacketData (sourceRowSpace d D M q a b C lam ℓ N μ i) (HighFrameIndex d D)
  | .inl p => finePairRowPacket d D M a b ℓ N p
  | .inr (.inl _) => ⟨Measure.dirac (), densityPacketWeight a b D 1 D, fun _ => finePairUnitMatrix d D⟩
  | .inr (.inr i) =>
    let r := higherBandFamilyTarget i.val
    ⟨higherBandCarrierMeasure d r ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2,
      densityPacketWeight a b (higherBandFamilyGuardDegree M i.val) r D,
      higherBandCarrierAmplitude d r D lam i.val.2⟩

theorem sourceRowPacket_valid (d : ℕ) [NeZero d] (D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    let P := sourceRowPacket d D M q a b C lam ℓ N μ i
    IsFiniteMeasure P.carrier ∧ SeparatedMatrixIntegrable P.carrier P.amplitude := by
  rcases i with p | (_ | i)
  · exact finePairRowPacket_valid d D M a b ℓ N p
  · dsimp [sourceRowPacket]
    exact ⟨inferInstance, SeparatedMatrixIntegrable.const _ _⟩
  · exact ⟨higherBandCarrierMeasure_finite _ _ _ _ i.property.1 _,
      higherBandCarrierAmplitude_integrable _ _ _ _ _ _ i.property.1 _⟩

def sourceRowComponent (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      HighUnionRowData d k D Unit (fun _ => SourceRowMark d D M q a b C lam ℓ N μ i)
  | i =>
    let P := sourceRowPacket d D M q a b C lam ℓ N μ i
    let R : HighUnionRowData d k D Unit (fun _ => SourceRowMark d D M q a b C lam ℓ N μ i) := match i with
      | .inl p => highUnionRowRestrict (finePairRowData d k D M q a b C ℓ N) p
      | .inr (.inl _) => singletonRowData d k D q a b C
      | .inr (.inr j) => higherBandFamilyComponent d k D M q a b C lam ℓ N μ j
    { rowLaw := fun _ => P.law q C
      rowMass := fun _ => P.mass q C
      rowIntercept := R.rowIntercept
      rowSlope := R.rowSlope
      rowActivation := fun _ => P.activation q C
      rowVector := fun _ e => (highResponseMarkAtom C q e.2.2).2
      rowTime := fun _ e => responseNode q e.2.2.2.2 }

def sourceRowData (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    HighUnionRowData d k D (SourceRowIndex d D M q a b C lam ℓ N μ)
      (SourceRowMark d D M q a b C lam ℓ N μ) where
  rowLaw := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowLaw ()
  rowMass := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowMass ()
  rowActivation := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowActivation ()
  rowIntercept := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowIntercept ()
  rowSlope := fun j i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowSlope j ()
  rowVector := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowVector ()
  rowTime := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowTime ()

end NearlyMinimax
