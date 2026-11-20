module

public import NearlyMinimax.FinePairHyperplanePacket
public import NearlyMinimax.FinePairResponseGeometry
public import NearlyMinimax.HighUnionReset
public import NearlyMinimax.HighLocalFrame

@[expose] public section

/-! The three genuine source fine-pair rows, on their actual finite-atom
and time/hyperplane mark spaces. The single global balancing law is applied
later by `HighUnionRowData`; these are its uncentered absolute row laws. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

inductive FinePairRowTag where
  | unit | coarse | fine
  deriving DecidableEq, Fintype

def finePairRowSpace (d D M : ℕ) : FinePairRowTag → MarkPacketSpace
  | .unit => .of Unit (HighDensityMarkIndex D 2 D)
  | .coarse => .of (ℝ × FinePairFieldMark d) (HighDensityMarkIndex D 2 D)
  | .fine => .of (ℝ × FinePairFieldMark d) (FinePairDensityIndex M)

abbrev FinePairRowMark (d D M q : ℕ) (i : FinePairRowTag) :=
  (finePairRowSpace d D M i).Mark (HighFrameIndex d D) q

instance finePairRowMark_measurable (d D M q : ℕ) (i : FinePairRowTag) :
    MeasurableSpace (FinePairRowMark d D M q i) := inferInstance

def finePairRowPacket (d D M : ℕ) (a b T₀ N : ℝ) :
    (i : FinePairRowTag) → MarkPacketData (finePairRowSpace d D M i) (HighFrameIndex d D)
  | .unit => ⟨Measure.dirac (), densityPacketWeight a b D 2 D, fun _ => finePairUnitMatrix d D⟩
  | .coarse => ⟨finePairTimeFieldMeasure d 0 T₀, densityPacketWeight a b D 2 D,
      finePairTimeMatrix d (finePairDistanceMatrix d D)⟩
  | .fine => ⟨finePairTimeFieldMeasure d T₀ N, finePairDensityWeight a b M,
      finePairTimeMatrix d (finePairDistanceMatrix d D)⟩

theorem finePairRowPacket_valid (d : ℕ) [NeZero d] (D M : ℕ) (a b T₀ N : ℝ) (i : FinePairRowTag) :
    let P := finePairRowPacket d D M a b T₀ N i
    IsFiniteMeasure P.carrier ∧ SeparatedMatrixIntegrable P.carrier P.amplitude := by
  cases i <;> dsimp [finePairRowPacket]
  · exact ⟨inferInstance, SeparatedMatrixIntegrable.const _ _⟩
  · exact ⟨finePairTimeFieldMeasure_finite d 0 T₀, finePairTimeMatrix_integrable d 0 T₀ _⟩
  · exact ⟨finePairTimeFieldMeasure_finite d T₀ N, finePairTimeMatrix_integrable d T₀ N _⟩

abbrev finePairRowLaw (d D M q : ℕ) (a b C T₀ N : ℝ) (i : FinePairRowTag) :
    Measure (FinePairRowMark d D M q i) := (finePairRowPacket d D M a b T₀ N i).law q C
abbrev finePairRowMass (d D M q : ℕ) (a b C T₀ N : ℝ) (i : FinePairRowTag) : ℝ :=
    (finePairRowPacket d D M a b T₀ N i).mass q C
abbrev finePairRowActivation (d D M q : ℕ) (a b C T₀ N : ℝ) (i : FinePairRowTag) :
    FinePairRowMark d D M q i → ℝ := (finePairRowPacket d D M a b T₀ N i).activation q C

def finePairRowIntercept (d D M q : ℕ) (a b : ℝ) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → ℝ
  | .unit => highPacketIntercept a b D 2 D q
  | .coarse => highPacketIntercept a b D 2 D q
  | .fine => finePairPacketIntercept a b M q

def finePairRowSlope (d k D M q : ℕ) (a b : ℝ) (j : HighWindowLabels d k) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → Covariate d → ℝ
  | .unit => fun e _ => highPacketSlope a b D 2 D q (fun _ _ => 1) e
  | .coarse => fun e x => highPacketSlope a b D 2 D q
      (fun ζ _ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) e
  | .fine => fun e x => finePairPacketSlope a b M q
      (fun ζ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) e

def finePairRowVector (d D M q : ℕ) (C : ℝ) (i : FinePairRowTag)
    (e : FinePairRowMark d D M q i) : HighFrameIndex d D → ℝ :=
  (highResponseMarkAtom C q e.2.2).2

def finePairRowTime (d D M q : ℕ) (i : FinePairRowTag) (e : FinePairRowMark d D M q i) : ℝ :=
  responseNode q e.2.2.2.2

def finePairRowData (d k D M q : ℕ) (a b C T₀ N : ℝ) :
    HighUnionRowData d k D FinePairRowTag (FinePairRowMark d D M q) where
  rowLaw := finePairRowLaw d D M q a b C T₀ N
  rowMass := finePairRowMass d D M q a b C T₀ N
  rowActivation := finePairRowActivation d D M q a b C T₀ N
  rowIntercept := finePairRowIntercept d D M q a b
  rowSlope := finePairRowSlope d k D M q a b
  rowVector := finePairRowVector d D M q C
  rowTime := finePairRowTime d D M q

section
variable (d D M q : ℕ)

section
variable (a b C T₀ N : ℝ) (i : FinePairRowTag)

theorem finePairRowMass_nonneg :
    0 ≤ finePairRowMass d D M q a b C T₀ N i := signedMarkMass_nonneg _ _

theorem finePairRowActivation_bound (e : FinePairRowMark d D M q i) :
    |finePairRowActivation d D M q a b C T₀ N i e| ≤ finePairRowMass d D M q a b C T₀ N i := absoluteActivation_bound _ _ _

end

theorem finePairRowIntercept_mem (a b : ℝ) (hab : a ≤ b)
    (i : FinePairRowTag) (e : FinePairRowMark d D M q i) :
    finePairRowIntercept d D M q a b i e ∈ Icc a b := by
  cases i
  · exact (densityPacketAtom_mem a b hab D 2 D e.2.1).1
  · exact (densityPacketAtom_mem a b hab D 2 D e.2.1).1
  · apply finePairPacketIntercept_mem <;> assumption

theorem finePairRowVector_ball (C : ℝ) (hC : 0 < C)
    (i : FinePairRowTag) (e : FinePairRowMark d D M q i) :
    (∑ γ, |finePairRowVector d D M q C i e γ|) ≤ C⁻¹ := covarianceAtom_mem_ball C hC _ _ _ _

theorem finePairRowTime_unit (i : FinePairRowTag)
    (e : FinePairRowMark d D M q i) : finePairRowTime d D M q i e ∈ Icc (0 : ℝ) 1 := responseNode_mem_unit q _

end

theorem finePairRowSlope_bound (d k D M q : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (j : HighWindowLabels d k) (i : FinePairRowTag) (e : FinePairRowMark d D M q i)
    (x : Covariate d) : |finePairRowSlope d k D M q a b j i e x| ≤ (b-a)/(4*b) := by
  cases i
  · exact highPacketSlope_bound a b ha hab D 2 D q (by norm_num)
      (fun _ : Unit => fun _ : Fin 2 => (1 : ℝ)) (by simp) e
  · exact highPacketSlope_bound a b ha hab D 2 D q (by norm_num) _
      (fun ζ _ => (finePairTimeFieldValue_abs ζ _).le) e
  · exact finePairPacketSlope_bound a b ha hab M q _
      (fun ζ => (finePairTimeFieldValue_abs ζ _).le) e

end NearlyMinimax
