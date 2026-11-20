module

public import NearlyMinimax.FinePairRows
public import NearlyMinimax.PacketRowData


@[expose] public section

/-! Primitive Borel, interval and reference-centering facts for the actual
three-row fine-pair data. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

section
variable (d D M q : ℕ)

theorem finePairRowIntercept_measurable (a b : ℝ) (i : FinePairRowTag) :
    Measurable (finePairRowIntercept d D M q a b i) := by
  cases i
  · apply highPacketIntercept_measurable <;> assumption
  · apply highPacketIntercept_measurable <;> assumption
  · exact finePairPacketIntercept_measurable a b M q

theorem finePairRowVector_measurable (C : ℝ) (i : FinePairRowTag)
    (γ : HighFrameIndex d D) : Measurable (fun e => finePairRowVector d D M q C i e γ) :=
  (measurable_of_countable (fun h : HighResponseMarkIndex (HighFrameIndex d D) q =>
    (highResponseMarkAtom C q h).2 γ)).comp (measurable_snd.comp measurable_snd)

theorem finePairRowTime_measurable (i : FinePairRowTag) :
    Measurable (finePairRowTime d D M q i) :=
  (measurable_of_countable (fun h : HighResponseMarkIndex (HighFrameIndex d D) q =>
    responseNode q h.2.2)).comp (measurable_snd.comp measurable_snd)

end

section
variable (d k D M q : ℕ) (a b : ℝ)

theorem finePairRowSlope_joint_measurable
    (j : HighWindowLabels d k) (i : FinePairRowTag) :
    Measurable (fun ex : FinePairRowMark d D M q i × Covariate d =>
      finePairRowSlope d k D M q a b j i ex.1 ex.2) := by
  have hψ :=
    (finePairTimeFieldValue_measurable d).comp
      (measurable_fst.prodMk ((highLocalCoordinates_measurable d k j).comp measurable_snd))
  cases i
  · exact (highPacketSlope_measurable a b D 2 D q (fun _ : Unit => fun _ => (1 : ℝ))
      (fun _ => measurable_const)).comp measurable_fst
  · exact highPacketSlope_joint_measurable_general d D 2 D q a b
      (fun ζ x _ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) (fun _ => hψ)
  · exact finePairPacketSlope_joint_measurable a b M q
      (fun ζ x => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) hψ

theorem finePairRow_reset_interval (ha : 0 < a) (hab : a < b)
    (j : HighWindowLabels d k) (i : FinePairRowTag) (e : FinePairRowMark d D M q i)
    (x : Covariate d) (v : ℝ) (hv : v ∈ Icc a b) :
    finePairRowSlope d k D M q a b j i e x * v + finePairRowIntercept d D M q a b i e ∈ Icc a b := by
  cases i
  · have h := densityPacketReset_mem a b ha hab D 2 D (by norm_num) e.2.1
      (fun _ : Unit => v) (fun _ _ => 1) () hv (by simp)
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, highPacketSlope,
      highPacketIntercept, localDensityReset] <;> ring
  · have h := densityPacketReset_mem a b ha hab D 2 D (by norm_num) e.2.1
      (fun _ : Unit => v) (fun _ _ => finePairTimeFieldValue e.1 (highLocalCoordinates d k j x))
      () hv (fun _ => (finePairTimeFieldValue_abs e.1 _).le)
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, highPacketSlope,
      highPacketIntercept, localDensityReset] <;> ring
  · have h := finePairDensityReset_mem_interval a b ha hab _ _
      (finePairPacketIntercept_mem a b hab.le M q e) (fineModulationNode_bound e.2.1.2)
      (fun _ : Unit => v) (fun _ => finePairTimeFieldValue e.1 (highLocalCoordinates d k j x)) () hv
      (finePairTimeFieldValue_abs e.1 _).le
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, finePairPacketSlope,
      finePairPacketIntercept, finePairDensityReset, finePairDensityAtom] <;> ring

end

section Reference
variable (d : ℕ) [NeZero d] (k D M q : ℕ) (a b C T₀ N : ℝ)
    (hpos : ∀ i, 0 < finePairRowMass d D M q a b C T₀ N i)
include hpos

section
variable (i : FinePairRowTag)

local notation "P" => finePairRowPacket d D M a b T₀ N i

theorem finePairRowLaw_probability :
    IsProbabilityMeasure (finePairRowLaw d D M q a b C T₀ N i) := by
  obtain ⟨hfin, hA⟩ := finePairRowPacket_valid d D M a b T₀ N i
  exact absoluteMarkLaw_probability _ _ (responsePacketWeight_integrable (P).weights q C (P).amplitude (P).carrier hA) (hpos i)

omit hpos in
theorem finePairRowActivation_measurable :
    Measurable (finePairRowActivation d D M q a b C T₀ N i) :=
  absoluteActivation_measurable _ _ (responsePacketWeight_measurable (P).weights q C (P).amplitude
    (finePairRowPacket_valid d D M a b T₀ N i).2.meas)

theorem finePairRowActivation_centered :
    (∫ e, finePairRowActivation d D M q a b C T₀ N i e ∂finePairRowLaw d D M q a b C T₀ N i) = 0 := by
  obtain ⟨hfin, hA⟩ := finePairRowPacket_valid d D M a b T₀ N i
  exact absoluteActivation_centered _ _ (responsePacketWeight_measurable (P).weights q C (P).amplitude hA.meas)
    (hpos i) (responsePacketWeight_integral_zero (P).weights q C (P).amplitude (P).carrier hA)

end

section
variable (ha : 0 < a) (hab : a < b)
    (j : HighWindowLabels d k) (x : Covariate d) (i : FinePairRowTag)
include ha hab

theorem finePairRowSlope_integrable :
    Integrable (fun e => finePairRowSlope d k D M q a b j i e x)
      (finePairRowLaw d D M q a b C T₀ N i) := by
  letI := finePairRowLaw_probability d D M q a b C T₀ N hpos i
  have hm : Measurable (fun e : FinePairRowMark d D M q i => finePairRowSlope d k D M q a b j i e x) :=
    (finePairRowSlope_joint_measurable d k D M q a b j i).comp
    (measurable_id.prodMk (measurable_const (a := x)))
  apply (integrable_const ((b-a)/(4*b))).mono' hm.aestronglyMeasurable
  filter_upwards [] with e
  simpa only [Real.norm_eq_abs] using finePairRowSlope_bound d k D M q a b ha hab j i e x

theorem finePairRowSlope_centered :
    (∫ e, finePairRowSlope d k D M q a b j i e x ∂finePairRowLaw d D M q a b C T₀ N i) = 0 := by
  have hm : Measurable (fun ζ : ℝ × FinePairFieldMark d =>
      finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) :=
    (boundedHyperplaneFieldValue_section_measurable d _).comp measurable_snd
  cases i
  · exact highPacketAbsoluteLaw_slope_integral_zero (Measure.dirac ()) a b ha hab D 2 D q (by norm_num)
      C (fun _ => finePairUnitMatrix d D) (SeparatedMatrixIntegrable.const _ _) (hpos .unit)
      (fun _ : Unit => fun _ => 1) (fun _ => measurable_const) (by simp)
  · exact highPacketAbsoluteLaw_slope_integral_zero (finePairTimeFieldMeasure d 0 T₀) a b ha hab
      D 2 D q (by norm_num) C _ (finePairTimeMatrix_integrable d 0 T₀ _) (hpos .coarse)
      (fun ζ _ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) (fun _ => hm)
      (fun ζ _ => (finePairTimeFieldValue_abs ζ _).le)
  · exact finePairPacketAbsoluteLaw_slope_integral_zero (finePairTimeFieldMeasure d T₀ N) a b M q
      C _ (finePairTimeMatrix_integrable d T₀ N _) (hpos .fine)
      ha hab (fun ζ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) hm
      (fun ζ => (finePairTimeFieldValue_abs ζ _).le)

end

end Reference
end NearlyMinimax
