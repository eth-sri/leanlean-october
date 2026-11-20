module

public import NearlyMinimax.FinePairRows


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
variable {Z : Type*} (d k D M q : ℕ) (C a b : ℝ) (ha : 0 < a) (hab : a < b) (j : HighWindowLabels d k)
    (i : FinePairRowTag)

theorem highPacketSlope_joint_measurable_finePair [MeasurableSpace Z]
    (d D q : ℕ) (a b : ℝ) (B : Z → Covariate d → Fin 2 → ℝ)
    (hB : ∀ l, Measurable (fun zx : Z × Covariate d => B zx.1 zx.2 l)) :
    let markIndex := HighPacketMarkIndex (HighFrameIndex d D) D 2 D q
    Measurable (fun ex : (Z × markIndex) × Covariate d =>
      highPacketSlope a b (fun ζ l => B ζ ex.2 l) ex.1) := by
  intro markIndex
  let atom := densityPacketAtom a b D 2 D
  have hc : Measurable (fun ex : (Z × markIndex) × Covariate d =>
      densityMargin a b (atom ex.1.2.1).1 / (2 * b)) :=
    (measurable_of_countable (fun h : markIndex =>
      densityMargin a b (atom h.1).1 / (2 * b))).comp
        (measurable_snd.comp measurable_fst)
  have he (l : Fin 2) : Measurable (fun ex : (Z × markIndex) × Covariate d =>
      (atom ex.1.2.1).2 l) :=
    (measurable_of_countable (fun h : markIndex =>
      (atom h.1).2 l)).comp (measurable_snd.comp measurable_fst)
  exact hc.mul (by fun_prop)

theorem finePairRowIntercept_measurable :
    Measurable (finePairRowIntercept d D M q a b i) := by
  cases i
  · exact highPacketIntercept_measurable a b D 2 D q
  · exact highPacketIntercept_measurable a b D 2 D q
  · exact finePairPacketIntercept_measurable a b M q

theorem finePairRowVector_measurable
    (γ : HighFrameIndex d D) : Measurable (fun e => finePairRowVector d D M q C i e γ) := by
  cases i
  · exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (highResponseMarkAtom C h.2).2 γ)).comp measurable_snd
  · exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (highResponseMarkAtom C h.2).2 γ)).comp measurable_snd
  · exact (measurable_of_countable (fun h : FinePairPacketIndex (HighFrameIndex d D) M q =>
      (highResponseMarkAtom C h.2).2 γ)).comp measurable_snd

theorem finePairRowTime_measurable :
    Measurable (finePairRowTime d D M q i) := by
  cases i
  · exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (highResponseMarkAtom 0 h.2).1)).comp measurable_snd
  · exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (highResponseMarkAtom 0 h.2).1)).comp measurable_snd
  · exact (measurable_of_countable (fun h : FinePairPacketIndex (HighFrameIndex d D) M q =>
      (highResponseMarkAtom 0 h.2).1)).comp measurable_snd

theorem finePairRowSlope_joint_measurable :
    Measurable (fun ex : FinePairRowMark d D M q i × Covariate d =>
      finePairRowSlope a b j i ex.1 ex.2) := by
  have hψ  :=
    (((boundedHyperplaneFieldValue_measurable d).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd) : Measurable fun ex => finePairTimeFieldValue ex.1 ex.2)).comp
      (measurable_fst.prodMk ((highLocalCoordinates_measurable j).comp measurable_snd))
  cases i
  · exact (highPacketSlope_measurable a b D 2 D q (fun _ : Unit => fun _ => (1 : ℝ))
      (fun _ => measurable_const)).comp measurable_fst
  · exact highPacketSlope_joint_measurable_finePair d D q a b
      (fun ζ x _ => finePairTimeFieldValue ζ (highLocalCoordinates j x)) (fun _ => hψ)
  · exact finePairPacketSlope_joint_measurable a b M q
      (ψ := (fun ζ x => finePairTimeFieldValue ζ (highLocalCoordinates j x))) hψ

include ha hab in
theorem finePairRow_reset_interval (e : FinePairRowMark d D M q i)
    (x : Covariate d) (v : ℝ) (hv : v ∈ Icc a b) :
    finePairRowSlope a b j i e x * v + finePairRowIntercept d D M q a b i e ∈ Icc a b := by
  cases i
  · have h := localDensityReset_mem_interval a b ha hab 2 (by norm_num)
      (densityPacketAtom a b D 2 D e.2.1).1 (densityPacketAtom_mem a b hab.le e.2.1).1
      (densityPacketAtom a b D 2 D e.2.1).2 (densityPacketAtom_mem a b hab.le e.2.1).2
      (p := (fun _ : Unit => v)) (fun _ _ => 1) (i := ()) hv (by norm_num)
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, highPacketSlope,
      highPacketIntercept, localDensityReset] <;> ring
  · have h := localDensityReset_mem_interval a b ha hab 2 (by norm_num)
      (densityPacketAtom a b D 2 D e.2.1).1 (densityPacketAtom_mem a b hab.le e.2.1).1
      (densityPacketAtom a b D 2 D e.2.1).2 (densityPacketAtom_mem a b hab.le e.2.1).2
      (p := (fun _ : Unit => v)) (fun _ _ => finePairTimeFieldValue e.1 (highLocalCoordinates j x))
      (i := ()) hv (fun _ => (finePairTimeFieldValue_abs e.1 _).le)
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, highPacketSlope,
      highPacketIntercept, localDensityReset] <;> ring
  · have h := finePairDensityReset_mem_interval ha hab
      (exteriorNode_mem hab.le e.2.1.1) (fineModulationNode_bound e.2.1.2)
      (p := (fun _ : Unit => v)) (ψ := (fun _ => finePairTimeFieldValue e.1 (highLocalCoordinates j x))) (u := ()) hv
      (finePairTimeFieldValue_abs e.1 _).le
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, finePairPacketSlope,
      finePairPacketIntercept, finePairDensityReset, finePairDensityAtom] <;> ring

end

section Reference
variable (d : ℕ) [NeZero d] (k D M q : ℕ) (a b C T₀ N : ℝ)
    (hpos : ∀ i, 0 < finePairRowMass d D M q a b C T₀ N i)
include hpos

variable (ha : 0 < a) (hab : a < b) (j : HighWindowLabels d k) (x : Covariate d) (i : FinePairRowTag)

theorem finePairRowLaw_probability :
    IsProbabilityMeasure (finePairRowLaw d D M q a b C T₀ N i) := by
  cases i
  · exact highPacketAbsoluteLaw_probability
      (fun _ _ => measurable_const) (integrable_const _) (hpos .unit)
  · exact highPacketAbsoluteLaw_probability
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse)
  · exact finePairPacketAbsoluteLaw_probability (finePairTimeFieldMeasure d T₀ N) a b M q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine)

theorem finePairRowActivation_measurable :
    Measurable (finePairRowActivation d D M q a b C T₀ N i) := by
  cases i
  · exact absoluteActivation_measurable _ (tensorWeight_measurable (densityPacketWeight a b D 2 D) q C
      (fun _ _ => measurable_const))
  · exact absoluteActivation_measurable _ (tensorWeight_measurable (densityPacketWeight a b D 2 D) q C
      (finePairTimeMatrix_measurable d _))
  · exact absoluteActivation_measurable _ (tensorWeight_measurable (finePairDensityWeight a b M) q C
      (finePairTimeMatrix_measurable d _))

theorem finePairRowActivation_centered :
    (∫ e, finePairRowActivation d D M q a b C T₀ N i e ∂finePairRowLaw d D M q a b C T₀ N i) = 0 := by
  cases i
  · exact highPacketActivation_centered
      (fun _ _ => measurable_const) (integrable_const _) (hpos .unit)
  · exact highPacketActivation_centered
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse)
  · exact finePairPacketActivation_centered (finePairTimeFieldMeasure d T₀ N) a b M q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine)

include ha hab in
theorem finePairRowSlope_integrable :
    Integrable (fun e => finePairRowSlope a b j i e x)
      (finePairRowLaw d D M q a b C T₀ N i) := by
  letI := finePairRowLaw_probability d D M q a b C T₀ N hpos i
  have hm : Measurable (fun e : FinePairRowMark d D M q i => finePairRowSlope a b j i e x) :=
    (finePairRowSlope_joint_measurable d k D M q a b j i).comp
    (measurable_id.prodMk (measurable_const (a := x)))
  apply (integrable_const ((b-a)/(4*b))).mono' hm.aestronglyMeasurable
  filter_upwards [] with e
  exact finePairRowSlope_bound ha hab j e x

include ha hab in
theorem finePairRowSlope_centered :
    (∫ e, finePairRowSlope a b j i e x ∂finePairRowLaw d D M q a b C T₀ N i) = 0 := by
  have hm : Measurable (fun ζ : ℝ × FinePairFieldMark d =>
      finePairTimeFieldValue ζ (highLocalCoordinates j x)) :=
    (boundedHyperplaneFieldValue_section_measurable _).comp measurable_snd
  cases i
  · exact highPacketAbsoluteLaw_slope_integral_zero ha hab (by norm_num) (A := (fun _ => finePairUnitMatrix d D)) (fun _ _ => measurable_const) (integrable_const _) (hpos .unit)
      (fun _ : Unit => fun _ => 1) (fun _ => measurable_const) (by norm_num)
  · exact highPacketAbsoluteLaw_slope_integral_zero ha hab (by norm_num) (finePairTimeMatrix_measurable d _)
      (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse)
      (fun ζ _ => finePairTimeFieldValue ζ (highLocalCoordinates j x)) (fun _ => hm)
      (fun ζ _ => (finePairTimeFieldValue_abs ζ _).le)
  · exact finePairPacketAbsoluteLaw_slope_integral_zero (finePairTimeFieldMeasure d T₀ N) a b M q
      C _ (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine)
      ha hab hm
      (fun ζ => (finePairTimeFieldValue_abs ζ _).le)

end Reference
end NearlyMinimax
