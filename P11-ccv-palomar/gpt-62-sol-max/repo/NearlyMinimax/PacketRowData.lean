module

public import NearlyMinimax.PacketAbsoluteMoments
public import NearlyMinimax.HighUnionSource

@[expose] public section

noncomputable section
open MeasureTheory Set
namespace NearlyMinimax

set_option backward.isDefEq.respectTransparency false

theorem high_source_interval_numeric {d : ℕ} (C : ModelConstants d) (M : ℝ)
    (hM : highCenterResolutionThreshold C ≤ M) :
    0 < C.densityLower+1/M ∧ C.densityLower+1/M < C.densityUpper-1/M := by
  have hg := highCenterResolution_guards C M hM
  have hM0 : 0 < M := by linarith
  constructor
  · linarith [C.densityLower_pos,one_div_pos.mpr hM0]
  · linarith [hg.2,highCenterRadius_pos C,(highCenterRadius_le_margins C).1,
      (highCenterRadius_le_margins C).2]

theorem highPacketSlope_joint_measurable_general {Z : Type*} [MeasurableSpace Z]
    (d m r D q : ℕ) (a b : ℝ) (B : Z → Covariate d → Fin r → ℝ)
    (hB : ∀ l, Measurable (fun zx : Z × Covariate d => B zx.1 zx.2 l)) :
    Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) m r D q) × Covariate d =>
      highPacketSlope a b m r D q (fun ζ l => B ζ ex.2 l) ex.1) := by
  have hc : Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) m r D q) × Covariate d =>
      densityMargin a b (densityPacketAtom a b m r D ex.1.2.1).1 / ((r : ℝ)*b)) :=
    (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
      densityMargin a b (densityPacketAtom a b m r D h.1).1 / ((r : ℝ)*b))).comp
        (measurable_snd.comp measurable_fst)
  have he (l : Fin r) : Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) m r D q) × Covariate d =>
      (densityPacketAtom a b m r D ex.1.2.1).2 l) :=
    (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
      (densityPacketAtom a b m r D h.1).2 l)).comp (measurable_snd.comp measurable_fst)
  exact hc.mul (Finset.measurable_fun_sum _ (fun l _ => (he l).mul
    ((hB l).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))

/-- Ordinary packet rows share the same finite marks, with different carriers and slope features. -/
def highPacketRowData {Z : Type*} [MeasurableSpace Z] (d k m r D q : ℕ)
    (a b C : ℝ) (σ : Measure Z) (A : Z → HighFrameIndex d D → HighFrameIndex d D → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ) :
    HighUnionRowData d k D Unit (fun _ => Z × HighPacketMarkIndex (HighFrameIndex d D) m r D q) where
  rowLaw := fun _ => highPacketAbsoluteLaw σ a b m r D q C A
  rowMass := fun _ => highPacketMarkMass σ a b m r D q C A
  rowActivation := fun _ => highPacketActivation σ a b m r D q C A
  rowIntercept := fun _ => highPacketIntercept a b m r D q
  rowSlope := fun j _ e x => highPacketSlope a b m r D q (fun ζ l => B j ζ x l) e
  rowVector := fun _ e => (highResponseMarkAtom C q e.2.2).2
  rowTime := fun _ e => (highResponseMarkAtom 0 q e.2.2).1

theorem highPacketRowData_guards {Z : Type*} [MeasurableSpace Z] {d : ℕ}
    (C : ModelConstants d) (M : ℝ) (hM : highCenterResolutionThreshold C ≤ M)
    (k m r D q : ℕ) (hr : 1 ≤ r) (Cfr : ℝ) (hCfr : 1 ≤ Cfr)
    (σ : Measure Z) [IsFiniteMeasure σ] (A : Z → HighFrameIndex d D → HighFrameIndex d D → ℝ)
    (hA : SeparatedMatrixIntegrable σ A)
    (hpos : 0 < highPacketMarkMass σ (C.densityLower+1/M) (C.densityUpper-1/M) m r D q Cfr A)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hmB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
    (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1) :
    HighUnionSourceGuards C M Cfr
      (highPacketRowData d k m r D q (C.densityLower+1/M) (C.densityUpper-1/M) Cfr σ A B) := by
  let a := C.densityLower+1/M
  let b := C.densityUpper-1/M
  obtain ⟨ha, hab⟩ := high_source_interval_numeric C M hM
  have hm (j) (x : Covariate d) (l : Fin r) : Measurable (fun ζ => B j ζ x l) :=
    (hmB j l).comp (measurable_prodMk_right (y := x))
  refine {
    resolution := hM
    frame := hCfr
    row_probability := fun _ => highPacketAbsoluteLaw_probability σ a b m r D q Cfr A hA hpos
    mass_nonneg := fun _ => hpos.le
    total_positive := by simpa [highRowTotalMass, highPacketRowData] using hpos
    activation_measurable := fun _ => absoluteActivation_measurable _ _
      (highPacketMarkWeight_measurable a b m r D q Cfr A hA.meas)
    activation_bound := fun _ => highPacketActivation_bound σ a b m r D q Cfr A
    activation_centered := fun _ => highPacketActivation_centered σ a b m r D q Cfr A hA hpos
    slope_measurable := fun j _ => highPacketSlope_joint_measurable_general d m r D q a b (B j) (hmB j)
    slope_integrable := fun j x _ => highPacketSlope_integrable σ a b ha hab m r D q hr Cfr A hA hpos
      (fun ζ l => B j ζ x l) (hm j x) (fun ζ l => hB j ζ x l)
    slope_centered := fun j x _ => highPacketAbsoluteLaw_slope_integral_zero σ a b ha hab m r D q hr Cfr A hA hpos
      (fun ζ l => B j ζ x l) (hm j x) (fun ζ l => hB j ζ x l)
    intercept_measurable := fun _ => highPacketIntercept_measurable a b m r D q
    intercept_interval := fun _ e => (densityPacketAtom_mem a b hab.le m r D e.2.1).1
    row_reset_interval := ?_
    vector_measurable := ?_
    time_measurable := ?_
    vector_ball := fun _ _ => covarianceAtom_mem_ball Cfr (by linarith) _ _ _ _
    time_interval := fun _ _ => responseNode_mem_unit q _ }
  · intro j i e x v hv
    have h := densityPacketReset_mem a b ha hab m r D hr e.2.1
      (fun _ : Unit => v) (fun _ l => B j e.1 x l) () hv (hB j e.1 x)
    convert h using 1 <;> dsimp [highPacketRowData, highPacketSlope, highPacketIntercept, localDensityReset] <;> ring
  · intro i γ
    fun_prop
  · intro i
    fun_prop

end NearlyMinimax
