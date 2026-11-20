module

public import NearlyMinimax.HighCenteredMark
public import NearlyMinimax.HighRawUpdates

@[expose] public section

/-! Actual positive reference-law balancing by a zero-weight constant reset. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section
variable {d : ℕ} {E : Type*} (C : ModelConstants d) (B A w : E → ℝ) {a b r W : ℝ} (δ q : ℝ)

def highCenterRadius : ℝ :=
  min (1 - C.densityLower) (C.densityUpper - 1) / 2

def highCenterMix : ℝ :=
  highCenterRadius C / (2 * (C.densityUpper - C.densityLower))

theorem highCenterRadius_pos : 0 < highCenterRadius C :=
  div_pos (lt_min (sub_pos.mpr C.densityLower_lt_one) (sub_pos.mpr C.one_lt_densityUpper))
    (by norm_num)

theorem highCenterRadius_le_margins :
    2 * highCenterRadius C ≤ 1 - C.densityLower ∧
      2 * highCenterRadius C ≤ C.densityUpper - 1 := by
  dsimp [highCenterRadius]
  grind

theorem highCenterMix_mem :
    0 < highCenterMix C ∧ highCenterMix C < 1 := by
  have hgap : 0 < C.densityUpper - C.densityLower := by
    linarith [C.densityLower_lt_one, C.one_lt_densityUpper]
  have hm := highCenterRadius_le_margins C
  constructor
  · exact div_pos (highCenterRadius_pos C) (by positivity)
  · apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith

def balancedResetAnchor : ℝ := (1 - δ * q) / (1 - δ)

theorem balancedResetAnchor_identity (hδ : δ < 1) :
    δ * q + (1 - δ) * balancedResetAnchor δ q = 1 := by
  unfold balancedResetAnchor
  grind

theorem balancedResetAnchor_margins {δ q : ℝ} (hr : 0 < r)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (ha : a + r ≤ 1) (hb : 1 + r ≤ b)
    (hW : b - a ≤ W) (hδW : δ * W ≤ r / 2) (hq : q ∈ Icc a b) :
    (1 - δ) * (balancedResetAnchor δ q - a) ≥ r / 2 ∧
      (1 - δ) * (b - balancedResetAnchor δ q) ≥ r / 2 := by
  have hi := balancedResetAnchor_identity δ q hδ1
  have hl : δ * (q - a) ≤ δ * W := mul_le_mul_of_nonneg_left (by linarith [hq.2]) hδ0
  have hu : δ * (b - q) ≤ δ * W := mul_le_mul_of_nonneg_left (by linarith [hq.1]) hδ0
  constructor <;> nlinarith

theorem balancedResetAnchor_mem (a b r W δ q : ℝ) (hr : 0 < r)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (ha : a + r ≤ 1) (hb : 1 + r ≤ b)
    (hW : b - a ≤ W) (hδW : δ * W ≤ r / 2) (hq : q ∈ Icc a b) :
    balancedResetAnchor δ q ∈ Icc a b := by
  have hm := balancedResetAnchor_margins hr hδ0 hδ1 ha hb hW hδW hq
  constructor <;> nlinarith

/-- The manuscript's mixing constant is uniform in M. -/
theorem sourceBalancedResetAnchor_mem {C : ModelConstants d}
    {M q : ℝ} (hM : 0 < M) (hmargin : 1 / M ≤ highCenterRadius C)
    (hq : q ∈ Icc (C.densityLower + 1 / M) (C.densityUpper - 1 / M)) :
    balancedResetAnchor (highCenterMix C) q ∈
      Icc (C.densityLower + 1 / M) (C.densityUpper - 1 / M) := by
  have hr := highCenterRadius_pos C
  have hδ := highCenterMix_mem C
  have hm := highCenterRadius_le_margins C
  have hg : C.densityUpper - C.densityLower ≠ 0 := by
    bound
  apply balancedResetAnchor_mem _ _ (highCenterRadius C)
    (C.densityUpper - C.densityLower) (highCenterMix C) q hr hδ.1.le hδ.2
  · bound
  · bound
  · linarith [one_div_pos.mpr hM]
  · dsimp [highCenterMix]
    field_simp
    linarith
  · exact hq

def balancedReferenceLaw [MeasurableSpace E] (μ : Measure E) (δ : ℝ) :
    Measure (E ⊕ Unit) :=
  ENNReal.ofReal δ • μ.map Sum.inl + ENNReal.ofReal (1 - δ) • Measure.dirac (Sum.inr ())

theorem balancedReferenceLaw_probability [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    IsProbabilityMeasure (balancedReferenceLaw μ δ) := by
  constructor
  rw [balancedReferenceLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp
  rw [← ENNReal.ofReal_add hδ0 (sub_nonneg.mpr hδ1)]
  simp

def balancedIntercept : E ⊕ Unit → ℝ :=
  Sum.elim B (fun _ => balancedResetAnchor δ q)

def balancedSlope : E ⊕ Unit → ℝ := Sum.elim A (fun _ => 0)

def balancedActivation : E ⊕ Unit → ℝ :=
  Sum.elim (fun e => w e / δ) (fun _ => 0)

end

section
variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {A : E → ℝ}
    (hA : Measurable A)

theorem balancedReferenceLaw_integrable (δ : ℝ) {F : E ⊕ Unit → ℝ} (hF : Measurable F)
    (hFi : Integrable (fun e => F (Sum.inl e)) μ) :
    Integrable F (balancedReferenceLaw μ δ) := by
  exact integrable_add_measure.mpr ⟨((integrable_map_measure hF.aestronglyMeasurable measurable_inl.aemeasurable).mpr hFi).smul_measure ENNReal.ofReal_ne_top,
    (integrable_dirac' hF.stronglyMeasurable (by finiteness)).smul_measure ENNReal.ofReal_ne_top⟩

include hδ0 hδ1 in
theorem balancedReferenceLaw_integral
    {F : E ⊕ Unit → ℝ} (hF : Measurable F)
    (hFi : Integrable (fun e => F (Sum.inl e)) μ) :
    ∫ e, F e ∂balancedReferenceLaw μ δ =
      δ * (∫ e, F (Sum.inl e) ∂μ) + (1 - δ) * F (Sum.inr ()) := by
  have hm  :=
    (integrable_map_measure hF.aestronglyMeasurable measurable_inl.aemeasurable).mpr hFi
  rw [balancedReferenceLaw, integral_add_measure
    (hm.smul_measure ENNReal.ofReal_ne_top) ((integrable_dirac' hF.stronglyMeasurable (by finiteness)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    integral_map measurable_inl.aemeasurable hF.aestronglyMeasurable,
    integral_dirac' _ _ hF.stronglyMeasurable,
    ENNReal.toReal_ofReal hδ0, ENNReal.toReal_ofReal (sub_nonneg.mpr hδ1)]
  rfl

include hδ0 in
theorem balancedIntercept_integral_one (hδ1 : δ < 1)
    {B : E → ℝ} (hB : Measurable B) (hBi : Integrable B μ) :
    ∫ e, balancedIntercept B δ (∫ e, B e ∂μ) e ∂balancedReferenceLaw μ δ = 1 := by
  rw [balancedReferenceLaw_integral hδ0 hδ1.le
    (by solve_by_elim [hB.sumElim]) hBi]
  exact balancedResetAnchor_identity δ _ hδ1

include hδ0 hδ1 hA in
theorem balancedSlope_integral_zero (hAi : Integrable A μ) (hcenter : ∫ e, A e ∂μ = 0) :
    ∫ e, balancedSlope A e ∂balancedReferenceLaw μ δ = 0 := by
  rw [balancedReferenceLaw_integral hδ0 hδ1 (by solve_by_elim [hA.sumElim]) hAi]
  simp_all [balancedSlope]

end

theorem balancedActivation_bound {E : Type*} (w : E → ℝ) {δ W : ℝ} (hδ : 0 < δ) (hW0 : 0 ≤ W)
    (hW : ∀ e, |w e| ≤ W) (e : E ⊕ Unit) : |balancedActivation w δ e| ≤ W / δ := by
  cases e with
  | inl e =>
    change |w e / δ| ≤ _
    rw [abs_div]
    bound
  | inr e =>
    change |0| ≤ _
    simpa using div_nonneg hW0 hδ.le

variable {E : Type*} [MeasurableSpace E] (μ : Measure E)

theorem balancedActivation_integral {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {w : E → ℝ} (hw : Measurable w) {F : E ⊕ Unit → ℝ} (hF : Measurable F)
    (hWF : Integrable (fun e => w e * F (Sum.inl e)) μ) :
    ∫ e, balancedActivation w δ e * F e ∂balancedReferenceLaw μ δ =
      ∫ e, w e * F (Sum.inl e) ∂μ := by
  have hFi : Integrable (fun e => balancedActivation w δ (Sum.inl e) * F (Sum.inl e)) μ := by
    convert hWF.div_const δ using 1
    funext e
    change w e / δ * F (Sum.inl e) = _
    ring
  rw [balancedReferenceLaw_integral hδ.le hδ1 (F := (fun e => balancedActivation w δ e * F e))
    (((hw.div_const δ).sumElim measurable_const).mul hF) hFi]
  simp [balancedActivation]
  have he : (fun e => w e / δ * F (Sum.inl e)) =
      (fun e => (w e * F (Sum.inl e)) / δ) := by funext e; ring
  rw [he, integral_div]
  field_simp

theorem balancedActivation_integral_zero
    {μ : Measure E} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {w : E → ℝ} (hw : Measurable w) (hwi : Integrable w μ) (hc : ∫ e, w e ∂μ = 0) :
    ∫ e, balancedActivation w δ e ∂balancedReferenceLaw μ δ = 0 := by
  grind [balancedActivation_integral μ hδ hδ1 hw (F := (fun _ => 1)) measurable_const (by simpa using hwi)]

theorem boundedIntercept_integrable [IsFiniteMeasure μ] {B : E → ℝ} (hB : Measurable B)
    (a b : ℝ) (hb : ∀ e, B e ∈ Icc a b) : Integrable B μ := by
  apply (integrable_const (max |a| |b|)).mono' hB.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  rw [Real.norm_eq_abs]
  grind

theorem boundedIntercept_mean_mem [IsProbabilityMeasure μ] {B : E → ℝ} (hB : Measurable B)
    (a b : ℝ) (hb : ∀ e, B e ∈ Icc a b) : (∫ e, B e ∂μ) ∈ Icc a b := by
  have hBi := boundedIntercept_integrable μ hB a b hb
  constructor
  · have hh := integral_mono (integrable_const a) hBi (fun e => (hb e).1)
    simpa using hh
  · have hh := integral_mono hBi (integrable_const b) (fun e => (hb e).2)
    simpa using hh

end NearlyMinimax
