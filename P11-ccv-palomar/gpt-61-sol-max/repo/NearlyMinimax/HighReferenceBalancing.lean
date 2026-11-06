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

def highCenterRadius {d } (C : ModelConstants d)  :=
  min (1 - C.densityLower) (C.densityUpper - 1) / 2

def highCenterMix {d } (C : ModelConstants d)  :=
  highCenterRadius C / (2 * (C.densityUpper - C.densityLower))

section
variable {d : ℕ} (C : ModelConstants d)

theorem highCenterRadius_pos  : 0 < highCenterRadius C :=
  div_pos (lt_min (sub_pos.mpr C.densityLower_lt_one) (sub_pos.mpr C.one_lt_densityUpper))
    (by norm_num)

theorem highCenterRadius_le_margins  :
    2 * highCenterRadius C ≤ 1 - C.densityLower ∧
      2 * highCenterRadius C ≤ C.densityUpper - 1 := by
  dsimp [highCenterRadius]
  grind

theorem highCenterMix_mem  :
    0 < highCenterMix C ∧ highCenterMix C < 1 := by
  have hgap : 0 < C.densityUpper - C.densityLower := by
    linarith [C.densityLower_lt_one, C.one_lt_densityUpper]
  have hr := highCenterRadius_pos C
  have hm := highCenterRadius_le_margins C
  constructor
  · exact div_pos hr (mul_pos (by norm_num) hgap)
  · apply (div_lt_iff₀ (mul_pos (by norm_num) hgap)).mpr
    nlinarith
end


def balancedResetAnchor (δ q : ℝ) : ℝ := (1 - δ * q) / (1 - δ)

theorem balancedResetAnchor_identity δ q (hδ : δ < 1) :
    δ * q + (1 - δ) * balancedResetAnchor δ q = 1 := by
  unfold balancedResetAnchor
  grind

section
variable (a b r W δ q : ℝ) (hr : 0 < r) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (ha : a + r ≤ 1) (hb : 1 + r ≤ b) (hW : b - a ≤ W) (hδW : δ * W ≤ r / 2) (hq : q ∈ Icc a b)
include hr hδ0 hδ1 ha hb hW hδW hq

theorem balancedResetAnchor_margins  :
    (1 - δ) * (balancedResetAnchor δ q - a) ≥ r / 2 ∧
      (1 - δ) * (b - balancedResetAnchor δ q) ≥ r / 2 := by
  have hi := balancedResetAnchor_identity δ q hδ1
  have hl : δ * (q - a) ≤ δ * W := mul_le_mul_of_nonneg_left (by linarith [hq.2]) hδ0
  have hu : δ * (b - q) ≤ δ * W := mul_le_mul_of_nonneg_left (by linarith [hq.1]) hδ0
  constructor <;> nlinarith

theorem balancedResetAnchor_mem  :
    balancedResetAnchor δ q ∈ Icc a b := by
  have hm := balancedResetAnchor_margins a b r W δ q hr hδ0 hδ1 ha hb hW hδW hq
  
  constructor <;> nlinarith
end


/-- The manuscript's mixing constant is uniform in M. -/
theorem sourceBalancedResetAnchor_mem {d } (C : ModelConstants d)
    M q (hM : 0 < M) (hmargin : 1 / M ≤ highCenterRadius C)
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
  · linarith [hm.1]
  · linarith [hm.2]
  · linarith [one_div_pos.mpr hM]
  · dsimp [highCenterMix]
    field_simp
    linarith
  · exact hq

section
variable {E : Type*}

def balancedReferenceLaw  [MeasurableSpace E] (μ : Measure E) (δ : ℝ) :
    Measure (E ⊕ Unit) :=
  ENNReal.ofReal δ • μ.map Sum.inl + ENNReal.ofReal (1 - δ) • Measure.dirac (Sum.inr ())

theorem balancedReferenceLaw_probability  [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    IsProbabilityMeasure (balancedReferenceLaw μ δ) := by
  constructor
  rw [balancedReferenceLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply measurable_inl MeasurableSet.univ]
  simp only [preimage_univ, measure_univ, Measure.dirac_apply_of_mem (mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hδ0 (sub_nonneg.mpr hδ1)]
  simp

def balancedIntercept  (B : E → ℝ) (δ q : ℝ) : E ⊕ Unit → ℝ :=
  Sum.elim B (fun _ => balancedResetAnchor δ q)

def balancedSlope  (A : E → ℝ) : E ⊕ Unit → ℝ := Sum.elim A (fun _ => 0)

def balancedActivation  (w : E → ℝ) (δ : ℝ) : E ⊕ Unit → ℝ :=
  Sum.elim (fun e => w e / δ) (fun _ => 0)

section
variable [MeasurableSpace E] (μ : Measure E) (δ : ℝ)

theorem balancedReferenceLaw_integrable   (F : E ⊕ Unit → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun e => F (Sum.inl e)) μ) :
    Integrable F (balancedReferenceLaw μ δ) := by
  have hm  :=
    (integrable_map_measure hF.aestronglyMeasurable measurable_inl.aemeasurable).mpr hFi
  have hd : Integrable F (Measure.dirac (Sum.inr ())) :=
    integrable_dirac' hF.stronglyMeasurable (by finiteness)
  exact integrable_add_measure.mpr ⟨hm.smul_measure ENNReal.ofReal_ne_top,
    hd.smul_measure ENNReal.ofReal_ne_top⟩

theorem balancedReferenceLaw_integral   (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (F : E ⊕ Unit → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun e => F (Sum.inl e)) μ) :
    ∫ e, F e ∂balancedReferenceLaw μ δ =
      δ * (∫ e, F (Sum.inl e) ∂μ) + (1 - δ) * F (Sum.inr ()) := by
  have hm  :=
    (integrable_map_measure hF.aestronglyMeasurable measurable_inl.aemeasurable).mpr hFi
  have hd : Integrable F (Measure.dirac (Sum.inr ())) :=
    integrable_dirac' hF.stronglyMeasurable (by finiteness)
  rw [balancedReferenceLaw, integral_add_measure
    (hm.smul_measure ENNReal.ofReal_ne_top) (hd.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    integral_map measurable_inl.aemeasurable hF.aestronglyMeasurable,
    integral_dirac' _ _ hF.stronglyMeasurable,
    ENNReal.toReal_ofReal hδ0, ENNReal.toReal_ofReal (sub_nonneg.mpr hδ1)]
  rfl
end


theorem balancedIntercept_measurable  [MeasurableSpace E]
    (B : E → ℝ) (hB : Measurable B) (δ q : ℝ) : Measurable (balancedIntercept B δ q) :=
  hB.sumElim measurable_const

theorem balancedSlope_measurable  [MeasurableSpace E]
    (A : E → ℝ) (hA : Measurable A) : Measurable (balancedSlope A) :=
  hA.sumElim measurable_const

theorem balancedActivation_measurable  [MeasurableSpace E]
    (w : E → ℝ) (hw : Measurable w) (δ : ℝ) : Measurable (balancedActivation w δ) :=
  (hw.div_const δ).sumElim measurable_const

section
variable [MeasurableSpace E] (μ : Measure E) (δ : ℝ) (hδ0 : 0 ≤ δ)
include hδ0

theorem balancedIntercept_integral_one   (hδ1 : δ < 1)
    (B : E → ℝ) (hB : Measurable B) (hBi : Integrable B μ) :
    ∫ e, balancedIntercept B δ (∫ e, B e ∂μ) e ∂balancedReferenceLaw μ δ = 1 := by
  rw [balancedReferenceLaw_integral μ δ hδ0 hδ1.le _
    (balancedIntercept_measurable B hB _ _) hBi]
  exact balancedResetAnchor_identity δ _ hδ1

theorem balancedSlope_integral_zero   (hδ1 : δ ≤ 1)
    (A : E → ℝ) (hA : Measurable A) (hAi : Integrable A μ) (hcenter : ∫ e, A e ∂μ = 0) :
    ∫ e, balancedSlope A e ∂balancedReferenceLaw μ δ = 0 := by
  rw [balancedReferenceLaw_integral μ δ hδ0 hδ1 _ (balancedSlope_measurable A hA) hAi]
  simp only [balancedSlope, Sum.elim_inl, Sum.elim_inr, hcenter, mul_zero, add_zero]
end


theorem balancedActivation_bound  (w : E → ℝ) (δ W : ℝ) (hδ : 0 < δ) (hW0 : 0 ≤ W)
    (hW : ∀ e, |w e| ≤ W) (e : E ⊕ Unit) : |balancedActivation w δ e| ≤ W / δ := by
  cases e with
  | inl e =>
    change |w e / δ| ≤ _
    rw [abs_div, abs_of_pos hδ]
    exact div_le_div_of_nonneg_right (hW e) hδ.le
  | inr e =>
    change |(0 : ℝ)| ≤ _
    simpa only [abs_zero] using div_nonneg hW0 hδ.le

section
variable [MeasurableSpace E] (μ : Measure E)

section
variable (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (w : E → ℝ) (hw : Measurable w)
include hδ hδ1 hw

theorem balancedActivation_integral    (F : E ⊕ Unit → ℝ) (hF : Measurable F)
    (hWF : Integrable (fun e => w e * F (Sum.inl e)) μ) :
    ∫ e, balancedActivation w δ e * F e ∂balancedReferenceLaw μ δ =
      ∫ e, w e * F (Sum.inl e) ∂μ := by
  have hFi : Integrable (fun e => balancedActivation w δ (Sum.inl e) * F (Sum.inl e)) μ := by
    convert hWF.div_const δ using 1
    funext e
    change w e / δ * F (Sum.inl e) = w e * F (Sum.inl e) / δ
    ring
  rw [balancedReferenceLaw_integral μ δ hδ.le hδ1 (fun e => balancedActivation w δ e * F e)
    ((balancedActivation_measurable w hw δ).mul hF) hFi]
  simp only [balancedActivation, Sum.elim_inl, Sum.elim_inr, zero_mul, mul_zero, add_zero]
  have he : (fun e => w e / δ * F (Sum.inl e)) =
      (fun e => (w e * F (Sum.inl e)) / δ) := by funext e; ring
  rw [he, integral_div]
  field_simp

theorem balancedActivation_integral_zero    (hwi : Integrable w μ) (hc : ∫ e, w e ∂μ = 0) :
    ∫ e, balancedActivation w δ e ∂balancedReferenceLaw μ δ = 0 := by
  have hh := balancedActivation_integral μ δ hδ hδ1 w hw (fun _ => 1) measurable_const
    (by simpa only [mul_one] using hwi)
  simpa only [mul_one, hc] using hh
end


theorem boundedIntercept_integrable   [IsFiniteMeasure μ] (B : E → ℝ) (hB : Measurable B)
    (a b : ℝ) (hb : ∀ e, B e ∈ Icc a b) : Integrable B μ := by
  apply (integrable_const (max |a| |b|)).mono' hB.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  rw [Real.norm_eq_abs]
  grind

theorem boundedIntercept_mean_mem   [IsProbabilityMeasure μ] (B : E → ℝ) (hB : Measurable B)
    (a b : ℝ) (hb : ∀ e, B e ∈ Icc a b) : (∫ e, B e ∂μ) ∈ Icc a b := by
  have hBi := boundedIntercept_integrable μ B hB a b hb
  constructor
  · have hh := integral_mono (integrable_const a) hBi (fun e => (hb e).1)
    simp_all
  · have hh := integral_mono hBi (integrable_const b) (fun e => (hb e).2)
    simp_all
end

end


end NearlyMinimax
