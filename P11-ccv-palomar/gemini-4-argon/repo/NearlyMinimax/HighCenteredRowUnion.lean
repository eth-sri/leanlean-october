module
public import NearlyMinimax.ActualSeparatedPacket
public import NearlyMinimax.HistoryPriorDensity
public import NearlyMinimax.HighWindowGeometry
public import NearlyMinimax.HighFrameCoefficientBridge
@[expose] public section
noncomputable section
open MeasureTheory Set Function ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section AbsoluteMark
variable {E : Type*} [MeasurableSpace E]
def signedMarkMass (μ : Measure E) (w : E → ℝ) : ℝ := ∫ e, |w e| ∂μ
def absoluteMarkLaw (μ : Measure E) (w : E → ℝ) : Measure E :=
  μ.withDensity (fun e => ENNReal.ofReal (|w e| / signedMarkMass μ w))
def absoluteActivation (μ : Measure E) (w : E → ℝ) (e : E) : ℝ :=
  signedMarkMass μ w * (w e / |w e|)
theorem signedMarkMass_nonneg (μ : Measure E) (w : E → ℝ) :
    0 ≤ signedMarkMass μ w := integral_nonneg (fun _ => abs_nonneg _)
theorem signedMarkMass_eq_variation (μ : Measure E) (w ) (hw : Integrable w μ) :
    signedMarkMass μ w = ((μ.withDensityᵥ w).variation univ).toReal := by
  rw [Measure.variation_withDensityᵥ hw, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable]
  simp only [signedMarkMass, Real.norm_eq_abs]
theorem absoluteMarkLaw_probability (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (hpos : 0 < signedMarkMass μ w) :
    IsProbabilityMeasure (absoluteMarkLaw μ w) := by
  constructor
  rw [absoluteMarkLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hw.abs.div_const _)
      (Filter.Eventually.of_forall (fun e => div_nonneg (abs_nonneg (w e)) hpos.le)),
    integral_div]
  change ENNReal.ofReal (signedMarkMass μ w / signedMarkMass μ w) = 1
  simp only [div_self hpos.ne', ENNReal.ofReal_one]
theorem absoluteActivation_measurable (μ : Measure E) (w : E → ℝ) (hw : Measurable w) :
    Measurable (absoluteActivation μ w) :=
  (hw.div hw.abs).const_mul _
theorem absoluteActivation_bound (μ : Measure E) (w : E → ℝ) (e : E) :
    |absoluteActivation μ w e| ≤ signedMarkMass μ w := by
  rw [absoluteActivation, abs_mul, abs_of_nonneg (signedMarkMass_nonneg μ w)]
  have hb : |w e / (|w e|)| ≤ 1 := by
    by_cases he : w e = 0
    · simp [he]
    · rw [abs_div, abs_abs, div_self (abs_ne_zero.mpr he)]
  exact (mul_le_mul_of_nonneg_left hb (signedMarkMass_nonneg μ w)).trans_eq (mul_one _)
theorem absoluteMarkLaw_activation_integral (μ w)
    (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w) (F : E → ℝ) :
    (∫ e, absoluteActivation μ w e * F e ∂absoluteMarkLaw μ w) =
      ∫ e, w e * F e ∂μ := by
  rw [absoluteMarkLaw, integral_withDensity_eq_integral_toReal_smul
    (hmw.abs.div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro e
  dsimp only
  rw [ENNReal.toReal_ofReal (div_nonneg (abs_nonneg (w e)) hpos.le), smul_eq_mul,
    absoluteActivation]
  by_cases he : w e = 0
  · simp [he]
  · field_simp
theorem absoluteActivation_centered (μ : Measure E) (w : E → ℝ)
    (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w)
    (hzero : ∫ e, w e ∂μ = 0) :
    (∫ e, absoluteActivation μ w e ∂absoluteMarkLaw μ w) = 0 := by
  have h := absoluteMarkLaw_activation_integral μ w hmw hpos (fun _ => 1)
  simp only [mul_one] at h
  exact h.trans hzero
theorem absoluteMarkLaw_signed_action (μ : Measure E) (w )
    (hw : Integrable w μ) (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w)
    (F ) (hF : Measurable F) (M : ℝ) (hbound : ∀ e, ‖F e‖ ≤ M) :
    (∫ e, absoluteActivation μ w e * F e ∂absoluteMarkLaw μ w) =
      ∫ᵛ e, F e ∂<•(μ.withDensityᵥ w) := by
  rw [absoluteMarkLaw_activation_integral μ w hmw hpos F,
    signedDensity_integral μ w hw hmw F hF M hbound]
end AbsoluteMark
section History
variable {E J : Type*} [MeasurableSpace E] [Fintype J] [LinearOrder J]
end History
section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
def highPacketMarkMass (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : ℝ :=
  signedMarkMass (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)
def highPacketAbsoluteLaw (σ : Measure Z) (a b : ℝ) (m r D q ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Measure (Z × HighPacketMarkIndex ι m r D q) :=
  absoluteMarkLaw (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)
def highPacketActivation (σ : Measure Z) (a b : ℝ) (m r D q ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Z × HighPacketMarkIndex ι m r D q → ℝ :=
  absoluteActivation (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)
theorem highPacketMarkMass_eq_variation (σ ) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    highPacketMarkMass σ a b m r D q C A =
      ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal :=
  signedMarkMass_eq_variation _ _ (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost)
theorem highPacketAbsoluteLaw_probability (σ ) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A) :
    IsProbabilityMeasure (highPacketAbsoluteLaw σ a b m r D q C A) :=
  absoluteMarkLaw_probability _ _ (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost) hpos
theorem highPacketActivation_centered (σ ) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A) :
    (∫ e, highPacketActivation σ a b m r D q C A e
      ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 :=
  have h_highPacketMarkWeight_integral_zero : (∫ e, highPacketMarkWeight a b m r D q C A e ∂σ.prod Measure.count) = 0 := by
    have h_highPacketSignedMeasure_zero_mass : highPacketSignedMeasure σ a b m r D q C A univ = 0 := by
      have hw := highPacketMarkWeight_integrable σ a b m r D q C A hA hcost
      rw [highPacketSignedMeasure, withDensityᵥ_apply hw MeasurableSet.univ, Measure.restrict_univ,
        integral_prod _ hw]
      simp only [integral_count]
      have hz (ζ : Z) : (∑ h : HighPacketMarkIndex ι m r D q,
          highPacketMarkWeight a b m r D q C A (ζ, h)) = 0 := by
        have h := highPacketObservable_finite_action a b m r D q C A (fun _ => 0)
          (fun _ _ _ => 1) (fun _ => 1) ζ
        have h_densityPacketAction_zero : densityPacketAction a b m r D (fun _ _ => 0) = 0 := by
          simp [densityPacketAction, densityDerivativeAction]
        simpa only [highPacketObservable, mul_one, mul_zero, responseMatrixAction_zero_mass,
          h_densityPacketAction_zero] using h
      simp only [hz, integral_zero]
    have h := h_highPacketSignedMeasure_zero_mass
    rw [highPacketSignedMeasure, withDensityᵥ_apply
      (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost) MeasurableSet.univ,
      Measure.restrict_univ] at h
    exact h
  absoluteActivation_centered _ _ (highPacketMarkWeight_measurable a b m r D q C A hA)
    hpos h_highPacketMarkWeight_integral_zero
theorem highPacketActivation_bound (σ a b m r D q C)
    (A : Z → ι → ι → ℝ) (e : Z × HighPacketMarkIndex ι m r D q) :
    |highPacketActivation σ a b m r D q C A e| ≤ highPacketMarkMass σ a b m r D q C A :=
  absoluteActivation_bound _ _ _
end Packet
abbrev HighRawState (d k D : ℕ) :=
  (Covariate d → ℝ) × (HighWindowLabels d k → (HighFrameIndex d D → ℝ))
def highCenterRadius  (C : ModelConstants d) : ℝ :=
  min (1 - C.densityLower) (C.densityUpper - 1) / 2
def highCenterMix  (C : ModelConstants d) : ℝ :=
  highCenterRadius C / (2 * (C.densityUpper - C.densityLower))
theorem highCenterRadius_pos  (C : ModelConstants d) : 0 < highCenterRadius C :=
  div_pos (lt_min (sub_pos.mpr C.densityLower_lt_one) (sub_pos.mpr C.one_lt_densityUpper))
    (by norm_num)
theorem highCenterRadius_le_margins  (C : ModelConstants d) :
    2 * highCenterRadius C ≤ 1 - C.densityLower ∧
      2 * highCenterRadius C ≤ C.densityUpper - 1 := by
  dsimp [highCenterRadius]
  constructor <;> linarith [min_le_left (1 - C.densityLower) (C.densityUpper - 1),
    min_le_right (1 - C.densityLower) (C.densityUpper - 1)]
theorem highCenterMix_mem  (C : ModelConstants d) :
    0 < highCenterMix C ∧ highCenterMix C < 1 := by
  have hgap : 0 < C.densityUpper - C.densityLower := by
    linarith [C.densityLower_lt_one, C.one_lt_densityUpper]
  have := highCenterRadius_le_margins C
  constructor
  · exact div_pos (highCenterRadius_pos C) (mul_pos (by norm_num) hgap)
  · apply (div_lt_iff₀ (mul_pos (by norm_num) hgap)).mpr
    nlinarith
def balancedResetAnchor (δ q : ℝ) : ℝ := (1 - δ * q) / (1 - δ)
theorem balancedResetAnchor_identity (δ q ) (hδ : δ < 1) :
    δ * q + (1 - δ) * balancedResetAnchor δ q = 1 := by
  unfold balancedResetAnchor
  field_simp [show 1 - δ ≠ 0 from (sub_pos.mpr hδ).ne']
  ring
theorem balancedResetAnchor_mem (a b r W δ q ) (hr : 0 < r)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (ha : a + r ≤ 1) (hb : 1 + r ≤ b)
    (hW : b - a ≤ W) (hδW : δ * W ≤ r / 2) (hq : q ∈ Icc a b) :
    balancedResetAnchor δ q ∈ Icc a b := by
  have h_balancedResetAnchor_margins : (1 - δ) * (balancedResetAnchor δ q - a) ≥ r / 2 ∧
      (1 - δ) * (b - balancedResetAnchor δ q) ≥ r / 2 := by
    have := balancedResetAnchor_identity δ q hδ1
    have : δ * (q - a) ≤ δ * W := mul_le_mul_of_nonneg_left (by linarith [hq.2]) hδ0
    have : δ * (b - q) ≤ δ * W := mul_le_mul_of_nonneg_left (by linarith [hq.1]) hδ0
    constructor <;> nlinarith
  have := h_balancedResetAnchor_margins
  have  := sub_pos.mpr hδ1
  constructor <;> nlinarith
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
theorem balancedReferenceLaw_integrable  [MeasurableSpace E]
    (μ : Measure E) (δ : ℝ) (F : E ⊕ Unit → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun e => F (Sum.inl e)) μ) :
    Integrable F (balancedReferenceLaw μ δ) := by
  exact integrable_add_measure.mpr ⟨((integrable_map_measure hF.aestronglyMeasurable measurable_inl.aemeasurable).mpr hFi).smul_measure ENNReal.ofReal_ne_top,
    (integrable_dirac' hF.stronglyMeasurable (by finiteness)).smul_measure ENNReal.ofReal_ne_top⟩
theorem balancedReferenceLaw_integral  [MeasurableSpace E]
    (μ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (F : E ⊕ Unit → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun e => F (Sum.inl e)) μ) :
    ∫ e, F e ∂balancedReferenceLaw μ δ =
      δ * (∫ e, F (Sum.inl e) ∂μ) + (1 - δ) * F (Sum.inr ()) := by
  rw [balancedReferenceLaw, integral_add_measure
    (((integrable_map_measure hF.aestronglyMeasurable measurable_inl.aemeasurable).mpr hFi).smul_measure ENNReal.ofReal_ne_top) ((integrable_dirac' hF.stronglyMeasurable (by finiteness)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    integral_map measurable_inl.aemeasurable hF.aestronglyMeasurable,
    integral_dirac' _ _ hF.stronglyMeasurable,
    ENNReal.toReal_ofReal hδ0, ENNReal.toReal_ofReal (sub_nonneg.mpr hδ1)]
  rfl
theorem balancedIntercept_measurable  [MeasurableSpace E]
    (B : E → ℝ) (hB : Measurable B) (δ q : ℝ) : Measurable (balancedIntercept B δ q) :=
  hB.sumElim measurable_const
theorem balancedSlope_measurable  [MeasurableSpace E]
    (A : E → ℝ) (hA : Measurable A) : Measurable (balancedSlope A) :=
  hA.sumElim measurable_const
theorem balancedActivation_measurable  [MeasurableSpace E]
    (w : E → ℝ) (hw : Measurable w) (δ : ℝ) : Measurable (balancedActivation w δ) :=
  (hw.div_const δ).sumElim measurable_const
theorem balancedActivation_bound {E : Type*} (w : E → ℝ) (δ W : ℝ) (hδ : 0 < δ) (hW0 : 0 ≤ W)
    (hW : ∀ e, |w e| ≤ W) (e : E ⊕ Unit) : |balancedActivation w δ e| ≤ W / δ := by
  cases e with
  | inl e =>
    change |w e / δ| ≤ _
    rw [abs_div, abs_of_pos hδ]
    exact div_le_div_of_nonneg_right (hW e) hδ.le
  | inr e =>
    change |0| ≤ _
    simpa only [abs_zero] using div_nonneg hW0 hδ.le
theorem balancedActivation_integral  [MeasurableSpace E]
    (μ δ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (w : E → ℝ) (hw : Measurable w) (F : E ⊕ Unit → ℝ) (hF : Measurable F)
    (hWF : Integrable (fun e => w e * F (Sum.inl e)) μ) :
    ∫ e, balancedActivation w δ e * F e ∂balancedReferenceLaw μ δ =
      ∫ e, w e * F (Sum.inl e) ∂μ := by
  rw [balancedReferenceLaw_integral μ δ hδ.le hδ1 (fun e => balancedActivation w δ e * F e)
    ((balancedActivation_measurable w hw δ).mul hF) (by convert hWF.div_const δ using 1; funext e; change w e / δ * F (Sum.inl e) = w e * F (Sum.inl e) / δ; ring)]
  simp only [balancedActivation, Sum.elim_inl, Sum.elim_inr, zero_mul, mul_zero, add_zero]
  have he : (fun e => w e / δ * F (Sum.inl e)) =
      (fun e => (w e * F (Sum.inl e)) / δ) := by funext e; ring
  rw [he, integral_div]
  field_simp
theorem boundedIntercept_integrable  [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (B : E → ℝ) (hB : Measurable B)
    (a b : ℝ) (hb : ∀ e, B e ∈ Icc a b) : Integrable B μ := by
  apply (integrable_const (max |a| |b|)).mono' hB.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have  := neg_abs_le a
    linarith [le_max_left |a| |b|, (hb e).1]
  · exact (hb e).2.trans ((le_abs_self b).trans (le_max_right _ _))
theorem boundedIntercept_mean_mem  [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (B : E → ℝ) (hB : Measurable B)
    (a b : ℝ) (hb : ∀ e, B e ∈ Icc a b) : (∫ e, B e ∂μ) ∈ Icc a b := by
  have hBi := boundedIntercept_integrable μ B hB a b hb
  constructor
  · have hh := integral_mono (integrable_const a) hBi (fun e => (hb e).1)
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh
  · have hh := integral_mono hBi (integrable_const b) (fun e => (hb e).2)
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh
theorem balancedIntercept_integral_one  [MeasurableSpace E]
    (μ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (B : E → ℝ) (hB : Measurable B) (hBi : Integrable B μ) :
    ∫ e, balancedIntercept B δ (∫ e, B e ∂μ) e ∂balancedReferenceLaw μ δ = 1 := by
  rw [balancedReferenceLaw_integral μ δ hδ0 hδ1.le _
    (balancedIntercept_measurable B hB _ _) hBi]
  exact balancedResetAnchor_identity δ _ hδ1
theorem finite_even_odd_sum_zero  [Fintype I]
    (e : Equiv.Perm I) (w f : I → ℝ)
    (hw : ∀ i, w (e i) = w i) (hf : ∀ i, f (e i) = -f i) :
    (∑ i, w i * f i) = 0 := by
  have : (∑ i, w i * f i) = -(∑ i, w i * f i) := by
    calc
      _ = ∑ i, w (e i) * f (e i) := by
        symm
        apply Fintype.sum_equiv e
        intro i
        rfl
      _ = ∑ i, -(w i * f i) := by simp_rw [hw, hf, mul_neg]
      _ = _ := Finset.sum_neg_distrib _
  linarith
def densityMarkReflection (m r D ) : Equiv.Perm (HighDensityMarkIndex m r D) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight (fun _ => Fin.revPerm))
def packetMarkReflection (ι m r D q) : Equiv.Perm (HighPacketMarkIndex ι m r D q) :=
  Equiv.prodCongr (densityMarkReflection m r D) (Equiv.refl _)
theorem densityPacketWeight_abs_reflection (a b m r D h) :
    |densityPacketWeight a b m r D (densityMarkReflection m r D h)| =
      |densityPacketWeight a b m r D h| := by
  change |densityPacketPrefactor a b r * exteriorWeight a b (m + r) h.1 *
      (∏ l, densityDerivativeWeight D (h.2 l).rev)| = _
  simp only [densityPacketWeight, abs_mul, Finset.abs_prod]
  have hp : (∏ l, |densityDerivativeWeight D (h.2 l).rev|) =
      ∏ l, |densityDerivativeWeight D (h.2 l)| := by
    apply Finset.prod_congr rfl
    intro l hl
    exact lobattoDerivativeWeight_abs_reflection ((D - 1) / 2) (h.2 l)
  rw [hp]
section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
def highPacketIntercept (a b : ℝ) (m r D q )
    (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  (densityPacketAtom a b m r D e.2.1).1
def highPacketSlope (a b : ℝ) (m r D q ) (B : Z → Fin r → ℝ)
    (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  densityMargin a b (highPacketIntercept a b m r D q e) / (r * b) *
    ∑ l, (densityPacketAtom a b m r D e.2.1).2 l * B e.1 l
theorem highPacketIntercept_measurable (a b m r D q) :
    Measurable (highPacketIntercept (Z := Z) (ι := ι) a b m r D q) := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable (fun _ => (densityPacketAtom a b m r D h.1).1)
  exact measurable_const
theorem highPacketSlope_measurable (a b : ℝ) (m r D q : ℕ) (B : Z → Fin r → ℝ)
    (hB : ∀ l, Measurable (fun ζ => B ζ l)) :
    Measurable (highPacketSlope (ι := ι) a b m r D q B) := by
  apply measurable_from_prod_countable_left
  intro h
  unfold highPacketSlope highPacketIntercept
  dsimp only
  apply Measurable.const_mul
  exact Finset.measurable_fun_sum _ (fun l _ => (hB l).const_mul _)
theorem highPacketSlope_bound (a b ) (ha : 0 < a) (hab : a < b)
    (m r D q : ℕ) (hr : 1 ≤ r) (B : Z → Fin r → ℝ) (hB : ∀ ζ l, |B ζ l| ≤ 1)
    (e : Z × HighPacketMarkIndex ι m r D q) :
    |highPacketSlope a b m r D q B e| ≤ (b - a) / (4 * b) :=
  localDensityReset_slope_bound a b ha hab r hr
    (densityPacketAtom a b m r D e.2.1).1
    (densityPacketAtom_mem a b hab.le m r D e.2.1).1
    (densityPacketAtom a b m r D e.2.1).2
    (densityPacketAtom_mem a b hab.le m r D e.2.1).2
    (fun _ l => B e.1 l) () (hB e.1)
theorem highPacketMarkWeight_abs_reflection (a b m r D q C)
    (A : Z → ι → ι → ℝ) (ζ : Z) (h : HighPacketMarkIndex ι m r D q) :
    |highPacketMarkWeight a b m r D q C A (ζ, packetMarkReflection ι m r D q h)| =
      |highPacketMarkWeight a b m r D q C A (ζ, h)| := by
  change |densityPacketWeight a b m r D (densityMarkReflection m r D h.1) *
      highResponseMarkWeight C q (A ζ) h.2| = _
  rw [abs_mul, densityPacketWeight_abs_reflection, highPacketMarkWeight, abs_mul]
theorem highPacketSlope_absolute_finite_sum_zero (a b m r D q C)
    (A : Z → ι → ι → ℝ) (B : Z → Fin r → ℝ) (ζ : Z) :
    (∑ h : HighPacketMarkIndex ι m r D q,
      |highPacketMarkWeight a b m r D q C A (ζ, h)| * highPacketSlope a b m r D q B (ζ, h)) = 0 :=
  have h_highPacketSlope_reflection {Z} {ι} (B : Z → Fin r → ℝ) (ζ : Z) (h : HighPacketMarkIndex ι m r D q) : highPacketSlope a b m r D q B (ζ, packetMarkReflection ι m r D q h) =
      -highPacketSlope a b m r D q B (ζ, h) := by
    change densityMargin a b (exteriorNode a b (m + r) h.1.1) / (↑r * b) *
        (∑ l, lobattoNode (derivativeOrder D) (h.1.2 l).rev * B ζ l) = _
    simp_rw [lobattoNode_reflection (derivativeOrder D) (by unfold derivativeOrder; omega)]
    simp only [neg_mul, Finset.sum_neg_distrib, mul_neg]
    rfl
  finite_even_odd_sum_zero (packetMarkReflection ι m r D q) _ _
    (highPacketMarkWeight_abs_reflection a b m r D q C A ζ)
    (h_highPacketSlope_reflection B ζ)
theorem absoluteMarkLaw_integral  [MeasurableSpace E]
    (μ w) (hmw : Measurable w)
    (hpos : 0 < signedMarkMass μ w) (F : E → ℝ) :
    (∫ e, F e ∂absoluteMarkLaw μ w) = (∫ e, |w e| * F e ∂μ) / signedMarkMass μ w := by
  rw [absoluteMarkLaw, integral_withDensity_eq_integral_toReal_smul
    (hmw.abs.div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he : (fun e => (ENNReal.ofReal (|w e| / signedMarkMass μ w)).toReal • F e) =
      (fun e => (|w e| * F e) / signedMarkMass μ w) := by
    funext e
    rw [ENNReal.toReal_ofReal (div_nonneg (abs_nonneg (w e)) hpos.le), smul_eq_mul]
    exact div_mul_eq_mul_div _ _ _
  rw [he, integral_div]
theorem highPacketSlope_integrable (σ ) [IsFiniteMeasure σ]
    (a b ) (ha : 0 < a) (hab : a < b) (m r D q ) (hr : 1 ≤ r) (C )
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (B : Z → Fin r → ℝ) (hmB : ∀ l, Measurable (fun ζ => B ζ l))
    (hB : ∀ ζ l, |B ζ l| ≤ 1) :
    Integrable (highPacketSlope a b m r D q B) (highPacketAbsoluteLaw σ a b m r D q C A) := by
  letI := highPacketAbsoluteLaw_probability σ a b m r D q C A hA hcost hpos
  apply (integrable_const ((b - a) / (4 * b))).mono'
    (highPacketSlope_measurable a b m r D q B hmB).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun e => by
    simpa only [Real.norm_eq_abs] using highPacketSlope_bound a b ha hab m r D q hr B hB e)
theorem highPacketAbsoluteLaw_slope_integral_zero (σ ) [IsFiniteMeasure σ]
    (a b ) (ha : 0 < a) (hab : a < b) (m r D q ) (hr : 1 ≤ r) (C )
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (B : Z → Fin r → ℝ) (hmB : ∀ l, Measurable (fun ζ => B ζ l))
    (hB : ∀ ζ l, |B ζ l| ≤ 1) :
    (∫ e, highPacketSlope a b m r D q B e ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 := by
  have hi := (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost).abs.mul_bdd
    (highPacketSlope_measurable a b m r D q B hmB).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      simpa only [Real.norm_eq_abs] using highPacketSlope_bound a b ha hab m r D q hr B hB e))
  rw [highPacketAbsoluteLaw, absoluteMarkLaw_integral _ _
    (highPacketMarkWeight_measurable a b m r D q C A hA) hpos,
    integral_prod _ hi]
  simp only [integral_count, highPacketSlope_absolute_finite_sum_zero, integral_zero, zero_div]
end Packet
section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (m r D q : ℕ) (C δ : ℝ)
  (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
  (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
include hA hcost hpos
end Packet
def highCenterResolutionThreshold  (C : ModelConstants d) : ℝ :=
  max 2 (highCenterRadius C)⁻¹
theorem highCenterResolution_guards {d : ℕ} (C : ModelConstants d) (M : ℝ)
    (hM : highCenterResolutionThreshold C ≤ M) : 2 ≤ M ∧ 1 / M ≤ highCenterRadius C := by
  have hM2  := (le_max_left _ _).trans hM
  have hM0 : 0 < M := by linarith
  refine ⟨hM2, ?_⟩
  apply (div_le_iff₀ hM0).mpr
  have hh := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hM) (highCenterRadius_pos C).le
  rw [mul_inv_cancel₀ (highCenterRadius_pos C).ne'] at hh
  nlinarith
section
variable {J : Type*} [Fintype J] {E : J → Type*} [∀ j, MeasurableSpace (E j)]
theorem rowSigmaMk_measurable (j ) : Measurable (@Sigma.mk J E j) := by
  apply Measurable.of_le_map
  exact iInf_le _ j
theorem rowSigmaFunction_measurable (F : (j : J) → E j → ℝ)
    (hF : ∀ j, Measurable (F j)) : Measurable (fun e : Sigma E => F e.1 e.2) := by
  intro s hs
  change MeasurableSet[⨅ j, MeasurableSpace.map (Sigma.mk j)
    (inferInstance : MeasurableSpace (E j))] ((fun e : Sigma E => F e.1 e.2) ⁻¹' s)
  rw [MeasurableSpace.measurableSet_iInf]
  exact fun j => hF j hs
def highRowTotalMass (B : J → ℝ) : ℝ := ∑ j, B j
def highRowSelectionProbability (B : J → ℝ) (j : J) : ℝ := B j / highRowTotalMass B
theorem highRowSelectionProbability_nonneg (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (j : J) :
    0 ≤ highRowSelectionProbability B j :=
  div_nonneg (hB j) (Finset.sum_nonneg (fun j _ => hB j))
theorem highRowSelectionProbability_pos (B ) (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (j : J) : 0 < highRowSelectionProbability B j :=
  div_pos (hB j) hTotal
theorem highRowSelectionProbability_sum (B : J → ℝ) (hTotal : highRowTotalMass B ≠ 0) :
    (∑ j, highRowSelectionProbability B j) = 1 := by
  unfold highRowSelectionProbability
  rw [← Finset.sum_div]
  exact div_self hTotal
def highRowReferenceUnion (π : (j : J) → Measure (E j)) (B : J → ℝ) : Measure (Sigma E) :=
  ∑ j, ENNReal.ofReal (highRowSelectionProbability B j) • (π j).map (Sigma.mk j)
theorem highRowReferenceUnion_probability (π : (j : J) → Measure (E j))
    [∀ j, IsProbabilityMeasure (π j)] (B : J → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hTotal : 0 < highRowTotalMass B) : IsProbabilityMeasure (highRowReferenceUnion π B) := by
  constructor
  rw [highRowReferenceUnion, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.map_apply (rowSigmaMk_measurable _) MeasurableSet.univ,
    preimage_univ, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => highRowSelectionProbability_nonneg B hB j),
    highRowSelectionProbability_sum B hTotal.ne']
  norm_num
theorem highRowReferenceUnion_integrable (π B)
    (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => F ⟨j, e⟩) (π j)) :
    Integrable F (highRowReferenceUnion π B) := by
  apply integrable_finsetSum_measure.mpr
  intro j _
  have h := (integrable_map_measure hF.aestronglyMeasurable (rowSigmaMk_measurable j).aemeasurable).mpr
    (hInt j)
  exact h.smul_measure ENNReal.ofReal_ne_top
theorem highRowReferenceUnion_integral (π B)
    (hB : ∀ j, 0 ≤ B j) (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => F ⟨j, e⟩) (π j)) :
    (∫ e, F e ∂highRowReferenceUnion π B) =
      ∑ j, highRowSelectionProbability B j * ∫ e, F ⟨j, e⟩ ∂π j := by
  unfold highRowReferenceUnion
  rw [integral_finsetSum_measure (fun j _ =>
    ((integrable_map_measure hF.aestronglyMeasurable (rowSigmaMk_measurable j).aemeasurable).mpr
      (hInt j)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_smul_measure, integral_map (rowSigmaMk_measurable j).aemeasurable hF.aestronglyMeasurable,
    ENNReal.toReal_ofReal (highRowSelectionProbability_nonneg B hB j), smul_eq_mul]
def highRowUnionActivation (B : J → ℝ) (w : (j : J) → E j → ℝ) (e : Sigma E) : ℝ :=
  w e.1 e.2 / highRowSelectionProbability B e.1
theorem highRowUnionActivation_measurable (B : J → ℝ) (w : (j : J) → E j → ℝ)
    (hw : ∀ j, Measurable (w j)) : Measurable (highRowUnionActivation B w) :=
  rowSigmaFunction_measurable _ (fun j => (hw j).div_const _)
theorem highRowUnionActivation_integrable (π : (j : J) → Measure (E j))
    (B : J → ℝ) (w : (j : J) → E j → ℝ) (hw : ∀ j, Measurable (w j))
    (hInt : ∀ j, Integrable (w j) (π j)) :
    Integrable (highRowUnionActivation B w) (highRowReferenceUnion π B) :=
  highRowReferenceUnion_integrable π B _ (highRowUnionActivation_measurable B w hw)
    (fun j => by simpa only [highRowUnionActivation] using
      (hInt j).div_const (highRowSelectionProbability B j))
theorem highRowUnionActivation_centered (π )
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (w : (j : J) → E j → ℝ)
    (hw : ∀ j, Measurable (w j)) (hInt : ∀ j, Integrable (w j) (π j))
    (hCenter : ∀ j, (∫ e, w j e ∂π j) = 0) :
    (∫ e, highRowUnionActivation B w e ∂highRowReferenceUnion π B) = 0 := by
  rw [highRowReferenceUnion_integral π B hB _ (highRowUnionActivation_measurable B w hw)
    (fun j => by simpa only [highRowUnionActivation] using
      (hInt j).div_const (highRowSelectionProbability B j))]
  simp only [highRowUnionActivation, integral_div, hCenter, zero_div, mul_zero, Finset.sum_const_zero]
theorem highRowUnionActivation_action (π B) (hB : ∀ j, 0 < B j) (hTotal : 0 < highRowTotalMass B)
    (w ) (hw : ∀ j, Measurable (w j))
    (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => w j e * F ⟨j, e⟩) (π j)) :
    (∫ e, highRowUnionActivation B w e * F e ∂highRowReferenceUnion π B) =
      ∑ j, ∫ e, w j e * F ⟨j, e⟩ ∂π j := by
  have he (j : J) : (fun e : E j => highRowUnionActivation B w ⟨j,e⟩ * F ⟨j,e⟩) =
      (fun e => (w j e * F ⟨j,e⟩) / highRowSelectionProbability B j) := by
    funext e
    unfold highRowUnionActivation
    ring
  rw [highRowReferenceUnion_integral π B (fun j => (hB j).le)
    (fun e => highRowUnionActivation B w e * F e)
    ((highRowUnionActivation_measurable B w hw).mul hF)
    (fun j => by rw [he j]; exact (hInt j).div_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [he j, integral_div]
  exact mul_div_cancel₀ _ (highRowSelectionProbability_pos B hB hTotal j).ne'
theorem highRowReferenceUnion_integral_common_mean (π )
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B)
    (F : (j : J) → E j → ℝ) (hF : ∀ j, Measurable (F j))
    (hInt : ∀ j, Integrable (F j) (π j)) (m : ℝ)
    (hMean : ∀ j, (∫ e, F j e ∂π j) = m) :
    (∫ e : Sigma E, F e.1 e.2 ∂highRowReferenceUnion π B) = m := by
  rw [highRowReferenceUnion_integral π B hB _ (rowSigmaFunction_measurable F hF) hInt]
  simp only [hMean]
  rw [← Finset.sum_mul, highRowSelectionProbability_sum B hTotal.ne', one_mul]
end
section
variable {J : Type*} [Fintype J] {E : J → Type*} [∀ j, MeasurableSpace (E j)]
def highCenteredRowUnionLaw (π : (j : J) → Measure (E j)) (B : J → ℝ) (δ : ℝ) :
    Measure ((Sigma E) ⊕ Unit) := balancedReferenceLaw (highRowReferenceUnion π B) δ
def highCenteredRowUnionActivation (B : J → ℝ) (w : (j : J) → E j → ℝ) (δ : ℝ) :
    (Sigma E) ⊕ Unit → ℝ := balancedActivation (highRowUnionActivation B w) δ
def highCenteredRowUnionIntercept (π : (j : J) → Measure (E j)) (B : J → ℝ)
    (intercept : (j : J) → E j → ℝ) (δ : ℝ) : (Sigma E) ⊕ Unit → ℝ :=
  balancedIntercept (fun e => intercept e.1 e.2) δ
    (∫ e : Sigma E, intercept e.1 e.2 ∂highRowReferenceUnion π B)
def highCenteredRowUnionSlope (slope : (j : J) → E j → ℝ) : (Sigma E) ⊕ Unit → ℝ :=
  balancedSlope (fun e => slope e.1 e.2)
theorem highCenteredRowUnionActivation_bound (B ) (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (w : (j : J) → E j → ℝ)
    (hw : ∀ j e, |w j e| ≤ B j) (δ ) (hδ : 0 < δ) (e ) :
    |highCenteredRowUnionActivation B w δ e| ≤ highRowTotalMass B / δ := by
  apply balancedActivation_bound _ δ _ hδ hTotal.le
  intro e
  have h_highRowUnionActivation_bound : |highRowUnionActivation B w e| ≤ highRowTotalMass B / 1 := by
    have : 0 < 1 := by norm_num
    have hw : ∀ j e, |w j e| ≤ B j / 1 := by simpa only [div_one] using hw
    have hα := highRowSelectionProbability_pos B hB hTotal e.1
    unfold highRowUnionActivation
    rw [abs_div, abs_of_pos hα]
    apply (div_le_iff₀ hα).mpr
    have he : highRowTotalMass B / 1 * highRowSelectionProbability B e.1 = B e.1 / 1 := by
      unfold highRowSelectionProbability
      field_simp
    rw [he]
    exact hw e.1 e.2
  simpa only [div_one] using h_highRowUnionActivation_bound
theorem highCenteredRowUnionSlope_measurable (slope : (j : J) → E j → ℝ)
    (hSlope : ∀ j, Measurable (slope j)) : Measurable (highCenteredRowUnionSlope slope) :=
  balancedSlope_measurable _ (rowSigmaFunction_measurable slope hSlope)
theorem highCenteredRowUnionSlope_integral_zero (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B)
    (slope : (j : J) → E j → ℝ) (hSlope : ∀ j, Measurable (slope j))
    (hiSlope : ∀ j, Integrable (slope j) (π j))
    (hCenter : ∀ j, (∫ e, slope j e ∂π j) = 0)
    (δ ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (∫ e, highCenteredRowUnionSlope slope e ∂highCenteredRowUnionLaw π B δ) = 0 :=
  have h_balancedSlope_integral_zero {E} [MeasurableSpace E] (μ) (A : E → ℝ) (hA : Measurable A) (hAi : Integrable A μ) (hcenter : ∫ e, A e ∂μ = 0) : ∫ e, balancedSlope A e ∂balancedReferenceLaw μ δ = 0 := by
    rw [balancedReferenceLaw_integral μ δ hδ0 hδ1 _ (balancedSlope_measurable A hA) hAi]
    simp only [balancedSlope, Sum.elim_inl, Sum.elim_inr, hcenter, mul_zero, add_zero]
  (h_balancedSlope_integral_zero _ _ (rowSigmaFunction_measurable slope hSlope) (highRowReferenceUnion_integrable π B _ (rowSigmaFunction_measurable slope hSlope) hiSlope) (highRowReferenceUnion_integral_common_mean π B hB hTotal slope hSlope hiSlope 0 hCenter))
theorem highCenteredRowUnion_reset_source_legal  (C : ModelConstants d)
    (π ) [∀ j, IsProbabilityMeasure (π j)]
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B)
    (slope intercept : (j : J) → E j → ℝ) (hIntercept : ∀ j, Measurable (intercept j))
    (M ) (hM : highCenterResolutionThreshold C ≤ M)
    (hBound : ∀ j e, intercept j e ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M))
    (hlegal : ∀ j e p, p ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) →
      slope j e*p+intercept j e ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M))
    (e p)
    (hp : p ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M)) :
    highCenteredRowUnionSlope slope e*p+highCenteredRowUnionIntercept π B intercept (highCenterMix C) e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  cases e with
  | inl e => exact hlegal e.1 e.2 p hp
  | inr u =>
    have h_highCenteredRowUnionIntercept_source_interval : ∀ e, highCenteredRowUnionIntercept π B intercept (highCenterMix C) e ∈
        Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
      letI := highRowReferenceUnion_probability π B hB hTotal
      have hg := highCenterResolution_guards C M hM
      have hq := boundedIntercept_mean_mem (highRowReferenceUnion π B)
        (fun e => intercept e.1 e.2) (rowSigmaFunction_measurable intercept hIntercept)
        (C.densityLower+1/M) (C.densityUpper-1/M) (fun e => hBound e.1 e.2)
      intro e
      cases e with
      | inl e => exact hBound e.1 e.2
      | inr u =>
        have h_sourceBalancedResetAnchor_mem (q) (hM : 0 < M) (hmargin : 1 / M ≤ highCenterRadius C) (hq : q ∈ Icc (C.densityLower + 1 / M) (C.densityUpper - 1 / M)) : balancedResetAnchor (highCenterMix C) q ∈
            Icc (C.densityLower + 1 / M) (C.densityUpper - 1 / M) := by
          have hδ := highCenterMix_mem C
          have hm := highCenterRadius_le_margins C
          have : C.densityUpper - C.densityLower ≠ 0 := by
            linarith [C.densityLower_lt_one, C.one_lt_densityUpper]
          apply balancedResetAnchor_mem _ _ (highCenterRadius C)
            (C.densityUpper - C.densityLower) (highCenterMix C) q (highCenterRadius_pos C) hδ.1.le hδ.2
          · linarith [hm.1]
          · linarith [hm.2]
          · linarith [one_div_pos.mpr hM]
          · dsimp [highCenterMix]
            field_simp
            linarith
          · exact hq
        exact h_sourceBalancedResetAnchor_mem _ (by linarith) hg.2 hq
    simpa only [highCenteredRowUnionSlope, balancedSlope, Sum.elim_inr, zero_mul, zero_add]
      using h_highCenteredRowUnionIntercept_source_interval (Sum.inr u)
end
end NearlyMinimax
