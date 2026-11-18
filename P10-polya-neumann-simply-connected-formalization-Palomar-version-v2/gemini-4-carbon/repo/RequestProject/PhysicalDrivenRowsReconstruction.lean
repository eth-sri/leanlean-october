module

public import RequestProject.PhysicalDrivenIntegrable
public import RequestProject.PhysicalVolterraNormalization

/-!
# All genuine driven rows from the same original boundary input

Finite-stage differentiation, integration, and vanishing tail give the actual
primitive recurrence for integrable forcing, and the factorial inverse at index
`k` reconstructs every scaled physical row from the zeroth gauge.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

private theorem physicalDrivenGaugePartial_primitive_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (j N : ℕ) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGaugePartial γ E (physicalDrivenVector W g) (j + 1) N θ =
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ,
        conj (deriv γ s) * physicalDrivenGaugePartial γ E (physicalDrivenVector W g) j N s) +
      ∫ s in (0 : ℝ)..θ,
        deriv γ s * physicalDrivenGaugeTerm γ E (physicalDrivenVector W g) (j + 2) N s := by
  let y := physicalDrivenVector W g
  let p := physicalDrivenGaugePartial γ E y (j + 1) N
  let a : ℝ → ℂ := fun s => conj (deriv γ s) * physicalDrivenGaugePartial γ E y j N s
  let t : ℝ → ℂ := fun s => deriv γ s * physicalDrivenGaugeTerm γ E y (j + 2) N s
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  have hp := physicalDrivenGaugePartial_continuousOn γ hγ.continuous E y hy (j + 1) N
  have ha : ContinuousOn a (Icc 0 (2 * Real.pi)) :=
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenGaugePartial_continuousOn γ hγ.continuous E y hy j N)
  have ht : ContinuousOn t (Icc 0 (2 * Real.pi)) :=
    hγ.continuous_deriv_one.continuousOn.mul
      (physicalDrivenGaugeTerm_continuousOn γ hγ.continuous E y hy (j + 2) N)
  have hsub : Icc 0 θ ⊆ Icc 0 (2 * Real.pi) := Icc_subset_Icc le_rfl hθ.2
  have hd (s : ℝ) (hs : s ∈ Ioo 0 θ) :
      HasDerivAt p (physicalDrivenQ E ^ 2 * a s + t s) s := by
    simpa only [p, a, t, physicalDrivenGaugeTerm, Nat.add_assoc, mul_assoc] using
      physicalDrivenGaugePartial_hasDerivAt_of_intervalIntegrable hK hγ hW g hg
        ⟨hs.1, hs.2.trans_le hθ.2⟩ j N
  have hia : IntervalIntegrable a volume 0 θ :=
    ((ha.mono hsub).mono (by rw [uIcc_of_le hθ.1])).intervalIntegrable
  have hit : IntervalIntegrable t volume 0 θ :=
    ((ht.mono hsub).mono (by rw [uIcc_of_le hθ.1])).intervalIntegrable
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1
    (hp.mono hsub) hd ((hia.const_mul _).add hit)
  rw [physicalDrivenGaugePartial_eq_zero_of_vector_eq_zero γ E y _ _
      (physicalDrivenVector_zero W g), sub_zero,
    intervalIntegral.integral_add (hia.const_mul _) hit,
    intervalIntegral.integral_const_mul] at hi
  exact hi.symm

theorem physicalDrivenGauge_primitive_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGauge γ E (physicalDrivenVector W g) (j + 1) θ =
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
        physicalDrivenGauge γ E (physicalDrivenVector W g) j s) := by
  let y := physicalDrivenVector W g
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  have hp : Tendsto (fun N : ℕ => physicalDrivenGaugePartial γ E y (j + 1) N θ) atTop
      (𝓝 (physicalDrivenGauge γ E y (j + 1) θ)) := by
    have h_simpa := ((summable_norm_physicalDrivenGaugeTerm γ E y (j + 1) θ).of_norm.hasSum.tendsto_sum_nat).comp
      (tendsto_add_atTop_nat 1)
    simp only [physicalDrivenGaugePartial, Function.comp_apply, Function.comp_def] at h_simpa ⊢
    exact h_simpa
  have ha := physicalDrivenGaugePartial_weightedIntegral_tendsto_to γ hγ.continuous E y hy j
    (fun s => conj (deriv γ s))
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn hθ
  have ht := (physicalDrivenGauge_weightedIntegral_hasSum_to γ hγ.continuous E y hy (j + 2)
    (deriv γ) hγ.continuous_deriv_one.continuousOn hθ).summable.tendsto_atTop_zero
  have hr := (ha.const_mul (physicalDrivenQ E ^ 2)).add ht
  simp only [add_zero] at hr
  exact tendsto_nhds_unique hp (hr.congr' (Eventually.of_forall fun N =>
    (physicalDrivenGaugePartial_primitive_of_intervalIntegrable hK hγ hW g hg j N hθ).symm))

theorem physicalDrivenGauge_eq_volterraPrimitiveIterate_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGauge γ E (physicalDrivenVector W g) j θ =
      (physicalDrivenQ E ^ 2) ^ j * volterraPrimitiveIterate
        (fun s => conj (deriv γ s))
        (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) j θ := by
  induction j generalizing θ with
  | zero => simp [volterraPrimitiveIterate]
  | succ j ih =>
    rw [physicalDrivenGauge_primitive_of_intervalIntegrable hK hγ hW g hg j hθ,
      show (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
          physicalDrivenGauge γ E (physicalDrivenVector W g) j s) =
        (physicalDrivenQ E ^ 2) ^ j * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
          volterraPrimitiveIterate (fun s => conj (deriv γ s))
            (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) j s) by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [uIcc_of_le hθ.1] at hs
        rw [ih ⟨hs.1, hs.2.trans hθ.2⟩]; ring,
      pow_succ', volterraPrimitiveIterate]
    ring

theorem volterraPrimitiveIterate_iterate (a h : ℝ → ℂ) (j k : ℕ) :
    volterraPrimitiveIterate a (volterraPrimitiveIterate a h k) j =
      volterraPrimitiveIterate a h (j + k) := by
  induction j with
  | zero => simp only [volterraPrimitiveIterate, zero_add]
  | succ j ih =>
    rw [show j + 1 + k = (j + k) + 1 by omega]
    funext θ
    change (∫ s in (0 : ℝ)..θ,
      a s * volterraPrimitiveIterate a (volterraPrimitiveIterate a h k) j s) =
      ∫ s in (0 : ℝ)..θ, a s * volterraPrimitiveIterate a h (j + k) s
    rw [ih]

/-- Every scaled physical row (including `k = 0`) is the actual Vekua boundary
series of the corresponding iterated primitive of the zeroth gauge. -/
theorem physicalDrivenScaledRow_eq_volterraVekua_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    (k : ℕ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenScaledRow E (physicalDrivenVector W g) k θ =
      (-(E : ℂ) / 4) ^ k *
        (∑' j : ℕ, physicalVekuaCoeff (E : ℂ) j * physicalDrivenCentered γ θ ^ j *
          volterraPrimitiveIterate (fun s => star (deriv γ s))
            (volterraPrimitiveIterate (fun s => star (deriv γ s))
              (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) k) j θ) := by
  rw [← physicalDrivenGauge_inverse_at γ E (physicalDrivenVector W g) θ k, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [physicalDrivenGauge_eq_volterraPrimitiveIterate_of_intervalIntegrable
      hK hγ hW g hg (j + k) hθ,
    physicalDrivenQ_sq hE, volterraPrimitiveIterate_iterate, physicalVekuaCoeff, pow_add]
  simp only [starRingEnd_apply]; ring

end PolyaNeumann

end
