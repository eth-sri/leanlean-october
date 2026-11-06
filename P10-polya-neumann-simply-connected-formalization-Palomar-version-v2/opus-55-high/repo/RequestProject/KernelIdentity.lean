module

public import RequestProject.SawtoothKernel

/-!
# The kernel identity of Lemma 6.6

For a continuous family `W` on `[0, L]` (`L = 2π`), the operator
`i(T_E - T_E^*) + O_E B_E O_E^*` acts on bounded measurable `g` through the kernel
`σ(θ, s) + r_E(θ, s)`, where `σ` is the sawtooth kernel of `2D^{-1}` (`SawtoothKernel.lean`) and
`r_E` is the corrected kernel of `CorrectedKernel.lean`:

* `volterra_corrected_eq_integral`:
  `i((T_E g)(θ) - (T_E^* g)(θ)) + (O_E B_E O_E^* g)(θ) = ∫₀^L (σ(θ,s) + r_E(θ,s)) g(s) ds`;
* `volterra_corrected_exp`: on Fourier modes `e_n(s) = e^{ins}`, `n ≠ 0`,
  `(i(T_E - T_E^*) + O_E B_E O_E^*) e_n = (2/n) e_n + ∫₀^L r_E(·,s) e_n(s) ds`, i.e. the operator
  is `2D^{-1}` plus the integral operator with kernel `r_E`;
* `volterra_corrected_one`: on the constant mode, the operator is the integral operator with
  kernel `r_E` (as `2D^{-1}` kills constants).
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set Interval
open scoped InnerProductSpace ComplexConjugate

variable {W : ℝ → Ell2 →L[ℂ] Ell2}

variable {F : ℝ → ℂ} {θ : ℝ}

/-- Splitting `∫₀^L sgn(θ - s) F(s) ds = ∫₀^θ F - ∫_θ^L F` for an integrable `F`. -/
lemma intervalIntegral_sign_mul_of_integrable (hθ : θ ∈ Icc 0 (2 * π))
    (h1 : IntervalIntegrable F volume 0 θ) (h2 : IntervalIntegrable F volume θ (2 * π)) :
    ∫ s in 0..(2 * π), Real.sign (θ - s) * F s =
      (∫ s in 0..θ, F s) - ∫ s in θ..(2 * π), F s := by
  have hnull : ∀ᵐ s ∂volume, s ≠ θ := by
    simp [ae_iff]
  have e1 : ∀ᵐ s ∂(volume.restrict (Ι 0 θ)), Real.sign (θ - s) * F s = F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with s hs hmem
    rw [Real.sign_of_pos (by grind)]
    simp
  have e2 : ∀ᵐ s ∂(volume.restrict (Ι θ (2 * π))),
      Real.sign (θ - s) * F s = -F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with s hmem
    rw [Real.sign_of_neg (by simp_all)]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (h1.congr_ae (Filter.EventuallyEq.symm e1)) (h2.neg.congr_ae (Filter.EventuallyEq.symm e2)),
    intervalIntegral.integral_congr_ae_restrict e1,
    intervalIntegral.integral_congr_ae_restrict e2, intervalIntegral.integral_neg]
  ring

/-- Integrability of `s ↦ sgn(θ - s) F(s)` on `[0, L]` for an integrable `F`. -/
lemma intervalIntegrable_sign_mul_of_integrable (hθ : θ ∈ Icc 0 (2 * π))
    (h1 : IntervalIntegrable F volume 0 θ) (h2 : IntervalIntegrable F volume θ (2 * π)) :
    IntervalIntegrable (fun s => Real.sign (θ - s) * F s) volume 0 (2 * π) := by
  have hnull : ∀ᵐ s ∂volume, s ≠ θ := by
    simp [ae_iff]
  have e1 : ∀ᵐ s ∂(volume.restrict (Ι 0 θ)), Real.sign (θ - s) * F s = F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with s hs hmem
    rw [Real.sign_of_pos (by grind)]
    simp
  have e2 : ∀ᵐ s ∂(volume.restrict (Ι θ (2 * π))),
      Real.sign (θ - s) * F s = -F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with s hmem
    rw [Real.sign_of_neg (by simp_all)]
    simp
  exact (h1.congr_ae (Filter.EventuallyEq.symm e1)).trans (h2.neg.congr_ae (Filter.EventuallyEq.symm e2))

/-- `i(T_E - T_E^*)` has the kernel `i sgn(θ - s) w_E(θ, s)`. -/
lemma volterra_sub_adj_eq_integral (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) =
      ∫ s in 0..(2 * π),
        Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s := by
  have hL : 0 ≤ 2 * π := by positivity
  have hk : ∀ s, conj (volterraKernel W s θ) = volterraKernel W θ s := fun s => by
    simp [volterraKernel, ← ContinuousLinearMap.adjoint_inner_right]
  have hkc : ContinuousOn (volterraKernel W θ) (Icc 0 (2 * π)) :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (basisVec 0))
  have hint : ∀ {a b : ℝ}, a ∈ Icc 0 (2 * π) → b ∈ Icc 0 (2 * π) →
      IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume a b := fun ha hb => by
    have := intervalIntegrable_smul_of_continuousOn hkc hg hgB ha hb
    simp_all [mul_comm]
  have e : ∀ s, Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s =
      Complex.I * (Real.sign (θ - s) * (volterraKernel W θ s * g s)) := fun s => by ring
  simp [e, intervalIntegral_sign_mul_of_integrable hθ (hint ⟨le_rfl, hL⟩ hθ) (hint hθ ⟨hL, le_rfl⟩), volterraOpAdj, hk, volterraOp]

/-- `O_E B_E O_E^*` has the kernel `⟨e₀, W(θ) B_E W(s)^* e₀⟩`. -/
lemma observation_cutBE_observationAdj_eq_integral (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) (θ : ℝ) :
    observation W (cutBE W (observationAdj W g)) θ =
      ∫ s in 0..(2 * π),
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s := by
  have hL : 0 ≤ 2 * π := by positivity
  set Lf : Ell2 →L[ℂ] ℂ := (innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))
  have := Lf.intervalIntegral_comp_comm (intervalIntegrable_smul_of_continuousOn (continuousOn_adjoint_apply hW (basisVec 0))
    hg hgB ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩)
  simp only [Lf, ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul] at this
  rw [observation, observationAdj, ← this]
  ring

/-- Pointwise: `σ(θ, s) + r_E(θ, s) = i sgn(θ - s) w_E(θ, s) + ⟨e₀, W(θ) B_E W(s)^* e₀⟩`. -/
lemma sawtoothKernel_add_correctedKernel (θ s : ℝ) :
    sawtoothKernel θ s + correctedKernel W θ s =
      Complex.I * Real.sign (θ - s) * volterraKernel W θ s +
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ := by
  simp only [sawtoothKernel, correctedKernel]
  ring

/-- The kernel `(σ + r_E)(θ, ·) g` is integrable on `[0, L]` (the two pieces separately). -/
lemma intervalIntegrable_kernel_pieces (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    IntervalIntegrable
      (fun s => Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s) volume 0 (2 * π) ∧
    IntervalIntegrable (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s)
      volume 0 (2 * π) := by
  have hL : 0 ≤ 2 * π := by positivity
  have h0 : 0 ∈ Icc 0 (2 * π) := ⟨le_rfl, hL⟩
  have hL' : (2 * π) ∈ Icc 0 (2 * π) := ⟨hL, le_rfl⟩
  have hkc : ContinuousOn (volterraKernel W θ) (Icc 0 (2 * π)) :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (basisVec 0))
  have hint : ∀ {a b : ℝ}, a ∈ Icc 0 (2 * π) → b ∈ Icc 0 (2 * π) →
      IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume a b := fun ha hb => by
    have := intervalIntegrable_smul_of_continuousOn hkc hg hgB ha hb
    simp_all [mul_comm]
  have i1 : IntervalIntegrable
      (fun s => Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s) volume 0 (2 * π) := by
    have := (intervalIntegrable_sign_mul_of_integrable hθ (hint h0 hθ) (hint hθ hL')).const_mul
      Complex.I
    grind
  have i2 : IntervalIntegrable (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s)
      volume 0 (2 * π) := by
    have := intervalIntegrable_smul_of_continuousOn (((innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (basisVec 0))) hg hgB h0 hL'
    simp_all [mul_comm]
  trivial

/-- `s ↦ (σ(θ, s) + r_E(θ, s)) g(s)` is integrable on `[0, L]`. -/
lemma intervalIntegrable_sawtooth_add_corrected_mul (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    IntervalIntegrable (fun s => (sawtoothKernel θ s + correctedKernel W θ s) * g s)
      volume 0 (2 * π) := by
  obtain ⟨i1, i2⟩ := intervalIntegrable_kernel_pieces hW hg hgB hθ
  refine (i1.add i2).congr fun s _ => ?_
  simp only [sawtoothKernel_add_correctedKernel]
  ring

/-- **Lemma 6.6 (kernel identity).** For bounded measurable `g` and `θ ∈ [0, L]`,
`i((T_E g)(θ) - (T_E^* g)(θ)) + (O_E B_E O_E^* g)(θ) = ∫₀^L (σ(θ, s) + r_E(θ, s)) g(s) ds`,
with the sawtooth kernel `σ` of `2D^{-1}` and the corrected kernel `r_E`. -/
theorem volterra_corrected_eq_integral (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) +
        observation W (cutBE W (observationAdj W g)) θ =
      ∫ s in 0..(2 * π), (sawtoothKernel θ s + correctedKernel W θ s) * g s := by
  obtain ⟨i1, i2⟩ := intervalIntegrable_kernel_pieces hW hg hgB hθ
  simp [sawtoothKernel_add_correctedKernel, add_mul, intervalIntegral.integral_add i1 i2, volterra_sub_adj_eq_integral hW hg hgB hθ, observation_cutBE_observationAdj_eq_integral hW hg hgB θ]

lemma intervalIntegrable_sawtoothKernel_mul {f : ℝ → ℂ} (hf : Continuous f) (θ : ℝ) :
    IntervalIntegrable (fun s => sawtoothKernel θ s * f s) volume 0 (2 * π) := by
  refine ((((intervalIntegrable_sign θ 0 (2 * π)).mul_continuousOn hf.continuousOn).const_mul
    Complex.I).sub ((by fun_prop : Continuous fun s  => Complex.I * ((θ - s) / π) * f s)
      |>.intervalIntegrable _ _)).congr fun s _ => ?_
  simp only [sawtoothKernel]
  ring

/-- `s ↦ r_E(θ, s) f(s)` is integrable on `[0, L]` for continuous `f`. -/
lemma intervalIntegrable_correctedKernel_mul (hW : ContinuousOn W (Icc 0 (2 * π)))
    {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ} (hfB : ∀ s, ‖f s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    IntervalIntegrable (fun s => correctedKernel W θ s * f s) volume 0 (2 * π) := by
  refine ((intervalIntegrable_sawtooth_add_corrected_mul hW hf.aestronglyMeasurable hfB hθ).sub
    (intervalIntegrable_sawtoothKernel_mul hf θ)).congr fun s _ => ?_
  ring

end PolyaNeumann
