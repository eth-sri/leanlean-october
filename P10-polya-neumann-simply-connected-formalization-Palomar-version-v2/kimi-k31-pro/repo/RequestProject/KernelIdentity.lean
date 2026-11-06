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

/-- Splitting `∫₀^L sgn(θ - s) F(s) ds = ∫₀^θ F - ∫_θ^L F` for an integrable `F`. -/
lemma intervalIntegral_sign_mul_of_integrable {F : ℝ → ℂ} {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π))
    (h1 : IntervalIntegrable F volume 0 θ) (h2 : IntervalIntegrable F volume θ (2 * π)) :
    ∫ s in (0 : ℝ)..(2 * π), (Real.sign (θ - s) : ℂ) * F s =
      (∫ s in (0 : ℝ)..θ, F s) - ∫ s in θ..(2 * π), F s := by
  have hnull : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ θ := by
    simp [ae_iff, measure_singleton]
  have e1 : ∀ᵐ s ∂(volume.restrict (Ι (0 : ℝ) θ)), (Real.sign (θ - s) : ℂ) * F s = F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with s hs hmem
    rw [Set.uIoc_of_le hθ.1] at hmem
    rw [Real.sign_of_pos (by have := lt_of_le_of_ne hmem.2 hs; linarith)]
    simp
  have e2 : ∀ᵐ s ∂(volume.restrict (Ι θ (2 * π))),
      (Real.sign (θ - s) : ℂ) * F s = -F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with s hmem
    rw [Set.uIoc_of_le hθ.2] at hmem
    rw [Real.sign_of_neg (by linarith [hmem.1])]
    simp
  have i1 : IntervalIntegrable (fun s => (Real.sign (θ - s) : ℂ) * F s) volume 0 θ :=
    h1.congr_ae (Filter.EventuallyEq.symm e1)
  have i2 : IntervalIntegrable (fun s => (Real.sign (θ - s) : ℂ) * F s) volume θ (2 * π) :=
    h2.neg.congr_ae (Filter.EventuallyEq.symm e2)
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    intervalIntegral.integral_congr_ae_restrict e1,
    intervalIntegral.integral_congr_ae_restrict e2, intervalIntegral.integral_neg]
  ring

/-- Integrability of `s ↦ sgn(θ - s) F(s)` on `[0, L]` for an integrable `F`. -/
lemma intervalIntegrable_sign_mul_of_integrable {F : ℝ → ℂ} {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π))
    (h1 : IntervalIntegrable F volume 0 θ) (h2 : IntervalIntegrable F volume θ (2 * π)) :
    IntervalIntegrable (fun s => (Real.sign (θ - s) : ℂ) * F s) volume 0 (2 * π) := by
  have hnull : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ θ := by
    simp [ae_iff, measure_singleton]
  have e1 : ∀ᵐ s ∂(volume.restrict (Ι (0 : ℝ) θ)), (Real.sign (θ - s) : ℂ) * F s = F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with s hs hmem
    rw [Set.uIoc_of_le hθ.1] at hmem
    rw [Real.sign_of_pos (by have := lt_of_le_of_ne hmem.2 hs; linarith)]
    simp
  have e2 : ∀ᵐ s ∂(volume.restrict (Ι θ (2 * π))),
      (Real.sign (θ - s) : ℂ) * F s = -F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with s hmem
    rw [Set.uIoc_of_le hθ.2] at hmem
    rw [Real.sign_of_neg (by linarith [hmem.1])]
    simp
  exact (h1.congr_ae (Filter.EventuallyEq.symm e1)).trans (h2.neg.congr_ae (Filter.EventuallyEq.symm e2))

/-- `i(T_E - T_E^*)` has the kernel `i sgn(θ - s) w_E(θ, s)`. -/
lemma volterra_sub_adj_eq_integral (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) =
      ∫ s in (0 : ℝ)..(2 * π),
        Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hk : ∀ s, conj (volterraKernel W s θ) = volterraKernel W θ s := fun s => by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_left]
  have hkc : ContinuousOn (fun s => volterraKernel W θ s) (Icc 0 (2 * π)) :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (basisVec 0))
  have hint : ∀ {a b : ℝ}, a ∈ Icc 0 (2 * π) → b ∈ Icc 0 (2 * π) →
      IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume a b := fun ha hb => by
    have := intervalIntegrable_smul_of_continuousOn hkc hg hgB ha hb
    simpa only [smul_eq_mul, mul_comm] using this


  have key := intervalIntegral_sign_mul_of_integrable hθ (hint (⟨le_rfl, hL⟩) hθ) (hint hθ (⟨hL, le_rfl⟩))
  have e : ∀ s, Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s =
      Complex.I * ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s)) := fun s => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, key]
  simp [volterraOpAdj, hk, volterraOp]

/-- `O_E B_E O_E^*` has the kernel `⟨e₀, W(θ) B_E W(s)^* e₀⟩`. -/
lemma observation_cutBE_observationAdj_eq_integral (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) (θ : ℝ) :
    observation W (cutBE W (observationAdj W g)) θ =
      ∫ s in (0 : ℝ)..(2 * π),
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hi := intervalIntegrable_smul_of_continuousOn (continuousOn_adjoint_apply hW (basisVec 0))
    hg hgB (⟨le_rfl, hL⟩ : (0 : ℝ) ∈ Icc 0 (2 * π)) (⟨hL, le_rfl⟩ : 2 * π ∈ Icc 0 (2 * π))
  set Lf := (innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))
  have := Lf.intervalIntegral_comp_comm hi
  simp [Lf, ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul,
    smul_eq_mul] at this
  rw [observation, observationAdj, ← this]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- Pointwise: `σ(θ, s) + r_E(θ, s) = i sgn(θ - s) w_E(θ, s) + ⟨e₀, W(θ) B_E W(s)^* e₀⟩`. -/
lemma sawtoothKernel_add_correctedKernel (θ s : ℝ) :
    sawtoothKernel θ s + correctedKernel W θ s =
      Complex.I * Real.sign (θ - s) * volterraKernel W θ s +
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ := by
  simp [sawtoothKernel, correctedKernel]
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
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * π) := ⟨le_rfl, hL⟩
  have hL' : (2 * π) ∈ Icc 0 (2 * π) := ⟨hL, le_rfl⟩
  have hkc : ContinuousOn (fun s => volterraKernel W θ s) (Icc 0 (2 * π)) :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (basisVec 0))
  have hint : ∀ {a b : ℝ}, a ∈ Icc 0 (2 * π) → b ∈ Icc 0 (2 * π) →
      IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume a b := fun ha hb => by
    have := intervalIntegrable_smul_of_continuousOn hkc hg hgB ha hb
    simpa only [smul_eq_mul, mul_comm] using this
  have i1 : IntervalIntegrable
      (fun s => Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s) volume 0 (2 * π) := by
    have := (intervalIntegrable_sign_mul_of_integrable hθ (hint h0 hθ) (hint hθ hL')).const_mul
      Complex.I
    refine this.congr fun s _ => ?_
    ring
  have hbc : ContinuousOn (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ)
      (Icc 0 (2 * π)) :=
    ((innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (basisVec 0))
  have i2 : IntervalIntegrable (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s)
      volume 0 (2 * π) := by
    have := intervalIntegrable_smul_of_continuousOn hbc hg hgB h0 hL'
    simpa only [smul_eq_mul, mul_comm] using this
  exact ⟨i1, i2⟩

/-- `s ↦ (σ(θ, s) + r_E(θ, s)) g(s)` is integrable on `[0, L]`. -/
lemma intervalIntegrable_sawtooth_add_corrected_mul (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    IntervalIntegrable (fun s => (sawtoothKernel θ s + correctedKernel W θ s) * g s)
      volume 0 (2 * π) := by
  obtain ⟨i1, i2⟩ := intervalIntegrable_kernel_pieces hW hg hgB hθ
  refine (i1.add i2).congr fun s _ => ?_
  simp [sawtoothKernel_add_correctedKernel]
  ring

/-- **Lemma 6.6 (kernel identity).** For bounded measurable `g` and `θ ∈ [0, L]`,
`i((T_E g)(θ) - (T_E^* g)(θ)) + (O_E B_E O_E^* g)(θ) = ∫₀^L (σ(θ, s) + r_E(θ, s)) g(s) ds`,
with the sawtooth kernel `σ` of `2D^{-1}` and the corrected kernel `r_E`. -/
theorem volterra_corrected_eq_integral (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) +
        observation W (cutBE W (observationAdj W g)) θ =
      ∫ s in (0 : ℝ)..(2 * π), (sawtoothKernel θ s + correctedKernel W θ s) * g s := by
  obtain ⟨i1, i2⟩ := intervalIntegrable_kernel_pieces hW hg hgB hθ
  simp_rw [sawtoothKernel_add_correctedKernel, add_mul]
  rw [intervalIntegral.integral_add i1 i2, volterra_sub_adj_eq_integral hW hg hgB hθ,
    observation_cutBE_observationAdj_eq_integral hW hg hgB θ]

lemma intervalIntegrable_sawtoothKernel_mul {f : ℝ → ℂ} (hf : Continuous f) (θ : ℝ) :
    IntervalIntegrable (fun s => sawtoothKernel θ s * f s) volume 0 (2 * π) := by
  have h1 := ((intervalIntegrable_sign θ 0 (2 * π)).mul_continuousOn hf.continuousOn).const_mul
    Complex.I
  have h2 : IntervalIntegrable (fun s => Complex.I * (((θ - s : ℝ) : ℂ) / π) * f s)
      volume 0 (2 * π) :=
    (by fun_prop : Continuous fun s : ℝ => Complex.I * (((θ - s : ℝ) : ℂ) / π) * f s)
      |>.intervalIntegrable _ _
  refine (h1.sub h2).congr fun s _ => ?_
  simp [sawtoothKernel, Complex.ofReal_sub]
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
