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
local notation "Φ0" => Icc 0

lemma intervalIntegral_sign_mul_of_integrable   (hθ : θ ∈ Φ0 (2 * π))
    (h1 : IntervalIntegrable F volume 0 θ) (h2 : IntervalIntegrable F volume θ (2 * π)) :
    ∫ s in 0..(2 * π), (Real.sign (θ - s) : ℂ) * F s =
      (∫ s in 0..θ, F s) - ∫ s in θ..(2 * π), F s := by
  have e1 : ∀ᵐ s ∂(volume.restrict (Ι 0 θ)), Real.sign (θ - s) * F s = F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [(show ∀ᵐ s ∂volume, s ≠ θ by
      simp [ae_iff])] with s hs hmem
    rw [Set.uIoc_of_le hθ.1] at hmem
    rw [Real.sign_of_pos (by have := lt_of_le_of_ne hmem.2 hs; linarith)]
    simp
  have e2 : ∀ᵐ s ∂(volume.restrict (Ι θ (2 * π))),
      Real.sign (θ - s) * F s = -F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with s hmem
    rw [Set.uIoc_of_le hθ.2] at hmem
    rw [Real.sign_of_neg (by linarith [hmem.1])]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (h1.congr_ae (Filter.EventuallyEq.symm e1)) (h2.neg.congr_ae (Filter.EventuallyEq.symm e2)),
    intervalIntegral.integral_congr_ae_restrict e1,
    intervalIntegral.integral_congr_ae_restrict e2, intervalIntegral.integral_neg]
  ring

/-- Integrability of `s ↦ sgn(θ - s) F(s)` on `[0, L]` for an integrable `F`. -/
lemma intervalIntegrable_sign_mul_of_integrable   (hθ : θ ∈ Φ0 (2 * π))
    (h1 : IntervalIntegrable F volume 0 θ) (h2 : IntervalIntegrable F volume θ (2 * π)) :
    IntervalIntegrable (fun s => (Real.sign (θ - s) : ℂ) * F s) volume 0 (2 * π) := by
  have e1 : ∀ᵐ s ∂(volume.restrict (Ι 0 θ)), Real.sign (θ - s) * F s = F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [(show ∀ᵐ s ∂volume, s ≠ θ by
      simp [ae_iff])] with s hs hmem
    rw [Set.uIoc_of_le hθ.1] at hmem
    rw [Real.sign_of_pos (by have := lt_of_le_of_ne hmem.2 hs; linarith)]
    simp
  exact (h1.congr_ae (Filter.EventuallyEq.symm e1)).trans (h2.neg.congr_ae (Filter.EventuallyEq.symm (show ∀ᵐ s ∂(volume.restrict (Ι θ (2 * π))), Real.sign (θ - s) * F s = -F s by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with s hmem
    rw [Set.uIoc_of_le hθ.2] at hmem
    rw [Real.sign_of_neg (by linarith [hmem.1])]
    simp)))

/-- Pointwise: `σ(θ, s) + r_E(θ, s) = i sgn(θ - s) w_E(θ, s) + ⟨e₀, W(θ) B_E W(s)^* e₀⟩`. -/
local notation "Φ1" => basisVec 0

local notation "Φ2" => volterraKernel W

lemma sawtoothKernel_add_correctedKernel θ s :
    sawtoothKernel θ s + correctedKernel W θ s =
      Complex.I * Real.sign (θ - s) * Φ2 θ s +
        ⟪Φ1, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (Φ1)))⟫_ℂ := by
  simp [sawtoothKernel, correctedKernel]
  ring

/-- The kernel `(σ + r_E)(θ, ·) g` is integrable on `[0, L]` (the two pieces separately). -/
lemma intervalIntegrable_kernel_pieces (hW : ContinuousOn W (Φ0 (2 * π)))
     (hg : AEStronglyMeasurable g volume)  (hgB : ∀ s, ‖g s‖ ≤ B)
     (hθ : θ ∈ Φ0 (2 * π)) :
    IntervalIntegrable
      (fun s => Complex.I * Real.sign (θ - s) * Φ2 θ s * g s) volume 0 (2 * π) ∧
    IntervalIntegrable (fun s =>
      ⟪Φ1, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (Φ1)))⟫_ℂ * g s)
      volume 0 (2 * π) := by
  have hL : 0 ≤ 2 * π := by positivity
  have h0 : 0 ∈ Φ0 (2 * π) := ⟨le_rfl, hL⟩
  have hL' : 2 * π ∈ Φ0 (2 * π) := ⟨hL, le_rfl⟩
  have hkc : ContinuousOn (Φ2 θ) (Φ0 (2 * π)) :=
    ((innerSL ℂ (Φ1)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (Φ1))
  have hint : ∀ {a b}, a ∈ Φ0 (2 * π) → b ∈ Φ0 (2 * π) →
      IntervalIntegrable (fun s => Φ2 θ s * g s) volume a b := fun ha hb => by
    simpa [mul_comm] using intervalIntegrable_smul_of_continuousOn hkc hg hgB ha hb
  exact ⟨(by
    refine ((intervalIntegrable_sign_mul_of_integrable hθ (hint h0 hθ) (hint hθ hL')).const_mul Complex.I).congr fun s _ => ?_
    ring), (by
    simpa [mul_comm] using (intervalIntegrable_smul_of_continuousOn (((innerSL ℂ (Φ1)).comp ((W θ).comp (cutBE W))).continuous.comp_continuousOn (continuousOn_adjoint_apply hW (Φ1))) hg hgB h0 hL'))⟩

/-- `s ↦ (σ(θ, s) + r_E(θ, s)) g(s)` is integrable on `[0, L]`. -/
lemma intervalIntegrable_sawtooth_add_corrected_mul (hW : ContinuousOn W (Φ0 (2 * π)))
     (hg : AEStronglyMeasurable g volume)  (hgB : ∀ s, ‖g s‖ ≤ B)
     (hθ : θ ∈ Φ0 (2 * π)) :
    IntervalIntegrable (fun s => (sawtoothKernel θ s + correctedKernel W θ s) * g s)
      volume 0 (2 * π) := by
  obtain ⟨i1, i2⟩ := intervalIntegrable_kernel_pieces hW hg hgB hθ
  refine (i1.add i2).congr fun s _ => ?_
  simp [sawtoothKernel_add_correctedKernel]
  ring

/-- **Lemma 6.6 (kernel identity).** For bounded measurable `g` and `θ ∈ [0, L]`,
`i((T_E g)(θ) - (T_E^* g)(θ)) + (O_E B_E O_E^* g)(θ) = ∫₀^L (σ(θ, s) + r_E(θ, s)) g(s) ds`,
with the sawtooth kernel `σ` of `2D^{-1}` and the corrected kernel `r_E`. -/
theorem volterra_corrected_eq_integral (hW : ContinuousOn W (Φ0 (2 * π)))
     (hg : AEStronglyMeasurable g volume)  (hgB : ∀ s, ‖g s‖ ≤ B)
     (hθ : θ ∈ Φ0 (2 * π)) :
    Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) +
        observation W (cutBE W (observationAdj W g)) θ =
      ∫ s in 0..(2 * π), (sawtoothKernel θ s + correctedKernel W θ s) * g s := by
  obtain ⟨i1, i2⟩ := intervalIntegrable_kernel_pieces hW hg hgB hθ
  simp_rw [sawtoothKernel_add_correctedKernel, add_mul]
  rw [intervalIntegral.integral_add i1 i2, show Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) = ∫ s in 0..(2 * π), Complex.I * Real.sign (θ - s) * Φ2 θ s * g s by
    have hL : 0 ≤ 2 * π := by positivity
    have hk : ∀ s, conj (Φ2 s θ) = Φ2 θ s := fun s => by
      simp only [volterraKernel]
      rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
        ContinuousLinearMap.adjoint_inner_left]
    have hkc : ContinuousOn (Φ2 θ) (Φ0 (2 * π)) :=
      ((innerSL ℂ (Φ1)).comp (W θ)).continuous.comp_continuousOn
        (continuousOn_adjoint_apply hW (Φ1))
    have hint : ∀ {a b}, a ∈ Φ0 (2 * π) → b ∈ Φ0 (2 * π) →
        IntervalIntegrable (fun s => Φ2 θ s * g s) volume a b := fun ha hb => by
      simpa [mul_comm] using intervalIntegrable_smul_of_continuousOn hkc hg hgB ha hb
    have h0 : 0 ∈ Φ0 (2 * π) := ⟨le_rfl, hL⟩
    have hL' : 2 * π ∈ Φ0 (2 * π) := ⟨hL, le_rfl⟩
    have key := intervalIntegral_sign_mul_of_integrable hθ (hint h0 hθ) (hint hθ hL')
    have e : ∀ s, Complex.I * Real.sign (θ - s) * Φ2 θ s * g s =
        Complex.I * ((Real.sign (θ - s)) * (Φ2 θ s * g s)) := fun s => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, key]
    simp [volterraOpAdj, hk, volterraOp],
    show observation W (cutBE W (observationAdj W g)) θ = ∫ s in 0..(2 * π), ⟪Φ1, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (Φ1)))⟫_ℂ * g s by
      have hL : 0 ≤ 2 * π := by positivity
      set Lf := (innerSL ℂ (Φ1)).comp ((W θ).comp (cutBE W))
      have := Lf.intervalIntegral_comp_comm (intervalIntegrable_smul_of_continuousOn (continuousOn_adjoint_apply hW (Φ1)) hg hgB ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩)
      simp [Lf] at this
      rw [observation, observationAdj, ← this]
      refine intervalIntegral.integral_congr fun s _ => ?_
      ring]

lemma intervalIntegrable_sawtoothKernel_mul  (hf : Continuous f) θ :
    IntervalIntegrable (fun s => sawtoothKernel θ s * f s) volume 0 (2 * π) := by
  refine ((((intervalIntegrable_sign θ 0 (2 * π)).mul_continuousOn hf.continuousOn).const_mul Complex.I).sub ((by fun_prop : Continuous fun s => Complex.I * ((θ - s : ℝ) / π) * f s) |>.intervalIntegrable _ _)).congr fun s _ => ?_
  simp [sawtoothKernel]
  ring

/-- `s ↦ r_E(θ, s) f(s)` is integrable on `[0, L]` for continuous `f`. -/
lemma intervalIntegrable_correctedKernel_mul (hW : ContinuousOn W (Φ0 (2 * π)))
     (hf : Continuous f)  (hfB : ∀ s, ‖f s‖ ≤ B)
     (hθ : θ ∈ Φ0 (2 * π)) :
    IntervalIntegrable (fun s => correctedKernel W θ s * f s) volume 0 (2 * π) := by
  refine ((intervalIntegrable_sawtooth_add_corrected_mul hW hf.aestronglyMeasurable hfB hθ).sub
    (intervalIntegrable_sawtoothKernel_mul hf θ)).congr fun s _ => ?_
  ring

end PolyaNeumann
