module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

public section


namespace PolyaNeumann

open Real MeasureTheory Set Interval
open scoped InnerProductSpace ComplexConjugate

variable {W : ℝ → ComplexEnd Ell2}



section
variable (hW : ContinuousOn W boundaryInterval) {g : ComplexCurve} (hg : AEStronglyMeasurable g volume) {B } (hgB : ∀ s, ‖g s‖ ≤ B)
include hW g hg B hgB

/-- `i(T_E - T_E^*)` has the kernel `i sgn(θ - s) w_E(θ, s)`. -/
lemma volterra_sub_adj_eq_integral
     (hθ : θ ∈ boundaryInterval) :
    Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) =
      ∫ s in (0 : ℝ)..circlePeriod,
        Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hk := conj_volterraKernel W θ
  have h0 : (0 : ℝ) ∈ boundaryInterval := ⟨le_rfl, hL⟩
  have hL' : circlePeriod ∈ boundaryInterval := ⟨hL, le_rfl⟩
  have key := intervalIntegral_sign_mul_of_integrable hθ (intervalIntegrable_volterraKernel_mul hW hg hgB θ h0 hθ) (intervalIntegrable_volterraKernel_mul hW hg hgB θ hθ hL')
  have e : ∀ s, Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s =
      Complex.I * ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s)) := fun s => by ring
  simp_all [volterraOpAdj, volterraOp]

/-- `O_E B_E O_E^*` has the kernel `⟨e₀, W(θ) B_E W(s)^* e₀⟩`. -/
lemma observation_cutBE_observationAdj_eq_integral (θ : ℝ) :
    observation W (cutBE W (observationAdj W g)) θ =
      ∫ s in (0 : ℝ)..circlePeriod,
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hi := intervalIntegrable_smul_of_continuousOn (continuousOn_adjoint_apply hW (basisVec 0))
    hg hgB (⟨le_rfl, hL⟩) (⟨hL, le_rfl⟩)
  set Lf : Ell2 →L[ℂ] ℂ := (innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))
  have := Lf.intervalIntegral_comp_comm hi
  simp  [Lf] at this
  rw [observation, observationAdj, ← this]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

end


/-- Pointwise: `σ(θ, s) + r_E(θ, s) = i sgn(θ - s) w_E(θ, s) + ⟨e₀, W(θ) B_E W(s)^* e₀⟩`. -/
lemma sawtoothKernel_add_correctedKernel (θ s : ℝ) :
    sawtoothKernel θ s + correctedKernel W θ s =
      Complex.I * Real.sign (θ - s) * volterraKernel W θ s +
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ := by
  simp  [sawtoothKernel, correctedKernel]
  ring

section
variable (hW : ContinuousOn W boundaryInterval) {g : ComplexCurve} (hg : AEStronglyMeasurable g volume) {B } (hgB : ∀ s, ‖g s‖ ≤ B) {θ } (hθ : θ ∈ boundaryInterval)
include hW g hg B hgB θ hθ

/-- The kernel `(σ + r_E)(θ, ·) g` is integrable on `[0, L]` (the two pieces separately). -/
lemma intervalIntegrable_kernel_pieces :
    IntervalIntegrable
      (fun s => Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s) volume 0 circlePeriod ∧
    IntervalIntegrable (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s)
      volume 0 circlePeriod := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have h0 : (0 : ℝ) ∈ boundaryInterval := ⟨le_rfl, hL⟩
  have hL' : circlePeriod ∈ boundaryInterval := ⟨hL, le_rfl⟩
  have i1 : IntervalIntegrable
      (fun s => Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s) volume 0 circlePeriod := by
    have := (intervalIntegrable_sign_mul_of_integrable hθ (intervalIntegrable_volterraKernel_mul hW hg hgB θ h0 hθ) (intervalIntegrable_volterraKernel_mul hW hg hgB θ hθ hL')).const_mul
      Complex.I
    refine this.congr fun s _ => ?_
    ring
  have hbc : ContinuousOn (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ)
      boundaryInterval :=
    ((innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (basisVec 0))
  have i2 : IntervalIntegrable (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s)
      volume 0 circlePeriod := by
    have := intervalIntegrable_smul_of_continuousOn hbc hg hgB h0 hL'
    simpa only [smul_eq_mul, mul_comm] using this
  exact ⟨i1, i2⟩

/-- `s ↦ (σ(θ, s) + r_E(θ, s)) g(s)` is integrable on `[0, L]`. -/
lemma intervalIntegrable_sawtooth_add_corrected_mul :
    IntervalIntegrable (fun s => (sawtoothKernel θ s + correctedKernel W θ s) * g s)
      volume 0 circlePeriod := by
  obtain ⟨i1, i2⟩ := intervalIntegrable_kernel_pieces hW hg hgB hθ
  refine (i1.add i2).congr fun s _ => ?_
  simp  [sawtoothKernel_add_correctedKernel]
  ring

/-- **Lemma 6.6 (kernel identity).** For bounded measurable `g` and `θ ∈ [0, L]`,
`i((T_E g)(θ) - (T_E^* g)(θ)) + (O_E B_E O_E^* g)(θ) = ∫₀^L (σ(θ, s) + r_E(θ, s)) g(s) ds`,
with the sawtooth kernel `σ` of `2D^{-1}` and the corrected kernel `r_E`. -/
theorem volterra_corrected_eq_integral :
    Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) +
        observation W (cutBE W (observationAdj W g)) θ =
      ∫ s in (0 : ℝ)..circlePeriod, (sawtoothKernel θ s + correctedKernel W θ s) * g s := by
  obtain ⟨i1, i2⟩ := intervalIntegrable_kernel_pieces hW hg hgB hθ
  simp_rw [sawtoothKernel_add_correctedKernel, add_mul]
  rw [intervalIntegral.integral_add i1 i2, volterra_sub_adj_eq_integral hW hg hgB hθ,
    observation_cutBE_observationAdj_eq_integral hW hg hgB θ]

end


lemma intervalIntegrable_sawtoothKernel_mul  (hf : Continuous f) θ :
    IntervalIntegrable (fun s => sawtoothKernel θ s * f s) volume 0 circlePeriod := by
  have h1 := ((intervalIntegrable_sign θ 0 circlePeriod).mul_continuousOn hf.continuousOn).const_mul
    Complex.I
  have h2 : IntervalIntegrable (fun s => Complex.I * (((θ - s : ℝ) : ℂ) / π) * f s)
      volume 0 circlePeriod :=
    (by fun_prop : Continuous fun s : ℝ => Complex.I * (((θ - s : ℝ) : ℂ) / π) * f s)
      |>.intervalIntegrable _ _
  refine (h1.sub h2).congr fun s _ => ?_
  simp  [sawtoothKernel]
  ring

/-- `s ↦ r_E(θ, s) f(s)` is integrable on `[0, L]` for continuous `f`. -/
lemma intervalIntegrable_correctedKernel_mul (hW : ContinuousOn W boundaryInterval)
     (hf : Continuous f)  (hfB : ∀ s, ‖f s‖ ≤ B)
     (hθ : θ ∈ boundaryInterval) :
    IntervalIntegrable (fun s => correctedKernel W θ s * f s) volume 0 circlePeriod := by
  refine ((intervalIntegrable_sawtooth_add_corrected_mul hW hf.aestronglyMeasurable hfB hθ).sub
    (intervalIntegrable_sawtoothKernel_mul hf θ)).congr fun s _ => ?_
  ring

end PolyaNeumann
