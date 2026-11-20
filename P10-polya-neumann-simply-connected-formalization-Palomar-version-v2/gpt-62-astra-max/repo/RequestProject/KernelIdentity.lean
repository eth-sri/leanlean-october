module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.SawtoothKernel
public import RequestProject.PlanarNotation

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

variable {W : TransportPath}

section

variable (hW : ContinuousOn W angleInterval)

include hW in
/-- `i(T_E - T_E^*)` has the kernel `i sgn(θ - s) w_E(θ, s)`. -/
lemma volterra_sub_adj_eq_integral
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) =
      ∫ₚ s,
        Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s := by
  have hL : 0 ≤ anglePeriod := by positivity
  have hk : ∀ s, conj (volterraKernel W s θ) = volterraKernel W θ s := fun s => by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_left]
  have hkc : ContinuousOn (fun s => volterraKernel W θ s) angleInterval :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (basisVec 0))
  have hint : ∀ {a b : ℝ}, a ∈ angleInterval → b ∈ angleInterval →
      IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume a b := fun ha hb => by
    have := intervalIntegrable_smul_of_continuousOn hkc hg hgB ha hb
    simpa [smul_eq_mul, mul_comm] using this
  have h0 : (0 : ℝ) ∈ angleInterval := ⟨le_rfl, hL⟩
  have hL' : anglePeriod ∈ angleInterval := ⟨hL, le_rfl⟩
  have key := (sign_split hθ (hint h0 hθ) (hint hθ hL')).2
  have e : ∀ s, Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s =
      Complex.I * ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s)) := fun s => by ring
  simp_rw [e]
  simp [intervalIntegral.integral_const_mul, key, volterraOpAdj, hk, volterraOp]

include hW in
/-- `O_E B_E O_E^*` has the kernel `⟨e₀, W(θ) B_E W(s)^* e₀⟩`. -/
lemma observation_cutBE_observationAdj_eq_integral
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) (θ : ℝ) :
    observation W (cutBE W (observationAdj W g)) θ =
      ∫ₚ s,
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s := by
  have hL : 0 ≤ anglePeriod := by positivity
  have hi := intervalIntegrable_smul_of_continuousOn (continuousOn_adjoint_apply hW (basisVec 0))
    hg hgB (⟨le_rfl, hL⟩ : 0 ∈ angleInterval) (⟨hL, le_rfl⟩ : anglePeriod ∈ angleInterval)
  set Lf : Ell2 →L[ℂ] ℂ := (innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))
  have := Lf.intervalIntegral_comp_comm hi
  simp only [Lf, ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul,
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

include hW in
/-- The kernel `(σ + r_E)(θ, ·) g` is integrable on `[0, L]` (the two pieces separately). -/
lemma intervalIntegrable_kernel_pieces
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    IntervalIntegrable
      (fun s => Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s) volume 0 anglePeriod ∧
    IntervalIntegrable (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s)
      volume 0 anglePeriod := by
  have hL : 0 ≤ anglePeriod := by positivity
  have h0 : 0 ∈ angleInterval := ⟨le_rfl, hL⟩
  have hL' : anglePeriod ∈ angleInterval := ⟨hL, le_rfl⟩
  have hkc : ContinuousOn (fun s => volterraKernel W θ s) angleInterval :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (basisVec 0))
  have hint : ∀ {a b : ℝ}, a ∈ angleInterval → b ∈ angleInterval →
      IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume a b := fun ha hb => by
    have := intervalIntegrable_smul_of_continuousOn hkc hg hgB ha hb
    simpa [mul_comm] using this
  have i1 : IntervalIntegrable
      (fun s => Complex.I * Real.sign (θ - s) * volterraKernel W θ s * g s) volume 0 anglePeriod := by
    have := (sign_split hθ (hint h0 hθ) (hint hθ hL')).1.const_mul
      Complex.I
    refine this.congr fun s _ => ?_
    ring
  have hbc  :=
    ((innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (basisVec 0))
  have i2 : IntervalIntegrable (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s)
      volume 0 anglePeriod := by
    have := intervalIntegrable_smul_of_continuousOn hbc hg hgB h0 hL'
    simpa [smul_eq_mul, mul_comm] using this
  simp [*]

include hW in
/-- `s ↦ (σ(θ, s) + r_E(θ, s)) g(s)` is integrable on `[0, L]`. -/
lemma intervalIntegrable_sawtooth_add_corrected_mul
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    IntervalIntegrable (fun s => (sawtoothKernel θ s + correctedKernel W θ s) * g s)
      volume 0 anglePeriod := by
  obtain ⟨i1, i2⟩ := intervalIntegrable_kernel_pieces hW hg hgB hθ
  refine (i1.add i2).congr fun s _ => ?_
  simp [sawtoothKernel_add_correctedKernel]
  ring

include hW in
/-- **Lemma 6.6 (kernel identity).** For bounded measurable `g` and `θ ∈ [0, L]`,
`i((T_E g)(θ) - (T_E^* g)(θ)) + (O_E B_E O_E^* g)(θ) = ∫₀^L (σ(θ, s) + r_E(θ, s)) g(s) ds`,
with the sawtooth kernel `σ` of `2D^{-1}` and the corrected kernel `r_E`. -/
theorem volterra_corrected_eq_integral
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) +
        observation W (cutBE W (observationAdj W g)) θ =
      ∫ₚ s, (sawtoothKernel θ s + correctedKernel W θ s) * g s := by
  obtain ⟨i1, i2⟩ := intervalIntegrable_kernel_pieces hW hg hgB hθ
  simp_rw [sawtoothKernel_add_correctedKernel, add_mul]
  rw [intervalIntegral.integral_add i1 i2, volterra_sub_adj_eq_integral hW hg hgB hθ,
    observation_cutBE_observationAdj_eq_integral hW hg hgB θ]

lemma intervalIntegrable_sawtoothKernel_mul {f : ℝ → ℂ} (hf : Continuous f) (θ : ℝ) :
    IntervalIntegrable (fun s => sawtoothKernel θ s * f s) volume 0 anglePeriod := by
  
  
  refine ((((intervalIntegrable_sign θ 0 anglePeriod).mul_continuousOn hf.continuousOn).const_mul
    Complex.I).sub ((by fun_prop : Continuous fun s : ℝ => Complex.I * (((θ - s : ℝ) : ℂ) / π) * f s)
    |>.intervalIntegrable _ _)).congr fun s _ => ?_
  simp only [sawtoothKernel, Complex.ofReal_sub]
  ring

include hW in
/-- `s ↦ r_E(θ, s) f(s)` is integrable on `[0, L]` for continuous `f`. -/
lemma intervalIntegrable_correctedKernel_mul
    {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ} (hfB : ∀ s, ‖f s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    IntervalIntegrable (fun s => correctedKernel W θ s * f s) volume 0 anglePeriod := by
  refine ((intervalIntegrable_sawtooth_add_corrected_mul hW hf.aestronglyMeasurable hfB hθ).sub
    (intervalIntegrable_sawtoothKernel_mul hf θ)).congr fun s _ => ?_
  ring

end

end PolyaNeumann
