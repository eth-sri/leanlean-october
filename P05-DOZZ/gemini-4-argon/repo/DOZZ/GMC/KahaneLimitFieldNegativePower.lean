/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosNegativePower
public import DOZZ.GMC.KahaneNegativeMellin
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! Bounded Laplace tests pass field-chaos Kahane comparisons through convergence in measure. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs


/-- Negative-power field comparison passes to limits in measure. The finite-cutoff comparison is
first transferred to bounded Laplace tests, then Mellin integration recovers the possibly infinite
negative moments of the limiting masses. -/
theorem kahane_limit_field_negative_power
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ℝ → ΩX → S → ℝ) (Ψ : ℝ → ΩY → S → ℝ)
    (hΦ : ∀ r, DOZZ.IsCenteredGaussianField PX (Φ r))
    (hΨ : ∀ r, DOZZ.IsCenteredGaussianField PY (Ψ r))
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) γ q (hq : 0 < q)
    (hcov : ∀ r, ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ r ω xy.1 * Φ r ω xy.2 ∂PX ≤ ∫ ω, Ψ r ω xy.1 * Ψ r ω xy.2 ∂PY)
    (hdiag : ∀ r, ∀ᵐ x ∂ν,
      ∫ ω, Φ r ω x ^ 2 ∂PX ≤ ∫ ω, Ψ r ω x ^ 2 ∂PY)
    ZX ZY
    (hXconv : TendstoInMeasure PX
      (fun r ω => (DOZZ.fieldChaosMass PX (Φ r) ν h γ ω).toReal) atTop ZX)
    (hYconv : TendstoInMeasure PY
      (fun r ω => (DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω).toReal) atTop ZY) :
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZX ω)) (-q) ∂PX ≤
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZY ω)) (-q) ∂PY := by
  classical
  have kahane_limit_field_laplace t (ht : 0 ≤ t) (hcov : ∀ r, ∀ᵐ xy ∂ν.prod ν, ∫ ω, Φ r ω xy.1 * Φ r ω xy.2 ∂PX ≤ ∫ ω, Ψ r ω xy.1 * Ψ r ω xy.2 ∂PY) (hdiag : ∀ r, ∀ᵐ x ∂ν, ∫ ω, Φ r ω x ^ 2 ∂PX ≤ ∫ ω, Ψ r ω x ^ 2 ∂PY) ZX ZY (hXconv : TendstoInMeasure PX (fun r ω => (DOZZ.fieldChaosMass PX (Φ r) ν h γ ω).toReal) atTop ZX) (hYconv : TendstoInMeasure PY (fun r ω => (DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω).toReal) atTop ZY) : ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * ZX ω)) ∂PX ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * ZY ω)) ∂PY := by
    classical
    let fX : ℝ → ΩX → ℝ := fun r ω => (DOZZ.fieldChaosMass PX (Φ r) ν h γ ω).toReal
    let fY : ℝ → ΩY → ℝ := fun r ω => (DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω).toReal
    obtain ⟨ns, hns, hXae⟩ := (hXconv.comp tendsto_natCast_atTop_atTop).exists_seq_tendsto_ae
    obtain ⟨ms, hms, hYae⟩ := ((hYconv.comp tendsto_natCast_atTop_atTop).comp hns.tendsto_atTop).exists_seq_tendsto_ae
    let : IsProbabilityMeasure PX := (hΦ 0).2 0 (fun i => Fin.elim0 i) |>.1
    let : IsProbabilityMeasure PY := (hΨ 0).2 0 (fun i => Fin.elim0 i) |>.1
    let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
    have hLap r :
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * fX r ω)) ∂PX ≤
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * fY r ω)) ∂PY := by
      by_cases hνzero : ν = 0
      · have hmassX (ω : ΩX) : DOZZ.fieldChaosMass PX (Φ r) ν h γ ω = 0 := by
          simp [DOZZ.fieldChaosMass, hνzero]
        have hmassY ω : DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω = 0 := by
          simp [DOZZ.fieldChaosMass, hνzero]
        simp [fX, fY, hmassX, hmassY]
      · have hS : Nonempty S := by
          obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hνzero)
          exact ⟨x⟩
        let : Nonempty S := hS
        simpa [fX, fY, νf] using
          kahane_field_laplace_of_nonzero_finite_measure_eq PX PY (Φ r) (Ψ r)
            (hΦ r) (hΨ r) νf (by
              intro hz
              apply hνzero
              simpa [νf] using (congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hz))
            h hh hhb γ t ht (by filter_upwards [hcov r] with xy hxy; simpa [DOZZ.gaussianCovariance] using hxy) (by filter_upwards [hdiag r] with x hx; simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hx)
    let FX : ℕ → ΩX → ℝ≥0∞ := fun n ω =>
      ENNReal.ofReal (Real.exp (-t * fX (ns (ms n)) ω))
    let FY : ℕ → ΩY → ℝ≥0∞ := fun n ω =>
      ENNReal.ofReal (Real.exp (-t * fY (ns (ms n)) ω))
    have hFXmeas : ∀ n, Measurable (FX n) := by
      intro n
      dsimp [FX, fX]
      exact ENNReal.measurable_ofReal.comp <| Real.measurable_exp.comp <|
        (measurable_const.mul <|
          (centeredGaussianField_fieldChaosMass_measurable PX (Φ (ns (ms n)))
            (hΦ (ns (ms n))) ν h hh γ).ennreal_toReal)
    have hFYmeas : ∀ n, Measurable (FY n) := by
      intro n
      dsimp [FY, fY]
      exact ENNReal.measurable_ofReal.comp <| Real.measurable_exp.comp <|
        (measurable_const.mul <|
          (centeredGaussianField_fieldChaosMass_measurable PY (Ψ (ns (ms n)))
            (hΨ (ns (ms n))) ν h hh γ).ennreal_toReal)
    have hFXbound : ∀ n, ∀ᵐ ω ∂PX, FX n ω ≤ 1 := by
      intro n
      filter_upwards [] with ω
      rw [ENNReal.ofReal_le_one]
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_nonneg ht (ENNReal.toReal_nonneg : 0 ≤ fX (ns (ms n)) ω)]
    have hFYbound : ∀ n, ∀ᵐ ω ∂PY, FY n ω ≤ 1 := by
      intro n
      filter_upwards [] with ω
      rw [ENNReal.ofReal_le_one]
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_nonneg ht (ENNReal.toReal_nonneg : 0 ≤ fY (ns (ms n)) ω)]
    let g : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-t * x))
    have hgcont : Continuous g := by
      dsimp [g]
      exact ENNReal.continuous_ofReal.comp <|
        Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hlimorder := le_of_tendsto_of_tendsto (tendsto_lintegral_of_dominated_convergence (fun _ : ΩX => (1 : ℝ≥0∞)) hFXmeas hFXbound (by simp) (by filter_upwards [(by filter_upwards [hXae] with ω hω; exact hω.comp hms.tendsto_atTop)] with ω hω; exact hgcont.continuousAt.tendsto.comp hω)) (tendsto_lintegral_of_dominated_convergence (fun _ : ΩY => (1 : ℝ≥0∞)) hFYmeas hFYbound (by simp) (by filter_upwards [(by filter_upwards [hYae] with ω hω; exact hω)] with ω hω; exact hgcont.continuousAt.tendsto.comp hω))
      (Filter.Eventually.of_forall (by intro n; simpa [FX, FY, fX, fY] using hLap (ns (ms n))))
    simpa [g] using hlimorder
  have hPXprob : IsProbabilityMeasure PX :=
    (hΦ 0).2 0 (fun i => Fin.elim0 i) |>.1
  have hPYprob : IsProbabilityMeasure PY :=
    (hΨ 0).2 0 (fun i => Fin.elim0 i) |>.1
  let : IsProbabilityMeasure PX := hPXprob
  let : IsProbabilityMeasure PY := hPYprob
  obtain ⟨ns, hns, hXae⟩ := (hXconv.comp tendsto_natCast_atTop_atTop).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hYae⟩ := ((hYconv.comp tendsto_natCast_atTop_atTop).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  let mX : ΩX → ℝ := fun ω => max (ZX ω) 0
  let mY : ΩY → ℝ := fun ω => max (ZY ω) 0
  have hmXeq : mX =ᵐ[PX] ZX := by
    filter_upwards [(show ∀ᵐ ω ∂PX, 0 ≤ ZX ω by filter_upwards [(by filter_upwards [hXae] with ω hω; exact hω.comp hms.tendsto_atTop)] with ω hω; exact isClosed_Ici.mem_of_tendsto hω (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg))] with ω hω
    simp [mX, max_eq_left hω]
  have hmYeq : mY =ᵐ[PY] ZY := by
    filter_upwards [(show ∀ᵐ ω ∂PY, 0 ≤ ZY ω by filter_upwards [(by filter_upwards [hYae] with ω hω; exact hω)] with ω hω; exact isClosed_Ici.mem_of_tendsto hω (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg))] with ω hω
    simp [mY, max_eq_left hω]
  have hLapLimit t (ht : 0 < t) :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-(mX ω * t))) ∂PX ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-(mY ω * t))) ∂PY := by
    calc
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-(mX ω * t))) ∂PX =
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * ZX ω)) ∂PX := by
            apply lintegral_congr_ae
            filter_upwards [hmXeq] with ω hω
            congr 2
            rw [hω]
            ring
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * ZY ω)) ∂PY :=
        kahane_limit_field_laplace t
          (le_of_lt ht) hcov hdiag ZX ZY hXconv hYconv
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (-(mY ω * t))) ∂PY := by
            apply lintegral_congr_ae
            filter_upwards [hmYeq] with ω hω
            congr 2
            rw [hω]
            ring
  have hMomentX :
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZX ω)) (-q) ∂PX =
        ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mX ω)) (-q) ∂PX := by
    apply lintegral_congr_ae
    filter_upwards [hmXeq] with ω hω
    rw [hω]
  have hMomentY :
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZY ω)) (-q) ∂PY =
        ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mY ω)) (-q) ∂PY := by
    apply lintegral_congr_ae
    filter_upwards [hmYeq] with ω hω
    rw [hω]
  calc
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZX ω)) (-q) ∂PX =
        ENNReal.ofReal (1 / Real.Gamma q) *
          ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
            (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mX ω * t))) ∂PX) ∂volume :=
          hMomentX.trans (nonneg_rpow_neg_lintegral_eq_weighted_laplace PX mX (fun ω => le_max_right _ _) ((hXconv.aemeasurable (fun r => (centeredGaussianField_fieldChaosMass_measurable PX (Φ r) (hΦ r) ν h hh γ) |>.ennreal_toReal.aemeasurable)).max measurable_const.aemeasurable) q hq)
    _ ≤ ENNReal.ofReal (1 / Real.Gamma q) *
          ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
            (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mY ω * t))) ∂PY) ∂volume :=
          mul_le_mul_of_nonneg_left (by apply lintegral_mono_ae; filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact mul_le_mul_of_nonneg_left (hLapLimit t ht) (by positivity)) (by positivity)
    _ = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZY ω)) (-q) ∂PY :=
          (hMomentY.trans (nonneg_rpow_neg_lintegral_eq_weighted_laplace PY mY (fun ω => le_max_right _ _) ((hYconv.aemeasurable (fun r => (centeredGaussianField_fieldChaosMass_measurable PY (Ψ r) (hΨ r) ν h hh γ) |>.ennreal_toReal.aemeasurable)).max measurable_const.aemeasurable) q hq)).symm


end DOZZ.Proofs
