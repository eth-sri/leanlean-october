/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosNegativePower
public import DOZZ.GMC.KahaneNegativeMellin
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Tactic

/-! Bounded Laplace tests pass field-chaos Kahane comparisons through convergence in measure. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private theorem tendsto_lintegral_laplace_of_inMeasure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (t : ℝ) (ht : 0 ≤ t) (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n))
    (hn : ∀ n ω, 0 ≤ f n ω) (Z : Ω → ℝ) (hZ : TendstoInMeasure P f atTop Z) :
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * f n ω)) ∂P) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (Real.exp (-t * Z ω)) ∂P)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hae⟩ := (hZ.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, tendsto_lintegral_of_dominated_convergence (fun _ => 1)
    (fun _ => by fun_prop) (fun n => ae_of_all _ fun ω => ?_) (by simp) ?_⟩
  · rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (hn _ _)
  · have hg : Continuous (fun x : ℝ => ENNReal.ofReal (Real.exp (-t * x))) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    filter_upwards [hae] with ω hω
    exact hg.continuousAt.tendsto.comp hω

variable {ΩX ΩY S : Type*} [_inst1 : MeasurableSpace ΩX] [_inst2 : MeasurableSpace ΩY] [_inst3 : MeasurableSpace S] (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ℝ → ΩX → S → ℝ) (Ψ : ℝ → ΩY → S → ℝ) (hΦ : ∀ r, DOZZ.IsCenteredGaussianField PX (Φ r)) (hΨ : ∀ r, DOZZ.IsCenteredGaussianField PY (Ψ r)) (ν : Measure S) [_inst11 : IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c)

include ΩX ΩY S _inst1 _inst2 _inst3 PX PY Φ Ψ hΦ hΨ ν _inst11 h hh hhb in
/-- A field-chaos Laplace comparison passes to limits in measure by bounded convergence. -/
theorem kahane_limit_field_laplace
     (γ t : ℝ) (ht : 0 ≤ t)
    (hcov : ∀ r, ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ r ω xy.1 * Φ r ω xy.2 ∂PX ≤ ∫ ω, Ψ r ω xy.1 * Ψ r ω xy.2 ∂PY)
    (hdiag : ∀ r, ∀ᵐ x ∂ν,
      ∫ ω, Φ r ω x ^ 2 ∂PX ≤ ∫ ω, Ψ r ω x ^ 2 ∂PY)
    (ZX : ΩX → ℝ) (ZY : ΩY → ℝ)
    (hXconv : TendstoInMeasure PX
      (fun r ω => (DOZZ.fieldChaosMass PX (Φ r) ν h γ ω).toReal) atTop ZX)
    (hYconv : TendstoInMeasure PY
      (fun r ω => (DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω).toReal) atTop ZY) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * ZX ω)) ∂PX ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * ZY ω)) ∂PY := by
  let := (hΦ 0).2 0 (fun i : Fin 0 => Fin.elim0 i) |>.1
  let := (hΨ 0).2 0 (fun i : Fin 0 => Fin.elim0 i) |>.1
  let fX := fun r ω => (DOZZ.fieldChaosMass PX (Φ r) ν h γ ω).toReal
  let fY := fun r ω => (DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω).toReal
  have hLap (r : ℝ) :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * fX r ω)) ∂PX ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * fY r ω)) ∂PY := by
    by_cases hνzero : ν = 0
    · simp [fX, fY, DOZZ.fieldChaosMass, hνzero]
    have : Nonempty S := by
      obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hνzero)
      exact ⟨x⟩
    let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
    apply kahane_field_laplace_of_nonzero_finite_measure_eq PX PY (Φ r) (Ψ r)
      (hΦ r) (hΨ r) νf (fun hz => hνzero (congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hz))
      h hh hhb γ t ht (hcov r)
    simpa [νf, DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hdiag r
  exact le_of_tendsto_of_tendsto
    (tendsto_lintegral_laplace_of_inMeasure PX t ht (fun n => fX n)
      (fun n => (centeredGaussianField_fieldChaosMass_measurable PX (Φ n) (hΦ n) ν h hh γ).ennreal_toReal)
      (fun _ _ => ENNReal.toReal_nonneg) ZX (hXconv.comp tendsto_natCast_atTop_atTop))
    (tendsto_lintegral_laplace_of_inMeasure PY t ht (fun n => fY n)
      (fun n => (centeredGaussianField_fieldChaosMass_measurable PY (Ψ n) (hΨ n) ν h hh γ).ennreal_toReal)
      (fun _ _ => ENNReal.toReal_nonneg) ZY (hYconv.comp tendsto_natCast_atTop_atTop))
    (Eventually.of_forall fun n : ℕ => hLap n)

include ΩX ΩY S _inst1 _inst2 _inst3 PX PY Φ Ψ hΦ hΨ ν _inst11 h hh hhb in
/-- Negative-power field comparison passes to limits in measure. The finite-cutoff comparison is
first transferred to bounded Laplace tests, then Mellin integration recovers the possibly infinite
negative moments of the limiting masses. -/
theorem kahane_limit_field_negative_power
     (γ q : ℝ) (hq : 0 < q)
    (hcov : ∀ r, ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ r ω xy.1 * Φ r ω xy.2 ∂PX ≤ ∫ ω, Ψ r ω xy.1 * Ψ r ω xy.2 ∂PY)
    (hdiag : ∀ r, ∀ᵐ x ∂ν,
      ∫ ω, Φ r ω x ^ 2 ∂PX ≤ ∫ ω, Ψ r ω x ^ 2 ∂PY)
    (ZX : ΩX → ℝ) (ZY : ΩY → ℝ)
    (hXconv : TendstoInMeasure PX
      (fun r ω => (DOZZ.fieldChaosMass PX (Φ r) ν h γ ω).toReal) atTop ZX)
    (hYconv : TendstoInMeasure PY
      (fun r ω => (DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω).toReal) atTop ZY) :
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZX ω)) (-q) ∂PX ≤
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZY ω)) (-q) ∂PY := by
  let := (hΦ 0).2 0 (fun i : Fin 0 => Fin.elim0 i) |>.1
  let := (hΨ 0).2 0 (fun i : Fin 0 => Fin.elim0 i) |>.1
  have hXmeas (r : ℝ) : AEMeasurable
      (fun ω => (DOZZ.fieldChaosMass PX (Φ r) ν h γ ω).toReal) PX :=
    (centeredGaussianField_fieldChaosMass_measurable PX (Φ r) (hΦ r) ν h hh γ).ennreal_toReal.aemeasurable
  have hYmeas (r : ℝ) : AEMeasurable
      (fun ω => (DOZZ.fieldChaosMass PY (Ψ r) ν h γ ω).toReal) PY :=
    (centeredGaussianField_fieldChaosMass_measurable PY (Ψ r) (hΨ r) ν h hh γ).ennreal_toReal.aemeasurable
  obtain ⟨ns, _, hXae⟩ := hXconv.exists_seq_tendsto_ae'
  obtain ⟨ms, _, hYae⟩ := hYconv.exists_seq_tendsto_ae'
  have hZX : ∀ᵐ ω ∂PX, 0 ≤ ZX ω := by
    filter_upwards [hXae] with ω hω
    exact ge_of_tendsto' hω (fun _ => ENNReal.toReal_nonneg)
  have hZY : ∀ᵐ ω ∂PY, 0 ≤ ZY ω := by
    filter_upwards [hYae] with ω hω
    exact ge_of_tendsto' hω (fun _ => ENNReal.toReal_nonneg)
  rw [nonneg_rpow_neg_lintegral_eq_weighted_laplace PX ZX hZX (hXconv.aemeasurable hXmeas) q hq,
    nonneg_rpow_neg_lintegral_eq_weighted_laplace PY ZY hZY (hYconv.aemeasurable hYmeas) q hq]
  apply mul_le_mul_right
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply mul_le_mul_right
  simpa [mul_comm, neg_mul] using
    kahane_limit_field_laplace PX PY Φ Ψ hΦ hΨ ν h hh hhb γ t ht.le
      hcov hdiag ZX ZY hXconv hYconv


end DOZZ.Proofs
