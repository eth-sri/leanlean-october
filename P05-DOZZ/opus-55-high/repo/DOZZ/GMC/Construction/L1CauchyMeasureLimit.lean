/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.FatouInMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Fatou transfers a uniform L¹ Cauchy bound to a limit in measure. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- If a real family is uniformly Cauchy in expected absolute difference and converges in
measure, its distance in expected absolute value to the limit obeys the same eventual bound. -/
theorem lintegral_abs_sub_limit_le_of_uniform_l1_cauchy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : ℝ → Ω → ℝ) (G : Ω → ℝ)
    (hFmeas : ∀ r, Measurable (F r))
    (hFG : TendstoInMeasure P F atTop G)
    (r R C : ℝ)
    (hbound : ∀ s, R ≤ s →
      ∫⁻ ω, ENNReal.ofReal |F r ω - F s ω| ∂P ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ENNReal.ofReal |F r ω - G ω| ∂P ≤ ENNReal.ofReal C := by
  obtain ⟨ns, hnsTop, hseqMeasure⟩ := hFG.exists_seq_tendstoInMeasure_atTop
  obtain ⟨nsub, hnsub, hae⟩ := hseqMeasure.exists_seq_tendsto_ae
  let ms := ns ∘ nsub
  have hmsTop : Tendsto ms atTop atTop := hnsTop.comp hnsub.tendsto_atTop
  let Q : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal |F r ω - F (ms n) ω|
  have hQmeas : ∀ n, Measurable (Q n) := by
    fun_prop
  have hQlim : ∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop
      (𝓝 (ENNReal.ofReal |F r ω - G ω|)) := by
    filter_upwards [hae] with ω hω
    have hsub : Tendsto (fun n => F r ω - F (ms n) ω) atTop
        (𝓝 _) := tendsto_const_nhds.sub hω
    exact (ENNReal.continuous_ofReal.tendsto _).comp hsub.abs
  have hliminf : (fun ω => liminf (fun n => Q n ω) atTop) =ᵐ[P]
      fun ω => ENNReal.ofReal |F r ω - G ω| := by
    filter_upwards [hQlim] with ω hω
    exact hω.liminf_eq
  have hEventual :=
    hmsTop.eventually (eventually_ge_atTop R)
  have hIntegralBound : ∀ᶠ n : ℕ in atTop,
      ∫⁻ ω, Q n ω ∂P ≤ ENNReal.ofReal C := by
    filter_upwards [hEventual] with n hn
    simpa [Q, ms] using hbound _ hn
  calc
    ∫⁻ ω, ENNReal.ofReal |F r ω - G ω| ∂P =
        ∫⁻ ω, liminf (fun n => Q n ω) atTop ∂P := lintegral_congr_ae hliminf.symm
    _ ≤ liminf (fun n => ∫⁻ ω, Q n ω ∂P) atTop := lintegral_liminf_le hQmeas
    _ ≤ ENNReal.ofReal C := liminf_le_of_frequently_le' hIntegralBound.frequently


end DOZZ.Proofs
