/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionSpatialLaw
public import DOZZ.GMC.Moments.InversionAnnularUniqueness
public import DOZZ.GMC.Moments.ChaosLawFDDLimit

/-! Finite-cutoff law transport for admissible chaos test integrals. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Distributions ENNReal
open DOZZ.Assembly

namespace DOZZ.Proofs

/-- The cutoff chaos law retains its coupling to auxiliary finite coordinates. -/
theorem admissibleLogChaos_cutoff_joint_vector_law_of_fdd
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ) (Z : Ω' → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P' U dens ε₁ Z)
    [IsFiniteMeasure (logRegularizationReference U dens)]
    {k m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ))
    (hfU : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ U)
    (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (γ r : ℝ) (hrY : Real.exp (-r) ≤ ε₀) (hrZ : Real.exp (-r) ≤ ε₁)
    (hfdd : ∀ n (xs : Fin n → ℂ),
      P.map (fun ω => (V ω, fun i => Y ω (Real.exp (-r)) (xs i))) =
      P'.map (fun ω => (V' ω, fun i => Z ω (Real.exp (-r)) (xs i)))) :
    P.map (fun ω => (V ω, fun j => regularizedLogChaosTestMass P U dens Y γ r ω (f j))) =
      P'.map (fun ω => (V' ω, fun j => regularizedLogChaosTestMass P' U dens Z γ r ω (f j))) := by
  let ε := Real.exp (-r)
  have hv (x : ℂ) : (∫ ω, Y ω ε x ^ 2 ∂P) = ∫ ω, Z ω ε x ^ 2 ∂P' := by
    have hMY : Measurable (fun ω => (V ω, fun (_ : Fin 1) => Y ω ε x)) :=
      hV.prodMk (measurable_pi_iff.mpr (fun _ => (hY.measurableAtScale ε).comp
        (measurable_id.prodMk measurable_const)))
    have hMZ : Measurable (fun ω => (V' ω, fun (_ : Fin 1) => Z ω ε x)) :=
      hV'.prodMk (measurable_pi_iff.mpr (fun _ => (hZ.measurableAtScale ε).comp
        (measurable_id.prodMk measurable_const)))
    have ht := congrArg (fun μ : Measure ((Fin k → ℝ) × (Fin 1 → ℝ)) => ∫ v, (v.2 0) ^ 2 ∂μ)
      (hfdd 1 (fun _ => x))
    have hφ : Measurable (fun v : (Fin k → ℝ) × (Fin 1 → ℝ) => (v.2 0) ^ 2) := by fun_prop
    change (∫ v, (v.2 0) ^ 2 ∂P.map (fun ω => (V ω, fun (_ : Fin 1) => Y ω ε x))) =
      ∫ v, (v.2 0) ^ 2 ∂P'.map (fun ω => (V' ω, fun (_ : Fin 1) => Z ω ε x)) at ht
    rw [integral_map hMY.aemeasurable hφ.aestronglyMeasurable,
      integral_map hMZ.aemeasurable hφ.aestronglyMeasurable] at ht
    exact ht
  let variance  := fun x => ∫ ω, Y ω ε x ^ 2 ∂P
  have hvariance : Measurable variance := by
    have ht := admissibleLogRegularization_variance_measurable P U dens ε₀ Y hY ε
    simpa only [variance, gaussianVariance, gaussianCovariance, pow_two] using ht
  let ν : FiniteMeasure ℂ := ⟨logRegularizationReference U dens, inferInstance⟩
  let z  := fun j x t => f j x *
    Real.exp (γ * t - γ ^ 2 / 2 * variance x)
  have hz j : Measurable (fun p : ℂ × ℝ => z j p.1 p.2) := by
    fun_prop
  have hiY j := admissibleCutoff_integrand_integrable_ae P U dens ε₀ Y hY
      (tsupport (f j : ℂ → ℝ)) (hfc j) (hfU j) γ r hrY ‖f j‖ (f j)
      (f j).continuous.measurable
      (fun x => by simpa only [← Real.norm_eq_abs] using (f j).norm_coe_le_norm x)
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  have hiZ j : ∀ᵐ ω ∂P', Integrable (fun x => z j x (Z ω ε x)) (ν : Measure ℂ) := by
    have ht := admissibleCutoff_integrand_integrable_ae P' U dens ε₁ Z hZ
      (tsupport (f j : ℂ → ℝ)) (hfc j) (hfU j) γ r hrZ ‖f j‖ (f j)
      (f j).continuous.measurable
      (fun x => by simpa only [← Real.norm_eq_abs] using (f j).norm_coe_le_norm x)
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
    simpa only [z, variance, hv, ε, ν, FiniteMeasure.toMeasure_mk] using ht
  have ht := spatialIntegral_joint_vector_law_of_fdd_finite ν
    (fun ω x => Y ω ε x) (fun ω x => Z ω ε x) V V' hV hV' z
    (hY.measurableAtScale ε) (hZ.measurableAtScale ε) hz hiY hiZ hfdd
  simpa only [z, variance, ν, ε, FiniteMeasure.toMeasure_mk, regularizedLogChaosTestMass, hv] using ht

section
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Compatible cutoff laws pass to limiting chaos jointly with their auxiliary coordinates. -/
theorem admissibleLogChaos_limit_joint_vector_law_of_fdd
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ) (Z : Ω' → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P' U dens ε₁ Z)
    [IsFiniteMeasure (logRegularizationReference U dens)]
    (γ : ℝ) (M : Ω → Measure ℂ) (N : Ω' → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P U dens Y γ M)
    (hN : IsAdmissibleGMCVersion P' U dens Z γ N)
    {k : ℕ} (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (hfdd : ∀ ε, 0 < ε → ε ≤ min ε₀ ε₁ → ∀ n (xs : Fin n → ℂ),
      P.map (fun ω => (V ω, fun i => Y ω ε (xs i))) =
      P'.map (fun ω => (V' ω, fun i => Z ω ε (xs i))))
    {m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ))
    (hfU : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ U) :
    P.map (fun ω => (V ω, fun j => ∫ x, f j x ∂M ω)) =
      P'.map (fun ω => (V' ω, fun j => ∫ x, f j x ∂N ω)) := by
  have hT : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have heps  :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hT
  have hmin  := lt_min hY.cutoffPositive hZ.cutoffPositive
  obtain ⟨L, hL⟩ := eventually_atTop.mp (heps.eventually (gt_mem_nhds hmin))
  let t  := fun n => ((L + n : ℕ) : ℝ)
  have ht : Tendsto t atTop atTop := by
    simpa only [t, Nat.add_comm, Function.comp_def] using hT.comp (tendsto_add_atTop_nat L)
  have hb n  := (hL (L + n) (Nat.le_add_right L n)).le
  have hmY r j  :=
    admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ r (f j) (f j).continuous.measurable
  have hmZ r j  :=
    admissibleCutoffIntegral_measurable P' U dens ε₁ Z hZ γ r (f j) (f j).continuous.measurable
  apply gmc_limit_joint_test_vector_law V V' hV.aemeasurable hV'.aemeasurable
    (fun n ω j => regularizedLogChaosTestMass P U dens Y γ (t n) ω (f j))
    (fun n ω j => regularizedLogChaosTestMass P' U dens Z γ (t n) ω (f j))
    (fun ω j => ∫ x, f j x ∂M ω) (fun ω j => ∫ x, f j x ∂N ω)
  · intro n
    exact (measurable_pi_iff.mpr (fun j => hmY (t n) j)).aemeasurable
  · intro n
    exact (measurable_pi_iff.mpr (fun j => hmZ (t n) j)).aemeasurable
  · apply AEMeasurable.of_eval
    intro j
    exact ((hM.2.2.2 (f j) (hfc j) (hfU j)).aestronglyMeasurable
      (fun r => (hmY r j).aestronglyMeasurable)).aemeasurable
  · apply AEMeasurable.of_eval
    intro j
    exact ((hN.2.2.2 (f j) (hfc j) (hfU j)).aestronglyMeasurable
      (fun r => (hmZ r j).aestronglyMeasurable)).aemeasurable
  · intro n
    exact admissibleLogChaos_cutoff_joint_vector_law_of_fdd P P' U dens ε₀ ε₁ Y Z hY hZ
      f hfc hfU V V' hV hV' γ (t n) ((hb n).trans (min_le_left _ _))
      ((hb n).trans (min_le_right _ _))
      (hfdd _ (Real.exp_pos _) (hb n))
  · intro j
    exact (hM.2.2.2 (f j) (hfc j) (hfU j)).comp ht
  · intro j
    exact (hN.2.2.2 (f j) (hfc j) (hfU j)).comp ht

end


end DOZZ.Proofs
