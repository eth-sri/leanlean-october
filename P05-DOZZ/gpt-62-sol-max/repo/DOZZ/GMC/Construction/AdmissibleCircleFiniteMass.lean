/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.AdmissibleCircleTestFatou
public import DOZZ.GMC.Construction.ReferenceMeasureFinite
public import DOZZ.GMC.Construction.FiniteMeasureTotalize
public import DOZZ.GMC.Construction.ReferenceMeasureTight
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import DOZZ.GMC.Construction.CircleCutoffTestMass
public import DOZZ.GMC.CircleAverageCutoffIntensity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousMap.CompactlySupported
public import DOZZ.GMC.ConvergenceApproximation

/-! An admissible whole-plane circle-chaos version has finite expected total mass. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Distributions CompactlySupported

noncomputable section

namespace DOZZ.Proofs

private theorem exists_compact_test_cutoff {K O : Set ℂ} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) : ∃ φ : BoundedContinuousFunction ℂ ℝ,
      EqOn φ 1 K ∧ EqOn φ 0 Oᶜ ∧ HasCompactSupport (φ : ℂ → ℝ) ∧ ∀ x, φ x ∈ Icc 0 1 := by
  obtain ⟨φ, h₁, h₀, hc, hb⟩ := exists_continuous_one_zero_of_isCompact hK hO.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hKO)
  exact ⟨(⟨φ, hc⟩ : C_c(ℂ, ℝ)).toBoundedContinuousFunction, h₁, h₀, hc, hb⟩

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) (M : Ω → Measure ℂ)
  (hM : IsAdmissibleGMCVersion P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ M)
include Ω X hX Xc hXc γ hM

/-- Testing compact subsets by Urysohn functions bounds the expected mass on every open set. -/
private theorem admissibleCircleVersion_expected_open_le {O : Set ℂ} (hO : IsOpen O) :
    ∫⁻ ω, M ω O ∂P ≤ gmcReferenceMeasure O := by
  let β := P.bind M
  have hc (K U : Set ℂ) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) : β K ≤ gmcReferenceMeasure U := by
    obtain ⟨f, hf₁, hf₀, hfK, hf⟩ := exists_compact_test_cutoff hK hU hKU
    have hf0 (x) : 0 ≤ f x := (hf x).1
    rw [show β K = _ from Measure.bind_apply hK.measurableSet hM.1.aemeasurable]
    refine (lintegral_mono (g := fun ω => ENNReal.ofReal (∫ x, f x ∂M ω)) fun ω => ?_).trans
      ((admissibleCircleVersion_expected_test_le P X hX Xc hXc γ M hM f hf0 hfK).trans ?_)
    · letI : IsFiniteMeasureOnCompacts (M ω) := ⟨fun L hL => hM.2.2.1 ω L hL (subset_univ L)⟩
      exact (f.continuous.integrable_of_hasCompactSupport hfK).measure_le_integral
        (ae_of_all _ hf0) (fun x hx => ge_of_eq (hf₁ hx))
    · letI : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
      rw [← ofReal_integral_eq_lintegral_ofReal (f.integrable _) (ae_of_all _ hf0)]
      exact integral_le_measure (fun x _ => (hf x).2) (fun x hx => (hf₀ hx).le)
  let := hO.locallyCompactSpace
  let K n := Subtype.val '' compactCovering O n
  have hm : Monotone K := fun _ _ h => image_mono (compactCovering_subset O h)
  have hcover : ⋃ n, K n = O := by
    simp only [K, ← image_iUnion, iUnion_compactCovering, image_univ, Subtype.range_coe]
  rw [← Measure.bind_apply hO.measurableSet hM.1.aemeasurable]
  conv_lhs => rw [← hcover, hm.measure_iUnion]
  exact iSup_le fun n => hc _ _ ((isCompact_compactCovering O n).image continuous_subtype_val)
    hO (fun _ ⟨x, _, hx⟩ => hx ▸ x.2)

/-- An admissible whole-plane circle-chaos version is finite almost surely. -/
theorem admissibleCircleVersion_finite_ae : ∀ᵐ ω ∂P, IsFiniteMeasure (M ω) := by
  have h := admissibleCircleVersion_expected_open_le P X hX Xc hXc γ M hM isOpen_univ
  filter_upwards [ae_lt_top ((Measure.measurable_coe MeasurableSet.univ).comp hM.1)
    (h.trans_lt gmcReferenceMeasure_univ_ne_top.lt_top).ne] with ω hω
  exact ⟨hω⟩

end

/-- Cutting off a test on the complement of `K` costs at most its sup norm times the tail mass. -/
private theorem test_cutoff_error_le (μ : Measure ℂ) [IsFiniteMeasure μ]
    (f φ : BoundedContinuousFunction ℂ ℝ) {K : Set ℂ} (hK : MeasurableSet K)
    (h₁ : EqOn φ 1 K) (hφ : ∀ x, φ x ∈ Icc 0 1) :
    dist (∫ x, f x ∂μ) (∫ x, (f * φ) x ∂μ) ≤ ‖f‖ * (μ Kᶜ).toReal := by
  rw [dist_eq_norm, ← integral_sub (f.integrable μ) ((f * φ).integrable μ)]
  let g := Kᶜ.indicator fun _ : ℂ => ‖f‖
  have hg : Integrable g μ := (integrable_const _).indicator hK.compl
  refine (norm_integral_le_of_norm_le hg (ae_of_all _ fun x => ?_)).trans (le_of_eq ?_)
  · change ‖f x - f x * φ x‖ ≤ g x
    by_cases hx : x ∈ K
    · simp [g, hx, h₁ hx]
    · rw [show f x - f x * φ x = f x * (1 - φ x) by ring, norm_mul,
        Real.norm_eq_abs (1 - φ x), abs_of_nonneg (sub_nonneg.mpr (hφ x).2)]
      simp only [g, mem_compl_iff, hx, not_false_eq_true, indicator_of_mem]
      exact (mul_le_of_le_one_right (norm_nonneg _) (sub_le_self _ (hφ x).1)).trans (f.norm_coe_le_norm x)
  · rw [show g = _ from rfl, integral_indicator_const _ hK.compl, Measure.real_def, smul_eq_mul, mul_comm]

section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A common intensity bound gives a uniform probability bound for the cutoff error. -/
private theorem test_cutoff_probability_bound {P : Measure Ω}
    {M : Ω → Measure ℂ} (hm : Measurable M) (hf : ∀ᵐ ω ∂P, IsFiniteMeasure (M ω))
    (f φ : BoundedContinuousFunction ℂ ℝ) {K : Set ℂ} (hK : MeasurableSet K)
    (h₁ : EqOn φ 1 K) (hφ : ∀ x, φ x ∈ Icc 0 1) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ dist (∫ x, f x ∂M ω) (∫ x, (f * φ) x ∂M ω)} ≤
      (∫⁻ ω, M ω Kᶜ ∂P) / ENNReal.ofReal (ε / (‖f‖ + 1)) := by
  let q := ENNReal.ofReal (ε / (‖f‖ + 1))
  have hq : 0 < q := ENNReal.ofReal_pos.mpr (by positivity)
  refine (measure_mono_ae (t := {ω | q ≤ M ω Kᶜ}) ?_).trans
    (meas_ge_le_lintegral_div ((Measure.measurable_coe hK.compl).comp hm).aemeasurable hq.ne' ENNReal.ofReal_ne_top)
  filter_upwards [hf] with ω hω he
  letI := hω
  change q ≤ M ω Kᶜ
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
  apply (div_le_iff₀ (by positivity)).mpr
  have h := he.trans (test_cutoff_error_le (M ω) f φ hK h₁ hφ)
  linarith [ENNReal.toReal_nonneg (a := M ω Kᶜ)]

/-- An admissible whole-plane circle version, after modification on one null set, satisfies the
global bounded-continuous-test convergence predicate `IsGMCOf`. -/
theorem admissibleCircleVersion_to_IsGMCOf
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (M : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ M) :
    ∃ N : Ω → Measure ℂ,
      (∀ ω, IsFiniteMeasure (N ω)) ∧ IsGMCOf P X γ N ∧ ∀ᵐ ω ∂P, N ω = M ω := by
  obtain ⟨N, hNm, hNf, hNM⟩ := exists_everywhere_finite_measure_version P M hM.1
    (admissibleCircleVersion_finite_ae P X hX Xc hXc γ M hM)
  refine ⟨N, hNf, ⟨hNf, Xc, hXc, fun f => ?_⟩, hNM⟩
  refine tendstoInMeasure_of_probApprox fun ε hε δ hδ => ?_
  let q := ENNReal.ofReal (ε / (‖f‖ + 1))
  have hq : 0 < q := ENNReal.ofReal_pos.mpr (by positivity)
  have ht : Tendsto (fun n : ℕ => gmcReferenceMeasure (Metric.closedBall (0 : ℂ) (n : ℝ))ᶜ / q)
      atTop (𝓝 0) := by
    simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const gmcReferenceMeasure_compl_closedBall_tendsto_zero
      (b := q) (Or.inr hq.ne')
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.mp ht δ hδ).exists
  let K := Metric.closedBall (0 : ℂ) (n : ℝ)
  have hK : MeasurableSet K := measurableSet_closedBall
  obtain ⟨φ, hφK, -, hφc, hφ⟩ := exists_compact_test_cutoff (isCompact_closedBall (0 : ℂ) (n : ℝ))
    isOpen_univ (subset_univ K)
  let g := f * φ
  let μ := fun r ω => regularizedGMC P Xc γ r ω
  have hgc : HasCompactSupport (g : ℂ → ℝ) := hφc.mul_left
  have hlim : TendstoInMeasure P (fun r ω => ∫ x, g x ∂μ r ω) atTop (fun ω => ∫ x, g x ∂N ω) :=
    TendstoInMeasure.congr
      (fun r => ae_of_all _ fun ω => circleCutoff_testMass_eq_regularizedGMC P X hX Xc hXc γ r ω g)
      (hNM.mono fun ω h => congrArg (fun m => ∫ x, g x ∂m) h.symm) (hM.2.2.2 g hgc (subset_univ _))
  refine ⟨_, _, hlim, Eventually.of_forall fun r => ?_, ?_⟩
  · have hb := test_cutoff_probability_bound (regularizedGMC_measurable P X hX Xc hXc γ r)
      (regularizedGMC_finite_ae P X hX Xc hXc γ r) f φ hK hφK hφ hε
    exact hb.trans (le_of_eq (congrArg (· / q)
      (regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ r Kᶜ hK.compl)) |>.trans hn)
  · rw [show {ω | ε ≤ dist (∫ x, g x ∂N ω) (∫ x, f x ∂N ω)} =
        {ω | ε ≤ dist (∫ x, f x ∂N ω) (∫ x, g x ∂N ω)} by ext ω; simp only [mem_setOf_eq, dist_comm]]
    refine (test_cutoff_probability_bound hNm (ae_of_all _ hNf) f φ hK hφK hφ hε).trans ?_
    have hN : ∫⁻ ω, N ω Kᶜ ∂P ≤ gmcReferenceMeasure Kᶜ := by
      rw [lintegral_congr_ae (hNM.mono fun ω h => congrArg (fun m : Measure ℂ => m Kᶜ) h)]
      exact admissibleCircleVersion_expected_open_le P X hX Xc hXc γ M hM
        Metric.isClosed_closedBall.isOpen_compl
    exact (ENNReal.div_le_div_right hN q).trans hn

end

end DOZZ.Proofs
