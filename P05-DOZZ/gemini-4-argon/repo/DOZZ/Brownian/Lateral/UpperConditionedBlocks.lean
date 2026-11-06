/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.BrownianWindowExponential
public import DOZZ.Brownian.Lateral.ReflectionInverse
public import DOZZ.Brownian.Williams.ThinBand

/-!
# Positive blocks under the upper-conditioned Brownian law

The source comparison uses negative-drift Brownian motion conditioned below one. Its actual
normalized whole-path law is already constructed by Williams. Here its unit-block envelopes
are bounded by the truncated endpoint moment and an independent Brownian unit-increment
exponential. The endpoint bound gives summable decay. The resulting envelopes also bound blocks
of any given lateral measure, without splitting its half-lines into independent measures.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- A positive unit-block exponential envelope on the continuous path carrier. -/
noncomputable def positiveBlockEnvelope (γ : ℝ) (n : ℝ≥0) (p : BrownianPath) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * p n + |γ| * brownianUnitNorm (brownianShiftPath n p)))

/-- The envelope is measurable as a function of the actual full path. -/
theorem measurable_positiveBlockEnvelope γ (n : ℝ≥0) :
    Measurable (positiveBlockEnvelope γ n) := by
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_const.mul (ContinuousMap.measurable_eval n)).add
      (measurable_const.mul (continuous_brownianUnitNorm.measurable.comp (continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id))))))


/-- A block of the positive half-cylinder for an arbitrary continuous radial path and measure. -/
noncomputable def positiveLateralBlock (γ : ℝ) (n : ℝ≥0)
    (p : BrownianPath) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (n : ℝ) ((n : ℝ) + 1),
    ENNReal.ofReal (Real.exp (γ * p (Real.toNNReal s))) ∂μ


/-- Independent radial and lateral inputs factor the arbitrary given-chaos block estimate. -/
theorem positiveLateralBlock_moment_le_independent_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ)
    (hγ : 0 ≤ γ) (hq : 0 ≤ q) (n : ℝ≥0)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : AEMeasurable Z P) (hi : IndepFun B Z P) :
    (∫⁻ ω, (positiveLateralBlock γ n (B ω) (Z ω)) ^ q ∂P) ≤
      (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω) ∂P) *
        (∫⁻ ω, (Z ω (Ioc (n : ℝ) ((n : ℝ) + 1))) ^ q ∂P) := by
  have positiveLateralBlock_le_envelope p (μ : Measure ℝ) : positiveLateralBlock γ n p μ ≤ positiveBlockEnvelope γ n p * μ (Ioc (n : ℝ) ((n : ℝ) + 1)) := by
    rw [← setLIntegral_const]
    apply setLIntegral_mono' measurableSet_Ioc
    intro s hs
    let t : ℝ≥0 := ⟨s - (n : ℝ), sub_nonneg.mpr hs.1.le⟩
    have ht : t ∈ Icc 0 (1 : ℝ≥0) := ⟨bot_le, by exact_mod_cast (by
      change s - (n : ℝ) ≤ 1
      linarith [hs.2])⟩
    have he : Real.toNNReal s = n + t := by
      apply NNReal.eq_iff.mpr
      rw [Real.coe_toNNReal s (n.coe_nonneg.trans hs.1.le), NNReal.coe_add]
      change s = (n : ℝ) + (s - (n : ℝ))
      ring
    have hn := ((brownianShiftPath n p).restrict (Icc 0 (1 : ℝ≥0))).norm_coe_le_norm ⟨t, ht⟩
    change |p (n + t) - p n| ≤ brownianUnitNorm (brownianShiftPath n p) at hn
    have hex : p (Real.toNNReal s) ≤ p n + brownianUnitNorm (brownianShiftPath n p) := by
      rw [he]
      have := (le_abs_self (p (n + t) - p n)).trans hn
      linarith
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hγ]
    nlinarith
  have positiveBlockEnvelope_rpow p (hγ : 0 ≤ γ) (hq : 0 ≤ q) : (positiveBlockEnvelope γ n p) ^ q = positiveBlockEnvelope (q * γ) n p := by
    rw [positiveBlockEnvelope, ennreal_exp_rpow]
    unfold positiveBlockEnvelope
    rw [abs_of_nonneg hγ, abs_of_nonneg (mul_nonneg hq hγ)]
    congr 2
    ring
  let f := positiveBlockEnvelope (q * γ) n
  let g : Measure ℝ → ℝ≥0∞ := fun μ => (μ (Ioc (n : ℝ) ((n : ℝ) + 1))) ^ q
  have hf : Measurable f := measurable_positiveBlockEnvelope _ _
  have hg : Measurable g := ENNReal.continuous_rpow_const.measurable.comp
    (Measure.measurable_coe measurableSet_Ioc)
  have he := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hf.comp_aemeasurable hB) (hg.comp_aemeasurable hZ) (hi.comp hf hg)
  change (∫⁻ ω, f (B ω) * g (Z ω) ∂P) =
    (∫⁻ ω, f (B ω) ∂P) * (∫⁻ ω, g (Z ω) ∂P) at he
  rw [← he]
  apply lintegral_mono
  intro ω
  have hb := ENNReal.rpow_le_rpow (positiveLateralBlock_le_envelope (B ω) (Z ω)) hq
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq,
    positiveBlockEnvelope_rpow (B ω) hγ hq] at hb
  exact hb



/-- Integrating the exponential radial weight over the positive half-line. -/
noncomputable def positiveLateralMass (γ : ℝ) (p : BrownianPath) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (γ * p (Real.toNNReal s))) ∂μ

/-- The actual positive half-mass is precisely the sum of its unit blocks. -/
theorem positiveLateralMass_eq_tsum_blocks γ p (μ : Measure ℝ) :
    positiveLateralMass γ p μ = ∑' n : ℕ, positiveLateralBlock γ n p μ := by
  have positive_unit_intervals_pairwise_disjoint : Pairwise (fun m n : ℕ => Disjoint (Ioc (m : ℝ) ((m : ℝ) + 1)) (Ioc (n : ℝ) ((n : ℝ) + 1))) := by
    intro m n hmn
    apply disjoint_left.mpr
    intro x hm hn
    rcases lt_or_gt_of_ne hmn with h | h
    · have he : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.add_one_le_iff.mpr h
      exact not_lt_of_ge (hm.2.trans he) hn.1
    · have he : (n : ℝ) + 1 ≤ m := by exact_mod_cast Nat.add_one_le_iff.mpr h
      exact not_lt_of_ge (hn.2.trans he) hm.1
  have positive_unit_intervals_union : (⋃ n : ℕ, Ioc (n : ℝ) ((n : ℝ) + 1)) = Ioi (0 : ℝ) := by
    ext s
    constructor
    · intro hs
      obtain ⟨n, hn⟩ := mem_iUnion.mp hs
      exact lt_of_le_of_lt (Nat.cast_nonneg _) hn.1
    · intro hs
      let n := Nat.ceil s - 1
      have he : (n : ℝ) + 1 = (Nat.ceil s : ℝ) := by exact_mod_cast (Nat.sub_add_cancel (Nat.one_le_ceil_iff.mpr hs))
      apply mem_iUnion.mpr
      refine ⟨n, ?_, ?_⟩
      · have hc := Nat.ceil_lt_add_one hs.le
        linarith
      · rw [he]
        exact Nat.le_ceil s
  unfold positiveLateralMass positiveLateralBlock
  rw [← positive_unit_intervals_union]
  exact lintegral_iUnion (fun _ => measurableSet_Ioc)
    positive_unit_intervals_pairwise_disjoint _


/-- Infinite Minkowski assembly for nonnegative block masses, using their actual root moments. -/
theorem lintegral_tsum_rpow_le_root_moments_power
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ℕ → Ω → ℝ≥0∞)
    (hF : ∀ n, AEMeasurable (F n) P) (q : ℝ) (hq : 1 ≤ q)
    : (∫⁻ ω, (∑' n, F n ω) ^ q ∂P) ≤
      (∑' n, (∫⁻ ω, (F n ω) ^ q ∂P) ^ (1 / q)) ^ q := by
  have lintegral_finset_rpow_root_le_sum S : (∫⁻ ω, (∑ n ∈ S, F n ω) ^ q ∂P) ^ (1 / q) ≤ ∑ n ∈ S, (∫⁻ ω, (F n ω) ^ q ∂P) ^ (1 / q) := by
    classical
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, lintegral_zero,
        ENNReal.zero_rpow_of_pos (lt_of_lt_of_le zero_lt_one hq),
        ENNReal.zero_rpow_of_pos (one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hq))]
      exact le_rfl
    | @insert n S hn ih =>
      have hs : AEMeasurable (fun ω => ∑ i ∈ S, F i ω) P :=
        by
          convert Finset.aemeasurable_sum S (fun i _ => hF i) using 1
          funext ω
          exact (Finset.sum_apply ω S F).symm
      have hb := ENNReal.lintegral_Lp_add_le (hF n) hs hq
      change (∫⁻ ω, (F n ω + ∑ i ∈ S, F i ω) ^ q ∂P) ^ (1 / q) ≤
        (∫⁻ ω, (F n ω) ^ q ∂P) ^ (1 / q) +
          (∫⁻ ω, (∑ i ∈ S, F i ω) ^ q ∂P) ^ (1 / q) at hb
      simp only [Finset.sum_insert hn]
      exact hb.trans (add_le_add le_rfl ih)
  have hqp := lt_of_lt_of_le zero_lt_one hq
  have hb : ∀ N : ℕ, (∫⁻ ω, (∑ n ∈ Finset.range N, F n ω) ^ q ∂P) ≤ (∑' n, (∫⁻ ω, (F n ω) ^ q ∂P) ^ (1 / q)) ^ q := by
    intro N
    have he := ENNReal.rpow_le_rpow ((lintegral_finset_rpow_root_le_sum (Finset.range N)).trans (ENNReal.sum_le_tsum (Finset.range N))) hqp.le
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hqp.ne', ENNReal.rpow_one] at he
    exact he
  have hm : ∀ N : ℕ, AEMeasurable
      (fun ω => (∑ n ∈ Finset.range N, F n ω) ^ q) P := fun N =>
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (by
        classical
        convert Finset.aemeasurable_sum (Finset.range N) (fun n _ => hF n) using 1
        funext ω
        exact (Finset.sum_apply ω (Finset.range N) F).symm)
  exact le_of_tendsto' (lintegral_tendsto_of_tendsto_of_monotone hm (ae_of_all _ (by intro ω N M hNM; apply ENNReal.rpow_le_rpow _ hqp.le; exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM) (fun _ _ _ => bot_le))) (ae_of_all _ (fun ω => ENNReal.continuous_rpow_const.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum (fun n => F n ω))))) hb

end DOZZ.Proofs
