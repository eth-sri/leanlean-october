/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.GMC.IsCenteredJointlyGaussian
import DOZZ.Statements.GMC.GaussianVariance
import DOZZ.Statements.GMC.IsAdmissibleLogRegularization
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import DOZZ.GMC.FiniteChaosMean

/-! Uniform-barrier cutoff construction for compact GMC tests. -/


open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

noncomputable def gaussianRectangleIndicator {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Z : Ω → ι → ℝ) (b c : ι → ℝ) : Ω → ℝ :=
  fun ω => if ∀ i, Z ω i + c i ≤ b i then 1 else 0

private theorem gaussianRectangleIndicator_aestronglyMeasurable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (b c : ι → ℝ) : AEStronglyMeasurable (gaussianRectangleIndicator Z b c) P := by
  let S : Set (ι → ℝ) := {z | ∀ i, z i + c i ≤ b i}
  have hS : MeasurableSet S := by
    have hEq : (⋂ i, {z : ι → ℝ | z i + c i ≤ b i}) = S := by
      ext z
      simp [S]
    rw [← hEq]
    apply MeasurableSet.iInter
    intro i
    have hcoord : Measurable (fun z : ι → ℝ => z i + c i) := by fun_prop
    exact measurableSet_le hcoord measurable_const
  have hZae : AEMeasurable Z P := by
    apply AEMeasurable.of_eval
    intro i
    exact hZ.2.1 i
  have hF : Measurable (fun z : ι → ℝ => if z ∈ S then (1 : ℝ) else 0) :=
    Measurable.ite hS measurable_const measurable_const
  have hEq : gaussianRectangleIndicator Z b c =
      (fun z : ι → ℝ => if z ∈ S then (1 : ℝ) else 0) ∘ Z := by
    funext ω
    rfl
  rw [hEq]
  exact hF.comp_aemeasurable hZae |>.aestronglyMeasurable

private noncomputable def gaussianRectangleShiftBandIndicator
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Z : Ω → ι → ℝ) (b c d : ι → ℝ) (i : ι) : Ω → ℝ :=
  Set.indicator {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
      (max (b i - c i) (b i - d i))} (fun _ => (1 : ℝ))

private theorem gaussianRectangleShiftBandIndicator_nonneg
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Z : Ω → ι → ℝ) (b c d : ι → ℝ) (i : ι) (ω : Ω) :
    0 ≤ gaussianRectangleShiftBandIndicator Z b c d i ω := by
  change 0 ≤ Set.indicator {ω' | Z ω' i ∈ Set.Icc
    (min (b i - c i) (b i - d i)) (max (b i - c i) (b i - d i))}
    (fun _ => (1 : ℝ)) ω
  by_cases hi : Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
      (max (b i - c i) (b i - d i))
  · have hi' : ω ∈ {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
        (max (b i - c i) (b i - d i))} := hi
    rw [Set.indicator_of_mem hi']
    norm_num
  · have hi' : ω ∉ {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
        (max (b i - c i) (b i - d i))} := hi
    rw [Set.indicator_of_notMem hi']

private theorem gaussianRectangleShiftBandIndicator_aestronglyMeasurable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (b c d : ι → ℝ) (i : ι) :
    AEStronglyMeasurable (gaussianRectangleShiftBandIndicator Z b c d i) P := by
  let S : Set (ι → ℝ) := {z | z i ∈ Set.Icc (min (b i - c i) (b i - d i))
    (max (b i - c i) (b i - d i))}
  have hS : MeasurableSet S := by
    change MeasurableSet ((fun z : ι → ℝ => z i) ⁻¹'
      Set.Icc (min (b i - c i) (b i - d i)) (max (b i - c i) (b i - d i)))
    exact isClosed_Icc.measurableSet.preimage (measurable_pi_apply i)
  have hZae : AEMeasurable Z P := by
    apply AEMeasurable.of_eval
    intro j
    exact hZ.2.1 j
  have hF : Measurable (fun z : ι → ℝ => if z ∈ S then (1 : ℝ) else 0) :=
    Measurable.ite hS measurable_const measurable_const
  have hEq : gaussianRectangleShiftBandIndicator Z b c d i =
      (fun z : ι → ℝ => if z ∈ S then (1 : ℝ) else 0) ∘ Z := by
    funext ω
    simp [S, gaussianRectangleShiftBandIndicator, Set.indicator]
  rw [hEq]
  exact hF.comp_aemeasurable hZae |>.aestronglyMeasurable

private theorem gaussianRectangleShiftBandIndicator_pointwise
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Z : Ω → ι → ℝ) (b c d : ι → ℝ) (ω : Ω) :
    |gaussianRectangleIndicator Z b c ω - gaussianRectangleIndicator Z b d ω| ≤
      ∑ i, gaussianRectangleShiftBandIndicator Z b c d i ω := by
  classical
  by_cases hc : ∀ i, Z ω i + c i ≤ b i
  · by_cases hd : ∀ i, Z ω i + d i ≤ b i
    · have hsum : 0 ≤ ∑ j, gaussianRectangleShiftBandIndicator Z b c d j ω :=
        Finset.sum_nonneg fun j _ => gaussianRectangleShiftBandIndicator_nonneg Z b c d j ω
      simpa [gaussianRectangleIndicator, hc, hd] using hsum
    · obtain ⟨i, hi⟩ := not_forall.mp hd
      have hgt : b i < Z ω i + d i := lt_of_not_ge hi
      have hupper : Z ω i ≤ b i - c i := by linarith [hc i]
      have hlower : b i - d i < Z ω i := by linarith
      have hmem : Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i)) := by
        constructor
        · exact (min_le_right _ _).trans hlower.le
        · exact hupper.trans (le_max_left _ _)
      have hband : gaussianRectangleShiftBandIndicator Z b c d i ω = 1 := by
        change Set.indicator {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} (fun _ => (1 : ℝ)) ω = 1
        have hmem' : ω ∈ {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
            (max (b i - c i) (b i - d i))} := hmem
        rw [Set.indicator_of_mem hmem']
      have hsum : 1 ≤ ∑ j, gaussianRectangleShiftBandIndicator Z b c d j ω := by
        calc
          1 = gaussianRectangleShiftBandIndicator Z b c d i ω := hband.symm
          _ ≤ ∑ j, gaussianRectangleShiftBandIndicator Z b c d j ω :=
            Finset.single_le_sum
              (fun j _ => gaussianRectangleShiftBandIndicator_nonneg Z b c d j ω)
              (Finset.mem_univ i)
      simpa [gaussianRectangleIndicator, hc, hd] using hsum
  · by_cases hd : ∀ i, Z ω i + d i ≤ b i
    · obtain ⟨i, hi⟩ := not_forall.mp hc
      have hupper : Z ω i ≤ b i - d i := by linarith [hd i]
      have hlower : b i - c i < Z ω i := by linarith
      have hmem : Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i)) := by
        constructor
        · exact (min_le_left _ _).trans hlower.le
        · exact hupper.trans (le_max_right _ _)
      have hband : gaussianRectangleShiftBandIndicator Z b c d i ω = 1 := by
        change Set.indicator {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} (fun _ => (1 : ℝ)) ω = 1
        have hmem' : ω ∈ {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
            (max (b i - c i) (b i - d i))} := hmem
        rw [Set.indicator_of_mem hmem']
      have hsum : 1 ≤ ∑ j, gaussianRectangleShiftBandIndicator Z b c d j ω := by
        calc
          1 = gaussianRectangleShiftBandIndicator Z b c d i ω := hband.symm
          _ ≤ ∑ j, gaussianRectangleShiftBandIndicator Z b c d j ω :=
            Finset.single_le_sum
              (fun j _ => gaussianRectangleShiftBandIndicator_nonneg Z b c d j ω)
              (Finset.mem_univ i)
      simpa [gaussianRectangleIndicator, hc, hd] using hsum
    · have hnonneg : 0 ≤ ∑ j, gaussianRectangleShiftBandIndicator Z b c d j ω :=
        Finset.sum_nonneg fun j _ => gaussianRectangleShiftBandIndicator_nonneg Z b c d j ω
      simpa [gaussianRectangleIndicator, hc, hd] using hnonneg

/-- A real Gaussian with variance at least one assigns an interval no more mass than its
Lebesgue length. This gives a covariance-independent boundary-strip bound for finite Gaussian
rectangle probabilities. -/
theorem gaussianReal_interval_le_length_of_variance_ge_one
    (μ : ℝ) (v : ℝ≥0) (hv : 1 ≤ (v : ℝ)) (a b : ℝ) (hab : a ≤ b) :
    gaussianReal μ v (Set.Icc a b) ≤ ENNReal.ofReal (b - a) := by
  have hvne : v ≠ 0 := by
    intro hz
    rw [hz] at hv
    norm_num at hv
  have hpdf (x : ℝ) : gaussianPDFReal μ v x ≤ 1 := by
    rw [gaussianPDFReal_def]
    have harg : (1 : ℝ) ≤ 2 * Real.pi * (v : ℝ) := by
      nlinarith [Real.pi_gt_three]
    have hden : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (v : ℝ)) := by
      have h := Real.sqrt_le_sqrt harg
      simpa using h
    have hdenpos : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) := by positivity
    have hinv : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ≤ 1 := by
      rwa [inv_le_one₀ hdenpos]
    have hargExp : -(x - μ) ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
      have hnum : -(x - μ) ^ 2 ≤ 0 := neg_nonpos.mpr (sq_nonneg (x - μ))
      have hdenExp : 0 < 2 * (v : ℝ) := by positivity
      exact div_nonpos_of_nonpos_of_nonneg hnum hdenExp.le
    have hexp : Real.exp (-(x - μ) ^ 2 / (2 * (v : ℝ))) ≤ 1 := (Real.exp_le_one_iff.mpr hargExp)
    calc
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          Real.exp (-(x - μ) ^ 2 / (2 * (v : ℝ))) ≤
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ 1 := by simpa using hinv
  have hpdfInt : IntegrableOn (gaussianPDFReal μ v) (Set.Icc a b) :=
    (integrable_gaussianPDFReal μ v).integrableOn
  have hconstInt : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
    integrableOn_const (by simp)
  have hInt : (∫ x in Set.Icc a b, gaussianPDFReal μ v x) ≤ b - a := by
    calc
      (∫ x in Set.Icc a b, gaussianPDFReal μ v x) ≤
          ∫ x in Set.Icc a b, (1 : ℝ) :=
        setIntegral_mono_on hpdfInt hconstInt isClosed_Icc.measurableSet fun x _ => hpdf x
      _ = b - a := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le hab]
        simp
  rw [gaussianReal_apply_eq_integral μ hvne (Set.Icc a b)]
  exact ENNReal.ofReal_le_ofReal hInt

/-- A coordinate of a centered jointly Gaussian vector with variance at least one has a
covariance-independent interval probability bound. -/
theorem gaussian_coordinate_interval_probability_le_length_of_variance_ge_one
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (i : ι) (hv : 1 ≤ gaussianVariance P (fun ω => Z ω i))
    (a b : ℝ) (hab : a ≤ b) :
    P {ω | Z ω i ∈ Set.Icc a b} ≤ ENNReal.ofReal (b - a) := by
  obtain ⟨v, hmap, _, hvar⟩ := coordinate_mean_variance P Z hZ i
  have hv' : 1 ≤ (v : ℝ) := by simpa [hvar] using hv
  have hprob : P {ω | Z ω i ∈ Set.Icc a b} =
      gaussianReal 0 v (Set.Icc a b) := by
    let Zi : Ω → ℝ := fun ω => Z ω i
    have hZi : AEMeasurable Zi P := hZ.2.1 i
    calc
      P {ω | Z ω i ∈ Set.Icc a b} = P (Zi ⁻¹' Set.Icc a b) := by rfl
      _ = P.map Zi (Set.Icc a b) := by
        symm
        exact Measure.map_apply_of_aemeasurable hZi isClosed_Icc.measurableSet
      _ = gaussianReal 0 v (Set.Icc a b) := by rw [hmap]
  rw [hprob]
  exact gaussianReal_interval_le_length_of_variance_ge_one 0 v hv' a b hab

/-- The finite Gaussian rectangle probability is Lipschitz in its deterministic shift, with a
modulus independent of all correlations, as soon as every marginal variance is at least one. -/
theorem finite_gaussian_rectangle_probability_shift_lipschitz
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (b : ι → ℝ) (hv : ∀ i, 1 ≤ gaussianVariance P (fun ω => Z ω i))
    (c d : ι → ℝ) :
    |(∫ ω, gaussianRectangleIndicator Z b c ω ∂P) -
      (∫ ω, gaussianRectangleIndicator Z b d ω ∂P)| ≤
        (Fintype.card ι : ℝ) * ‖c - d‖ := by
  classical
  have hPfinite : IsFiniteMeasure P := by
    refine ⟨?_⟩
    rw [hZ.1.measure_univ]
    exact ENNReal.one_lt_top
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) P := (integrable_const_iff (μ := P) (c := (1 : ℝ))).2 (Or.inr hPfinite)
  have hrectAEM (e : ι → ℝ) :
      AEStronglyMeasurable (gaussianRectangleIndicator Z b e) P :=
    gaussianRectangleIndicator_aestronglyMeasurable P Z hZ b e
  have hrectBound (e : ι → ℝ) :
      ∀ᵐ ω ∂P, ‖gaussianRectangleIndicator Z b e ω‖ ≤ 1 := by
    apply ae_of_all
    intro ω
    dsimp [gaussianRectangleIndicator]
    split_ifs <;> norm_num
  have hrectInt (e : ι → ℝ) :
      Integrable (gaussianRectangleIndicator Z b e) P :=
    hone.mono' (hrectAEM e) (hrectBound e)
  have hbandAEM (i : ι) :
      AEStronglyMeasurable (gaussianRectangleShiftBandIndicator Z b c d i) P :=
    gaussianRectangleShiftBandIndicator_aestronglyMeasurable P Z hZ b c d i
  have hbandBound (i : ι) :
      ∀ᵐ ω ∂P, ‖gaussianRectangleShiftBandIndicator Z b c d i ω‖ ≤ 1 := by
    apply ae_of_all
    intro ω
    by_cases hi : Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
        (max (b i - c i) (b i - d i))
    · change ‖Set.indicator {ω' | Z ω' i ∈ Set.Icc
        (min (b i - c i) (b i - d i)) (max (b i - c i) (b i - d i))}
        (fun _ => (1 : ℝ)) ω‖ ≤ 1
      have hi' : ω ∈ {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} := hi
      rw [Set.indicator_of_mem hi']
      norm_num
    · change ‖Set.indicator {ω' | Z ω' i ∈ Set.Icc
        (min (b i - c i) (b i - d i)) (max (b i - c i) (b i - d i))}
        (fun _ => (1 : ℝ)) ω‖ ≤ 1
      have hi' : ω ∉ {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} := hi
      rw [Set.indicator_of_notMem hi']
      norm_num
  have hbandInt (i : ι) :
      Integrable (gaussianRectangleShiftBandIndicator Z b c d i) P :=
    hone.mono' (hbandAEM i) (hbandBound i)
  have hbandNull (i : ι) : NullMeasurableSet
      {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
        (max (b i - c i) (b i - d i))} P :=
    (hZ.2.1 i).nullMeasurableSet_preimage isClosed_Icc.measurableSet
  have hbandIntegral (i : ι) :
      (∫ ω, gaussianRectangleShiftBandIndicator Z b c d i ω ∂P) =
        P.real {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} := by
    let S : Set Ω := {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
      (max (b i - c i) (b i - d i))}
    calc
      (∫ ω, gaussianRectangleShiftBandIndicator Z b c d i ω ∂P) =
          ∫ ω, Set.indicator S (fun _ => (1 : ℝ)) ω ∂P := by
            rfl
      _ = ∫ ω in S, (1 : ℝ) ∂P := integral_indicator₀ (hbandNull i)
      _ = P.real S := by rw [setIntegral_const]; simp
  have hbandProb (i : ι) :
      P.real {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
        (max (b i - c i) (b i - d i))} ≤ |c i - d i| := by
    let lo : ℝ := min (b i - c i) (b i - d i)
    let hi : ℝ := max (b i - c i) (b i - d i)
    have hlen : hi - lo = |c i - d i| := by
      dsimp [hi, lo]
      rw [max_sub_min_eq_abs]
      congr 1
      ring
    have hprob := gaussian_coordinate_interval_probability_le_length_of_variance_ge_one
      P Z hZ i (hv i) lo hi min_le_max
    have hprob' : P {ω | Z ω i ∈ Set.Icc lo hi} ≤ ENNReal.ofReal (hi - lo) := hprob
    rw [hlen] at hprob'
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob'
    rw [ENNReal.toReal_ofReal (abs_nonneg (c i - d i))] at hreal
    change (P {ω | Z ω i ∈ Set.Icc lo hi}).toReal ≤ |c i - d i|
    assumption
  have hsumInt : Integrable
      (fun ω => ∑ i, gaussianRectangleShiftBandIndicator Z b c d i ω) P :=
    integrable_finsetSum Finset.univ (fun i _ => hbandInt i)
  have hsumIntegral :
      (∫ ω, ∑ i, gaussianRectangleShiftBandIndicator Z b c d i ω ∂P) =
        ∑ i, P.real {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      exact hbandIntegral i
    · intro i _
      exact hbandInt i
  have hsumBound :
      (∑ i, |c i - d i|) ≤ (Fintype.card ι : ℝ) * ‖c - d‖ := by
    calc
      (∑ i, |c i - d i|) ≤ ∑ i, ‖c - d‖ := by
        apply Finset.sum_le_sum
        intro i _
        simpa using norm_le_pi_norm (c - d) i
      _ = (Fintype.card ι : ℝ) * ‖c - d‖ := by simp
  have hEq :
      (∫ ω, gaussianRectangleIndicator Z b c ω ∂P) -
        (∫ ω, gaussianRectangleIndicator Z b d ω ∂P) =
          ∫ ω, gaussianRectangleIndicator Z b c ω -
            gaussianRectangleIndicator Z b d ω ∂P := by
    rw [integral_sub (hrectInt c) (hrectInt d)]
  calc
    |(∫ ω, gaussianRectangleIndicator Z b c ω ∂P) -
        (∫ ω, gaussianRectangleIndicator Z b d ω ∂P)| =
          ‖∫ ω, gaussianRectangleIndicator Z b c ω -
            gaussianRectangleIndicator Z b d ω ∂P‖ := by
              rw [hEq, Real.norm_eq_abs]
    _ ≤ ∫ ω, ‖gaussianRectangleIndicator Z b c ω -
          gaussianRectangleIndicator Z b d ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ∑ i, gaussianRectangleShiftBandIndicator Z b c d i ω ∂P :=
      integral_mono ((hrectInt c).sub (hrectInt d)).norm hsumInt
        (fun ω => by simpa [Real.norm_eq_abs] using
          gaussianRectangleShiftBandIndicator_pointwise Z b c d ω)
    _ = ∑ i, P.real {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} := hsumIntegral
    _ ≤ ∑ i, |c i - d i| := Finset.sum_le_sum fun i _ => hbandProb i
    _ ≤ (Fintype.card ι : ℝ) * ‖c - d‖ := hsumBound

/-- Uniform convergence of every coordinate shift implies uniform convergence of finite Gaussian
rectangle probabilities, with a bound independent of the correlations and of the parameterized
Gaussian vectors. -/
theorem finite_gaussian_rectangle_probability_two_shift_tendsto_uniformly
    {Ω α ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Γ : Set ℝ) (S : Set α)
    (Z : α → Ω → ι → ℝ)
    (hZ : ∀ a ∈ S, IsCenteredJointlyGaussian P (Z a))
    (b : ι → ℝ)
    (hv : ∀ a ∈ S, ∀ i, 1 ≤ gaussianVariance P (fun ω => Z a ω i))
    (c : ℝ → ℝ → ℝ → α → ι → ℝ) (d : ℝ → α → ι → ℝ)
    (hshift : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε ε' : ℝ, 0 < ε → ε ≤ δ → 0 < ε' → ε' ≤ δ →
        ∀ γ ∈ Γ, ∀ a ∈ S, ∀ i, |c ε ε' γ a i - d γ a i| < η) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε ε' : ℝ, 0 < ε → ε ≤ δ → 0 < ε' → ε' ≤ δ →
        ∀ γ ∈ Γ, ∀ a ∈ S,
          |(∫ ω, gaussianRectangleIndicator (Z a) b (c ε ε' γ a) ω ∂P) -
            (∫ ω, gaussianRectangleIndicator (Z a) b (d γ a) ω ∂P)| < η := by
  intro η hη
  let η' : ℝ := η / ((Fintype.card ι : ℝ) + 1)
  have hη' : 0 < η' := by
    dsimp [η']
    positivity
  obtain ⟨δ, hδ, hcoord⟩ := hshift η' hη'
  refine ⟨δ, hδ, ?_⟩
  intro ε ε' hε hεcut hε' hε'cut γ hγ a ha
  have hnorm : ‖c ε ε' γ a - d γ a‖ ≤ η' := by
    rw [pi_norm_le_iff_of_nonneg (le_of_lt hη')]
    intro i
    simpa [Pi.sub_apply, Real.norm_eq_abs] using
      (hcoord ε ε' hε hεcut hε' hε'cut γ hγ a ha i).le
  have hprob := finite_gaussian_rectangle_probability_shift_lipschitz
    P (Z a) (hZ a ha) b (hv a ha) (c ε ε' γ a) (d γ a)
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hcardη : (Fintype.card ι : ℝ) * η' < η := by
    dsimp [η']
    field_simp
    nlinarith
  calc
    _ ≤ (Fintype.card ι : ℝ) * ‖c ε ε' γ a - d γ a‖ := hprob
    _ ≤ (Fintype.card ι : ℝ) * η' :=
      mul_le_mul_of_nonneg_left hnorm hcard
    _ < η := hcardη

end DOZZ.Proofs
