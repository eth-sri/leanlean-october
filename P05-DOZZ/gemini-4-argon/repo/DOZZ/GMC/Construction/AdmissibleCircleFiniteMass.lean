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
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! An admissible whole-plane circle-chaos version has finite expected total mass. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Distributions CompactlySupported

noncomputable section

namespace DOZZ.Proofs

private def massCutoffFun (n : ℕ) : ℂ → ℝ :=
  fun x => max 0 (min 1 ((n : ℝ) + 1 - ‖x‖))

private theorem massCutoffFun_continuous n : Continuous (massCutoffFun n) := by
  change Continuous (fun x : ℂ => max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)))
  fun_prop

private theorem massCutoffFun_support (n : ℕ) :
    Function.support (massCutoffFun n) ⊆ Metric.closedBall (0 : ℂ) ((n : ℝ) + 1) := by
  intro x hx
  change massCutoffFun n x ≠ 0 at hx
  by_contra hout
  exact hx (by dsimp [massCutoffFun]; rw [max_eq_left (le_trans (min_le_right _ _) (show (n : ℝ) + 1 - ‖x‖ ≤ 0 by rw [Metric.mem_closedBall, (show dist x (0 : ℂ) = ‖x‖ by simp)] at hout; linarith))])

private def massCutoffCc (n : ℕ) : C_c(ℂ, ℝ) := by
  let f : C(ℂ, ℝ) := ⟨massCutoffFun n, massCutoffFun_continuous n⟩
  have hcompact : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)) (massCutoffFun_support n)
  exact ⟨f, hcompact⟩

private def massCutoff (n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  (massCutoffCc n).toBoundedContinuousFunction






private def cutoffTest (f : BoundedContinuousFunction ℂ ℝ) (R : ℕ) :
    BoundedContinuousFunction ℂ ℝ := f * massCutoff R






private def tailInnerFun (R : ℕ) (x : ℂ) : ℝ :=
  max 0 (min 1 (‖x‖ - (R : ℝ)))




private def tailTestFun (R n : ℕ) (x : ℂ) : ℝ :=
  tailInnerFun R x * massCutoffFun n x

private theorem tailTestFun_continuous R n : Continuous (tailTestFun R n) := by
  exact ((show Continuous (tailInnerFun R) by change Continuous (fun x => max 0 (min 1 (‖x‖ - (R : ℝ)))); fun_prop)).mul (massCutoffFun_continuous n)

private theorem tailTestFun_support (R n : ℕ) :
    Function.support (tailTestFun R n) ⊆ Metric.closedBall (0 : ℂ) ((n : ℝ) + 1) := by
  intro x hx
  change tailTestFun R n x ≠ 0 at hx
  by_contra hout
  have hcut : massCutoffFun n x = 0 := by
    by_contra hne
    apply hout
    exact massCutoffFun_support n (by change massCutoffFun n x ≠ 0; exact hne)
  exact hx (by simp [tailTestFun, hcut])

private def tailTestCc (R n : ℕ) : C_c(ℂ, ℝ) := by
  let f : C(ℂ, ℝ) := ⟨tailTestFun R n, tailTestFun_continuous R n⟩
  have hcompact : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)) (tailTestFun_support R n)
  exact ⟨f, hcompact⟩

private def tailTest (R n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  (tailTestCc R n).toBoundedContinuousFunction












/-- An admissible whole-plane circle version, after modification on one null set, satisfies the
global bounded-continuous-test convergence predicate `IsGMCOf`. -/
theorem admissibleCircleVersion_to_IsGMCOf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ Xc (hXc : IsCircleAverage P X Xc)
    (M : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ M) :
    ∃ N : Ω → Measure ℂ,
      (∀ ω, IsFiniteMeasure (N ω)) ∧ IsGMCOf P X γ N ∧ ∀ᵐ ω ∂P, N ω = M ω := by
  classical
  have tailInnerFun_nonneg R x : 0 ≤ tailInnerFun R x := le_max_left _ _
  have massCutoff_mono x : Monotone fun n => massCutoff n x := by
    intro n m hnm
    simp only [massCutoff, massCutoffCc,
      CompactlySupportedContinuousMap.toBoundedContinuousFunction]
    change max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)) ≤
      max 0 (min 1 ((m : ℝ) + 1 - ‖x‖))
    exact max_le_max le_rfl (min_le_min le_rfl (by
      have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      linarith))
  have tailTest_mono R x : Monotone fun n => tailTest R n x := by
    intro n m hnm
    simp only [tailTest, tailTestCc,
      CompactlySupportedContinuousMap.toBoundedContinuousFunction]
    change tailInnerFun R x * massCutoffFun n x ≤
      tailInnerFun R x * massCutoffFun m x
    exact mul_le_mul_of_nonneg_left (massCutoff_mono x hnm) (tailInnerFun_nonneg R x)
  have massCutoff_le_one n x : massCutoff n x ≤ 1 := by
    simp only [massCutoff, massCutoffCc,
      CompactlySupportedContinuousMap.toBoundedContinuousFunction]
    change max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)) ≤ 1
    exact max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩
  have tailTest_le_inner R n x : tailTest R n x ≤ tailInnerFun R x := by
    simp only [tailTest, tailTestCc, CompactlySupportedContinuousMap.toBoundedContinuousFunction]
    change tailInnerFun R x * massCutoffFun n x ≤ tailInnerFun R x
    linarith only [mul_nonneg (tailInnerFun_nonneg R x) (sub_nonneg.mpr (by simpa [massCutoff, massCutoffCc, CompactlySupportedContinuousMap.toBoundedContinuousFunction] using (massCutoff_le_one n x)))]
  have massCutoff_nonneg n x : 0 ≤ massCutoff n x := by
    simp [massCutoff, massCutoffCc, massCutoffFun,
      CompactlySupportedContinuousMap.toBoundedContinuousFunction]
  have tailTest_nonneg R n x : 0 ≤ tailTest R n x := by
    change 0 ≤ tailInnerFun R x * massCutoffFun n x
    exact mul_nonneg (tailInnerFun_nonneg R x) (massCutoff_nonneg n x)
  have tailTest_hasCompactSupport (R : ℕ) (n : ℕ) : HasCompactSupport (tailTest R n : ℂ → ℝ) := (tailTestCc R n).hasCompactSupport
  have massCutoff_tendsto_one x : Tendsto (fun n : ℕ => massCutoff n x) atTop (𝓝 1) := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    have hEvent : ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 - ‖x‖ ≥ 1 := Filter.eventually_atTop.2 ⟨N, fun n hn => by
        have : 0 ≤ (n : ℝ) - ‖x‖ := sub_nonneg.mpr (le_trans (show ‖x‖ < (N : ℝ) by exact_mod_cast hN).le (by exact_mod_cast hn))
        linarith⟩
    exact tendsto_const_nhds.congr' ((show ∀ᶠ n : ℕ in atTop, massCutoff n x = 1 by filter_upwards [hEvent] with n hn; simp [massCutoff, massCutoffCc, CompactlySupportedContinuousMap.toBoundedContinuousFunction, massCutoffFun, hn]).mono fun _ hn => hn.symm)
  have circleIntegral_cutoff_error_le (μ : Measure ℂ) [IsFiniteMeasure μ] f (R : ℕ) : ‖∫ x, f x ∂μ - ∫ x, cutoffTest f R x ∂μ‖ ≤ ‖f‖ * (μ (Metric.closedBall (0 : ℂ) (R : ℝ))ᶜ).toReal := by
    classical
    have massCutoff_eq_one_of_mem_closedBall (n : ℕ) x (hx : x ∈ Metric.closedBall (0 : ℂ) (n : ℝ)) : massCutoff n x = 1 := by
      have : ‖x‖ ≤ (n : ℝ) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hx
      have harg : 1 ≤ (n : ℝ) + 1 - ‖x‖ := by linarith
      simp [massCutoff, massCutoffCc, massCutoffFun,
        CompactlySupportedContinuousMap.toBoundedContinuousFunction, min_eq_left harg]
    let tail := (Metric.closedBall (0 : ℂ) (R : ℝ))ᶜ
    have htail := (Metric.isClosed_closedBall (x := (0 : ℂ)) (ε := (R : ℝ))).measurableSet.compl
    have hfmem : MemLp (fun x => f x) 1 μ :=
      MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
        (ae_of_all _ f.norm_coe_le_norm)
    have hfint : Integrable (fun x => f x) μ := hfmem.integrable (by norm_num)
    have hgf := (cutoffTest f R).continuous.measurable
    have hgmem : MemLp (fun x => cutoffTest f R x) 1 μ :=
      MemLp.of_bound hgf.aestronglyMeasurable ‖cutoffTest f R‖
        (ae_of_all _ (cutoffTest f R).norm_coe_le_norm)
    have hgint : Integrable (fun x => cutoffTest f R x) μ := hgmem.integrable (by norm_num)
    let d : ℂ → ℝ := fun x => f x - cutoffTest f R x
    have hdint := hfint.sub hgint
    have htailConst : Integrable (tail.indicator (fun _ : ℂ => ‖f‖)) μ := by
      have hcLp : MemLp (fun _ : ℂ => ‖f‖) 1 μ :=
        MemLp.of_bound (aestronglyMeasurable_const : AEStronglyMeasurable
          (fun _ : ℂ => ‖f‖) μ) ‖f‖ (ae_of_all _ fun _ => by simp)
      have hc : Integrable (fun _ : ℂ => ‖f‖) μ := hcLp.integrable (by norm_num)
      exact hc.indicator htail
    have hpoint : ∀ x, ‖d x‖ ≤ tail.indicator (fun _ : ℂ => ‖f‖) x := by
      intro x
      by_cases hx : x ∈ tail
      · have hχnonneg : 0 ≤ massCutoff R x := massCutoff_nonneg R x
        have := massCutoff_le_one R x
        have habs : |1 - massCutoff R x| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        have hdeq : d x = f x * (1 - massCutoff R x) := by
          change f x - f x * massCutoff R x = f x * (1 - massCutoff R x)
          ring
        rw [hdeq, Real.norm_eq_abs, abs_mul]
        simp [Set.indicator, hx]
        calc
          |f x| * |1 - massCutoff R x| ≤ |f x| := by
            simpa using mul_le_mul_of_nonneg_left habs (abs_nonneg (f x))
          _ ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
      · have hxball : x ∈ Metric.closedBall (0 : ℂ) (R : ℝ) := by
          simpa [tail, Set.mem_compl_iff] using hx
        have hχ := massCutoff_eq_one_of_mem_closedBall R x hxball
        have hdzero : d x = 0 := by simp [d, cutoffTest, hχ]
        simp [Set.indicator, hx, hdzero]
    calc
      ‖∫ x, f x ∂μ - ∫ x, cutoffTest f R x ∂μ‖ = ‖∫ x, d x ∂μ‖ := by
        rw [integral_sub hfint hgint]
      _ ≤ ∫ x, ‖d x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, tail.indicator (fun _ : ℂ => ‖f‖) x ∂μ :=
        integral_mono hdint.norm htailConst hpoint
      _ = ‖f‖ * (μ tail).toReal := by
        rw [integral_indicator_const ‖f‖ htail, Measure.real_def]
        simp [tail, smul_eq_mul]
        ring
  have massCutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (massCutoff n : ℂ → ℝ) := by
    exact (massCutoffCc n).hasCompactSupport
  have admissibleCircleVersion_expected_tail_le (R : ℕ) : ∫⁻ ω, M ω (Metric.closedBall (0 : ℂ) ((R : ℝ) + 1))ᶜ ∂P ≤ gmcReferenceMeasure (Metric.closedBall (0 : ℂ) (R : ℝ))ᶜ := by
    classical
    have tailInner_one_of_mem_compl_closedBall x (hx : x ∈ (Metric.closedBall (0 : ℂ) ((R : ℝ) + 1))ᶜ) : tailInnerFun R x = 1 := by
      have : (R : ℝ) + 1 < ‖x‖ := lt_of_not_ge (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
      dsimp [tailInnerFun]
      rw [min_eq_left (show 1 ≤ ‖x‖ - (R : ℝ) by linarith)]
      simp
    have tailInner_zero_of_mem_closedBall x (hx : x ∈ Metric.closedBall (0 : ℂ) (R : ℝ)) : tailInnerFun R x = 0 := by
      dsimp [tailInnerFun]
      rw [max_eq_left (le_trans (min_le_right _ _) (sub_nonpos.mpr (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)))]
    have tailTest_lintegral_tendsto (μ : Measure ℂ) : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (tailTest R n x) ∂μ) atTop (𝓝 (∫⁻ x, ENNReal.ofReal (tailInnerFun R x) ∂μ)) := by
      have tailTest_tendsto_inner x : Tendsto (fun n : ℕ => tailTest R n x) atTop (𝓝 (tailInnerFun R x)) := by
        simpa [tailTest, tailTestCc, tailTestFun,
          massCutoff, massCutoffCc, massCutoffFun,
          CompactlySupportedContinuousMap.toBoundedContinuousFunction] using (tendsto_const_nhds.mul (massCutoff_tendsto_one x))
      exact lintegral_tendsto_of_tendsto_of_monotone (fun n => (ENNReal.measurable_ofReal.comp (tailTest R n).continuous.measurable).aemeasurable) (ae_of_all _ fun x n m hnm => ENNReal.ofReal_le_ofReal (tailTest_mono R x hnm)) (by filter_upwards [] with x; exact ENNReal.tendsto_ofReal (tailTest_tendsto_inner x))
    have tailInnerFun_le_one x : tailInnerFun R x ≤ 1 := by
      dsimp [tailInnerFun]
      exact max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩
    let tail := (Metric.closedBall (0 : ℂ) (R : ℝ))ᶜ
    let tailLarge := (Metric.closedBall (0 : ℂ) ((R : ℝ) + 1))ᶜ
    let A : ℕ → Ω → ℝ≥0∞ := fun n ω =>
      ∫⁻ x, ENNReal.ofReal (tailTest R n x) ∂M ω
    let B : Ω → ℝ≥0∞ := fun ω => ∫⁻ x, ENNReal.ofReal (tailInnerFun R x) ∂M ω
    have hABound n : ∫⁻ ω, A n ω ∂P ≤ gmcReferenceMeasure tail := by
      have hcompare x :
          ENNReal.ofReal (tailTest R n x) ≤ tail.indicator (fun _ => (1 : ℝ≥0∞)) x := by
        by_cases hx : x ∈ tail
        · simpa [Set.indicator, hx] using ENNReal.ofReal_le_ofReal
            (tailTest_le_inner R n x |>.trans (tailInnerFun_le_one x))
        · have hball : x ∈ Metric.closedBall (0 : ℂ) (R : ℝ) := by
            simpa [tail, Set.mem_compl_iff] using hx
          have hzero : tailTest R n x = 0 := by
            have hle := tailTest_le_inner R n x
            rw [(tailInner_zero_of_mem_closedBall x hball)] at hle
            exact le_antisymm hle (tailTest_nonneg R n x)
          simp [Set.indicator, hx, hzero]
      calc
        ∫⁻ ω, A n ω ∂P =
            ∫⁻ ω, ENNReal.ofReal (∫ x, tailTest R n x ∂M ω) ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all _ (by intro ω; exact (ofReal_integral_eq_lintegral_ofReal (@Continuous.integrable_of_hasCompactSupport ℂ ℝ _ _ _ (M ω) inferInstance (tailTest R n) ⟨fun K hK => hM.2.2.1 ω K hK (Set.subset_univ K)⟩ (tailTest R n).continuous (tailTest_hasCompactSupport R n)) (ae_of_all _ (tailTest_nonneg R n))).symm)
        _ ≤ ∫⁻ x, ENNReal.ofReal (tailTest R n x) ∂gmcReferenceMeasure := (admissibleCircleVersion_expected_test_le P X hX Xc hXc γ M hM (tailTest R n) (tailTest_nonneg R n) (tailTest_hasCompactSupport R n))
        _ ≤ ∫⁻ x, tail.indicator (fun _ => (1 : ℝ≥0∞)) x ∂gmcReferenceMeasure :=
            lintegral_mono hcompare
        _ = gmcReferenceMeasure tail := by
            rw [lintegral_indicator_const ((Metric.isClosed_closedBall (x := (0 : ℂ)) (ε := (R : ℝ))).measurableSet.compl)]
            simp [tail]
    have hpoint ω : M ω tailLarge ≤ B ω := by
      have hcompare x :
          tailLarge.indicator (fun _ => (1 : ℝ≥0∞)) x ≤
            ENNReal.ofReal (tailInnerFun R x) := by
        by_cases hx : x ∈ tailLarge
        · have hone := tailInner_one_of_mem_compl_closedBall x (by simpa [tailLarge] using hx)
          simp [Set.indicator, hx, hone]
        · simp [Set.indicator, hx]
      calc
        M ω tailLarge = ∫⁻ x, tailLarge.indicator (fun _ => (1 : ℝ≥0∞)) x ∂M ω := by
          rw [lintegral_indicator_const ((Metric.isClosed_closedBall (x := (0 : ℂ)) (ε := (R : ℝ) + 1)).measurableSet.compl)]
          simp [tailLarge]
        _ ≤ B ω := lintegral_mono hcompare
    calc
      ∫⁻ ω, M ω tailLarge ∂P ≤ ∫⁻ ω, B ω ∂P := lintegral_mono hpoint
      _ ≤ gmcReferenceMeasure tail := (le_of_tendsto' (lintegral_tendsto_of_tendsto_of_monotone (fun n => ((fun n => (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp (tailTest R n).continuous.measurable)).comp hM.1) n).aemeasurable) (by apply ae_of_all; intro ω n m hnm; exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (tailTest_mono R x hnm)) (by apply ae_of_all; intro ω; exact tailTest_lintegral_tendsto (M ω))) hABound)
  have admissibleCircleVersion_finite_ae : ∀ᵐ ω ∂P, IsFiniteMeasure (M ω) := by
    have admissibleCircleVersion_expected_total_le : ∫⁻ ω, M ω Set.univ ∂P ≤ gmcReferenceMeasure Set.univ := by
      classical
      have massCutoff_lintegral_tendsto (μ : Measure ℂ) : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (massCutoff n x) ∂μ) atTop (𝓝 (μ Set.univ)) := by
        have hmeas n : AEMeasurable (fun x => ENNReal.ofReal (massCutoff n x)) μ := (ENNReal.measurable_ofReal.comp (massCutoff n).continuous.measurable).aemeasurable
        have h := lintegral_tendsto_of_tendsto_of_monotone hmeas (ae_of_all _ fun x n m hnm => ENNReal.ofReal_le_ofReal (massCutoff_mono x hnm)) (by filter_upwards [] with x; simpa using ENNReal.tendsto_ofReal (massCutoff_tendsto_one x))
        simpa using h
      let A : ℕ → Ω → ℝ≥0∞ := fun n ω =>
        ∫⁻ x, ENNReal.ofReal (massCutoff n x) ∂M ω
      have hABound n : ∫⁻ ω, A n ω ∂P ≤ gmcReferenceMeasure Set.univ := by
        calc
          ∫⁻ ω, A n ω ∂P =
              ∫⁻ ω, ENNReal.ofReal (∫ x, massCutoff n x ∂M ω) ∂P := by
                apply lintegral_congr_ae
                exact ae_of_all _ (by intro ω; exact (ofReal_integral_eq_lintegral_ofReal (@Continuous.integrable_of_hasCompactSupport ℂ ℝ _ _ _ (M ω) inferInstance (massCutoff n) ⟨fun K hK => hM.2.2.1 ω K hK (Set.subset_univ K)⟩ (massCutoff n).continuous (massCutoff_hasCompactSupport n)) (ae_of_all _ (massCutoff_nonneg n))).symm)
          _ ≤ ∫⁻ x, ENNReal.ofReal (massCutoff n x) ∂gmcReferenceMeasure := (admissibleCircleVersion_expected_test_le P X hX Xc hXc γ M hM (massCutoff n) (massCutoff_nonneg n) (massCutoff_hasCompactSupport n))
          _ ≤ gmcReferenceMeasure Set.univ := by
                calc
                  ∫⁻ x, ENNReal.ofReal (massCutoff n x) ∂gmcReferenceMeasure ≤
                      ∫⁻ x, (1 : ℝ≥0∞) ∂gmcReferenceMeasure := by
                        apply lintegral_mono
                        intro x
                        simpa using ENNReal.ofReal_le_ofReal (massCutoff_le_one n x)
                  _ = gmcReferenceMeasure Set.univ := by simp
      exact le_of_tendsto' (lintegral_tendsto_of_tendsto_of_monotone (fun n => ((fun n => (Measure.measurable_lintegral ((ENNReal.measurable_ofReal.comp (massCutoff n).continuous.measurable))) |>.comp hM.1) n).aemeasurable) (by apply ae_of_all; intro ω n m hnm; exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (massCutoff_mono x hnm)) (by apply ae_of_all; intro ω; exact massCutoff_lintegral_tendsto (M ω))) hABound
    filter_upwards [ae_lt_top ((Measure.measurable_coe MeasurableSet.univ).comp hM.1) (ne_of_lt (lt_of_le_of_lt (admissibleCircleVersion_expected_total_le) (lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top)))] with ω hω
    exact ⟨hω⟩
  have cutoffTest_hasCompactSupport f (R : ℕ) : HasCompactSupport (cutoffTest f R : ℂ → ℝ) := by
    have massCutoff_zero_of_not_mem_closedBall (n : ℕ) x (hx : x ∉ Metric.closedBall (0 : ℂ) ((n : ℝ) + 1)) : massCutoff n x = 0 := by
      have : (n : ℝ) + 1 < ‖x‖ := by
        have hnot : ¬ ‖x‖ ≤ (n : ℝ) + 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hx
        exact lt_of_not_ge hnot
      have harg : (n : ℝ) + 1 - ‖x‖ ≤ 0 := by linarith
      simp [massCutoff, massCutoffCc, massCutoffFun,
        CompactlySupportedContinuousMap.toBoundedContinuousFunction,
        max_eq_left (le_trans (min_le_right _ _) harg)]
    let g : ℂ → ℝ := fun x => f x * massCutoff R x
    have hgsupport : Function.support g ⊆ Metric.closedBall (0 : ℂ) ((R : ℝ) + 1) := by
      intro x hx
      change g x ≠ 0 at hx
      by_contra hout
      exact hx (by simp [g, (massCutoff_zero_of_not_mem_closedBall R x hout)])
    exact HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : ℂ) ((R : ℝ) + 1)) (by simpa [g, cutoffTest] using hgsupport)
  obtain ⟨N, hNmeas, hNfinite, hNM⟩ :=
    exists_everywhere_finite_measure_version P M hM.1 (admissibleCircleVersion_finite_ae)
  have hNtail (n : ℕ) :
      ∫⁻ ω, N ω (Metric.closedBall (0 : ℂ) ((n : ℝ) + 1))ᶜ ∂P ≤
        gmcReferenceMeasure (Metric.closedBall (0 : ℂ) (n : ℝ))ᶜ := by
    calc
      ∫⁻ ω, N ω (Metric.closedBall (0 : ℂ) ((n : ℝ) + 1))ᶜ ∂P =
          ∫⁻ ω, M ω (Metric.closedBall (0 : ℂ) ((n : ℝ) + 1))ᶜ ∂P := by
            apply lintegral_congr_ae
            filter_upwards [hNM] with ω hω
            rw [hω]
      _ ≤ gmcReferenceMeasure (Metric.closedBall (0 : ℂ) (n : ℝ))ᶜ :=
        admissibleCircleVersion_expected_tail_le n
  have hGlobal : ∀ f : BoundedContinuousFunction ℂ ℝ,
      TendstoInMeasure P
        (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => ∫ x, f x ∂N ω) := by
    intro f
    apply (tendstoInMeasure_iff_norm).2
    intro ε hε
    let B : ℝ := ‖f‖ + 1
    let q : ℝ≥0∞ := ENNReal.ofReal (ε / (3 * B))
    have : 0 < B := by dsimp [B]; linarith [norm_nonneg f]
    have hq0 : q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos hε (by positivity)))
    have hqtop : q ≠ ∞ := ENNReal.ofReal_ne_top
    let tail : ℕ → Set ℂ := fun n =>
      (Metric.closedBall (0 : ℂ) ((n + 1 : ℕ) : ℝ))ᶜ
    let referenceTail : ℕ → Set ℂ := fun n => (Metric.closedBall (0 : ℂ) (n : ℝ))ᶜ
    let cutoffTail : ℕ → ℝ → Ω → ℝ≥0∞ := fun n r ω =>
      regularizedGMC P Xc γ r ω (tail n)
    have htailSubset n : tail n ⊆ referenceTail n := by
      intro x hx
      have : (n : ℝ) + 1 < ‖x‖ := lt_of_not_ge (by simpa [(show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num [Nat.cast_add])] using (by simpa [tail, Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff] using hx))
      simpa [referenceTail, Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff] using
        (not_le_of_gt (show (n : ℝ) < ‖x‖ by linarith))
    have hcutMeas n r : Measurable (cutoffTail n r) := by
      exact (Measure.measurable_coe
        ((Metric.isClosed_closedBall (x := (0 : ℂ))
          (ε := ((n + 1 : ℕ) : ℝ))).measurableSet.compl)).comp
          (regularizedGMC_measurable P X hX Xc hXc γ r)
    have hcutExp n r :
        ∫⁻ ω, cutoffTail n r ω ∂P = gmcReferenceMeasure (tail n) := by
      exact regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ r (tail n)
        ((Metric.isClosed_closedBall (x := (0 : ℂ))
          (ε := ((n + 1 : ℕ) : ℝ))).measurableSet.compl)
    have hprobCore n : Tendsto
        (fun r => P {ω | ε / 3 ≤ ‖
          (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
          (∫ x, cutoffTest f (n + 1) x ∂N ω)‖}) atTop (𝓝 0) := by
      let fc := cutoffTest f (n + 1)
      simpa [fc, norm_sub_rev] using (tendstoInMeasure_iff_norm.mp (tendstoInMeasure_integral_after_ae_measure_change (fun r ω => ∫ x, fc x ∂regularizedGMC P Xc γ r ω) M N fc hNM (by exact TendstoInMeasure.congr (by intro r; exact Filter.Eventually.of_forall fun ω => (circleCutoff_testMass_eq_regularizedGMC P X hX Xc hXc γ r ω fc)) (Filter.Eventually.of_forall fun _ => rfl) (hM.2.2.2 fc (cutoffTest_hasCompactSupport f (n + 1)) (Set.subset_univ _)))) (ε / 3) (by positivity))
    have hboundError n r :
        P {ω | ε / 3 ≤ ‖
          (∫ x, f x ∂regularizedGMC P Xc γ r ω) -
          (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)‖} ≤
          gmcReferenceMeasure (referenceTail n) / q := by
      calc
        P {ω | ε / 3 ≤ ‖
            (∫ x, f x ∂regularizedGMC P Xc γ r ω) -
            (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)‖} ≤
            P {ω | q ≤ cutoffTail n r ω} := measure_mono_ae (by filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hfinite hω; exact (ENNReal.ofReal_le_iff_le_toReal (by exact measure_ne_top _ _)).2 (by apply (div_le_iff₀ (by positivity)).2; dsimp [B]; linarith only [(show ε / 3 ≤ ‖f‖ * (cutoffTail n r ω).toReal by exact hω.trans (by simpa [cutoffTail, tail] using (@circleIntegral_cutoff_error_le (regularizedGMC P Xc γ r ω) hfinite f (n + 1)))), (ENNReal.toReal_nonneg : 0 ≤ (cutoffTail n r ω).toReal)]))
        _ ≤ (∫⁻ ω, cutoffTail n r ω ∂P) / q :=
            meas_ge_le_lintegral_div (hcutMeas n r).aemeasurable hq0 hqtop
        _ = gmcReferenceMeasure (tail n) / q := by rw [hcutExp]
        _ ≤ gmcReferenceMeasure (referenceTail n) / q := by
          apply ENNReal.div_le_div_right
          exact measure_mono (htailSubset n)
    have hboundLimitError n :
        P {ω | ε / 3 ≤ ‖
          (∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖} ≤
          gmcReferenceMeasure (referenceTail n) / q := by
      calc
            P {ω | ε / 3 ≤ ‖
              (∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖} ≤
            P {ω | q ≤ N ω (tail n)} := measure_mono_ae (by filter_upwards [] with ω; intro hω; exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top (N ω) (tail n))).2 (by apply (div_le_iff₀ (by positivity)).2; dsimp [B]; linarith only [(show ε / 3 ≤ ‖f‖ * (N ω (tail n)).toReal by exact hω.trans (by simpa [tail] using (show ‖(∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖ ≤ ‖f‖ * (N ω (tail n)).toReal by simpa only [norm_sub_rev, tail, Nat.cast_add, Nat.cast_one] using (@circleIntegral_cutoff_error_le (N ω) (hNfinite ω) f (n + 1))))), (ENNReal.toReal_nonneg : 0 ≤ (N ω (tail n)).toReal)]))
        _ ≤ (∫⁻ ω, N ω (tail n) ∂P) / q :=
            meas_ge_le_lintegral_div
              ((Measure.measurable_coe
                ((Metric.isClosed_closedBall (x := (0 : ℂ))
                  (ε := ((n + 1 : ℕ) : ℝ))).measurableSet.compl)).comp
                hNmeas).aemeasurable hq0 hqtop
        _ ≤ gmcReferenceMeasure (referenceTail n) / q := by
          simpa [referenceTail] using (ENNReal.div_le_div_right (by simpa [tail, referenceTail, Nat.cast_add, Nat.cast_one] using hNtail n) q)
    have hEventBound n r :
        P {ω | ε ≤ ‖
            (∫ x, f x ∂regularizedGMC P Xc γ r ω) - (∫ x, f x ∂N ω)‖} ≤
          gmcReferenceMeasure (referenceTail n) / q +
            P {ω | ε / 3 ≤ ‖
              (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
              (∫ x, cutoffTest f (n + 1) x ∂N ω)‖} +
            gmcReferenceMeasure (referenceTail n) / q := by
      let E₁ : Set Ω := {ω | ε / 3 ≤ ‖
        (∫ x, f x ∂regularizedGMC P Xc γ r ω) -
        (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)‖}
      let E₂ : Set Ω := {ω | ε / 3 ≤ ‖
        (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
        (∫ x, cutoffTest f (n + 1) x ∂N ω)‖}
      let E₃ : Set Ω := {ω | ε / 3 ≤ ‖
        (∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖}
      have hsubset :
          {ω | ε ≤ ‖
            (∫ x, f x ∂regularizedGMC P Xc γ r ω) - (∫ x, f x ∂N ω)‖} ⊆
            E₁ ∪ (E₂ ∪ E₃) := by
        intro ω hω
        by_contra hnot
        have htriangle :
            ‖(∫ x, f x ∂regularizedGMC P Xc γ r ω) - (∫ x, f x ∂N ω)‖ ≤
              ‖(∫ x, f x ∂regularizedGMC P Xc γ r ω) -
                  (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)‖ +
              ‖(∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
                  (∫ x, cutoffTest f (n + 1) x ∂N ω)‖ +
              ‖(∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖ := by
          calc
            _ = ‖((∫ x, f x ∂regularizedGMC P Xc γ r ω) -
                  (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)) +
                  ((∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
                    (∫ x, cutoffTest f (n + 1) x ∂N ω)) +
                  ((∫ x, cutoffTest f (n + 1) x ∂N ω) -
                    (∫ x, f x ∂N ω))‖ := by congr 1; ring
            _ ≤ _ := by
              calc
                _ ≤ ‖((∫ x, f x ∂regularizedGMC P Xc γ r ω) -
                    (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)) +
                    ((∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
                      (∫ x, cutoffTest f (n + 1) x ∂N ω))‖ +
                    ‖(∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖ :=
                      norm_add_le
                        (((∫ x, f x ∂regularizedGMC P Xc γ r ω) -
                          (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)) +
                          ((∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
                            (∫ x, cutoffTest f (n + 1) x ∂N ω)))
                        ((∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω))
                _ ≤ _ := by
                  exact add_le_add
                    (norm_add_le
                      ((∫ x, f x ∂regularizedGMC P Xc γ r ω) -
                        (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω))
                      ((∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
                        (∫ x, cutoffTest f (n + 1) x ∂N ω)))
                    (le_refl _)
        exact (not_lt_of_ge (show ε ≤ ‖ (∫ x, f x ∂regularizedGMC P Xc γ r ω) - (∫ x, f x ∂N ω)‖ by simpa only [Set.mem_ofPred_eq] using hω)) (lt_of_le_of_lt htriangle (by linarith only [(lt_of_not_ge (by simpa [E₁] using (fun h => hnot (Or.inl h))) : ‖ (∫ x, f x ∂regularizedGMC P Xc γ r ω) - (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)‖ < ε / 3), (show ‖ (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) - (∫ x, cutoffTest f (n + 1) x ∂N ω)‖ < ε / 3 by exact lt_of_not_ge (by simpa [E₂] using (fun h => hnot (Or.inr (Or.inl h))))), (lt_of_not_ge (by simpa [E₃] using (fun h => hnot (Or.inr (Or.inr h)))) : ‖ (∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖ < ε / 3)]))
      have hmeasE s t : P (s ∪ t) ≤ P s + P t := measure_union_le _ _
      calc
        P {ω | ε ≤ ‖
            (∫ x, f x ∂regularizedGMC P Xc γ r ω) - (∫ x, f x ∂N ω)‖} ≤
            P (E₁ ∪ (E₂ ∪ E₃)) := measure_mono hsubset
        _ ≤ P E₁ + P (E₂ ∪ E₃) := hmeasE _ _
        _ ≤ P E₁ + P E₂ + P E₃ := by
          calc
            _ ≤ P E₁ + (P E₂ + P E₃) :=
              add_le_add (le_refl _) (hmeasE E₂ E₃)
            _ = P E₁ + P E₂ + P E₃ := by rw [add_assoc]
        _ ≤ gmcReferenceMeasure (referenceTail n) / q + P E₂ +
            gmcReferenceMeasure (referenceTail n) / q := by
          grw [hboundError n r, hboundLimitError n]
    have hTailDiv : Tendsto (fun n => gmcReferenceMeasure (referenceTail n) / q)
        atTop (𝓝 0) := by
      have ht := ENNReal.Tendsto.div_const (b := q) (by simpa [referenceTail] using gmcReferenceMeasure_compl_closedBall_tendsto_zero) (Or.inr hq0)
      simpa using ht
    have hSum n :
        Tendsto (fun r : ℝ => gmcReferenceMeasure (referenceTail n) / q +
          P {ω | ε / 3 ≤ ‖
            (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
            (∫ x, cutoffTest f (n + 1) x ∂N ω)‖} +
          gmcReferenceMeasure (referenceTail n) / q) atTop
          (𝓝 (gmcReferenceMeasure (referenceTail n) / q + 0 +
            gmcReferenceMeasure (referenceTail n) / q)) := by
      exact (tendsto_const_nhds.add ((fun n => hprobCore n) n)).add tendsto_const_nhds
    refine ENNReal.tendsto_nhds_zero.2 fun δ hδ => ?_
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 ((show Tendsto (fun n => gmcReferenceMeasure (referenceTail n) / q + 0 + gmcReferenceMeasure (referenceTail n) / q) atTop (𝓝 0) by simpa using ((hTailDiv.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))).add hTailDiv)).eventually (ENNReal.nhds_zero_basis.mem_iff.mpr ⟨δ, hδ, Set.Subset.rfl⟩))
    filter_upwards [((hSum n).eventually (Iio_mem_nhds (hn n (Nat.le_refl n))))] with r hr
    exact le_of_lt (lt_of_le_of_lt (hEventBound n r) hr)
  refine ⟨N, hNfinite, ⟨hNfinite, ⟨Xc, hXc, hGlobal⟩⟩, hNM⟩

end DOZZ.Proofs
