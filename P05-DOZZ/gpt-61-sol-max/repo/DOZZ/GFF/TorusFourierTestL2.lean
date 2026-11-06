/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusFourierTestPullback
public import DOZZ.GFF.LocalEnergyBound
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# DOZZ.GFF.TorusFourierTestL2

The cutoff Fourier tests converge in the local `L²` topology. The comparison uses the concrete
unit-torus Fourier partial sums and the square-integrable covariance kernel bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped BoundedContinuousFunction ENNReal InnerProductSpace Topology lp

namespace DOZZ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure GFFUnitTorus2) := by
  infer_instance

/-- A real Fourier term is represented by the real part of its coefficient times its character. -/
theorem ae_torusRealFourierTerm_apply (L : ℝ) (f : TestFn) (k : Fin 2 → ℤ) :
    (fun t : GFFUnitTorus2 => torusRealFourierTerm L f k t) =ᵐ[
      (volume : Measure GFFUnitTorus2)]
      (fun t =>
        (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).re *
            (UnitAddTorus.mFourier k t).re -
          (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).im *
            (UnitAddTorus.mFourier k t).im) := by
  let c := UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k
  filter_upwards [Complex.reCLM.coeFn_compLpL
      (c • UnitAddTorus.mFourierLp 2 k),
    Lp.coeFn_smul c (UnitAddTorus.mFourierLp 2 k),
    UnitAddTorus.coeFn_mFourierLp 2 k] with t hreal hsmul hchar
  change torusFourierRealPartCLM
      (c • UnitAddTorus.mFourierLp 2 k) t = _
  calc
    torusFourierRealPartCLM (c • UnitAddTorus.mFourierLp 2 k) t =
        Complex.reCLM ((c • UnitAddTorus.mFourierLp 2 k) t) := hreal
    _ = c.re * (UnitAddTorus.mFourier k t).re -
        c.im * (UnitAddTorus.mFourier k t).im := by
      simp_all

/-- The finite real Fourier sum is represented by the corresponding finite sum of real characters. -/
theorem ae_torusRealFourierPartialSum_apply (L : ℝ) (f : TestFn)
    (s : Finset (Fin 2 → ℤ)) :
    (fun t : GFFUnitTorus2 => torusRealFourierPartialSum L f s t) =ᵐ[
      (volume : Measure GFFUnitTorus2)]
      (fun t => s.sum fun k =>
        (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).re *
            (UnitAddTorus.mFourier k t).re -
          (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).im *
            (UnitAddTorus.mFourier k t).im) := by
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun k => torusRealFourierTerm L f k),
    ae_all_iff.mpr (fun k => ae_torusRealFourierTerm_apply L f k)] with t hsum hterm
  have hterms : s.sum (fun k => torusRealFourierTerm L f k t) =
      s.sum (fun k =>
        (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).re *
            (UnitAddTorus.mFourier k t).re -
          (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).im *
            (UnitAddTorus.mFourier k t).im) := by
    simp_all
  exact hsum.trans hterms

/-- The real part of the periodized test agrees with the original test on the representative
physical box. -/
theorem ae_torusFourierRealPart_periodization (L : ℝ) (f : TestFn) :
    (fun t : GFFUnitTorus2 =>
      torusFourierRealPartCLM (torusPeriodizationLp L f) t) =ᵐ[
        (volume : Measure GFFUnitTorus2)]
      (fun t => f (torusBoxPoint L t)) := by
  filter_upwards [Complex.reCLM.coeFn_compLpL (torusPeriodizationLp L f),
    (memLp_torusPeriodizationFunction L f).coeFn_toLp] with t hreal hperiod
  change torusFourierRealPartCLM (torusPeriodizationLp L f) t = _ at hreal
  change torusPeriodizationLp L f t = torusPeriodizationFunction L f t at hperiod
  continuity

variable (R L : ℝ) (hR : 0 < R) (hL : 0 < L)

include R L hR hL in
/-- The local cutoff Fourier test pulls back to the cutoff times the real Fourier partial sum. -/
theorem equatorLocalFourierPartialTest_torusBoxPoint  (f : TestFn) (s : Finset (Fin 2 → ℤ)) (t : GFFUnitTorus2) :
    equatorLocalFourierPartialTest R L hR f s (torusBoxPoint L t) =
      localTorusCutoff R hR (torusBoxPoint L t) *
        s.sum fun k =>
          (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).re *
              (UnitAddTorus.mFourier k t).re -
            (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).im *
              (UnitAddTorus.mFourier k t).im := by
  rw [equatorLocalFourierPartialTest_apply]
  simp_rw [localTorusCosTest_torusBoxPoint R L hR hL,
    localTorusSinTest_torusBoxPoint R L hR hL]
  rw [Finset.mul_sum]
  field_simp

/-- The local cutoff acts as the identity on a test supported in its inner ball. -/
theorem localTorusCutoff_mul_eq_of_support (R : ℝ) (hR : 0 < R) (f : TestFn)
    (hsupp : Function.support f ⊆ ball (0 : ℂ) (R - 1)) (z : ℂ) :
    localTorusCutoff R hR z * f z = f z := by
  by_cases hz : f z = 0
  · simp [hz]
  · have hzball := hsupp (Function.mem_support.mpr hz)
    have hnorm : ‖z‖ < R - 1 := by
      simpa [mem_ball, dist_eq_norm] using hzball
    have hzclosed : z ∈ closedBall 0 (R + 1) := by
      simpa [mem_closedBall, dist_eq_norm] using
        (le_of_lt (show ‖z‖ < R + 1 by linarith))
    rw [localTorusCutoff_eq_one R hR hzclosed]
    ring

/-- In `L²`, the squared norm is the integral of the square of the real representative. -/
theorem integral_sq_eq_Lp_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : Lp ℝ 2 μ) :
    (∫ x, u x ^ 2 ∂μ) = ‖u‖ ^ 2 := by
  calc
    (∫ x, u x ^ 2 ∂μ) = ∫ x, ⟪u x, u x⟫_ℝ ∂μ := by
      simp_all
    _ = ⟪u, u⟫_ℝ := (MeasureTheory.L2.inner_def u u).symm
    _ = ‖u‖ ^ 2 := by simp [inner_self_eq_norm_sq_to_K]

/-- The difference between a cutoff Fourier test and its target has the support of the cutoff. -/
theorem equatorLocalFourierPartialTest_sub_support_subset (R L : ℝ)
    (hR : 0 < R) (f : TestFn) (s : Finset (Fin 2 → ℤ))
    (hsupp : Function.support f ⊆ ball (0 : ℂ) (R - 1)) :
    Function.support (equatorLocalFourierPartialTest R L hR f s - f) ⊆
      ball (0 : ℂ) (R + 2) := by
  apply Function.support_subset_iff'.2
  intro z hz
  have hdist : R + 2 ≤ dist z 0 := by
    simpa [mem_ball] using hz
  have hcut : localTorusCutoff R hR z = 0 := by
    apply (localTorusCutoff R hR).zero_of_le_dist
    exact hdist
  have hpartial : equatorLocalFourierPartialTest R L hR f s z = 0 := by
    rw [equatorLocalFourierPartialTest_apply]
    simp_all
  have hinner : z ∉ ball (0 : ℂ) (R - 1) := by
    intro hin
    exact hz (ball_subset_ball (by linarith) hin)
  have hfz : f z = 0 := by
    by_contra hne
    simp_all
  simp_all

include R L hR hL in
/-- The `L²` error of the cutoff Fourier test is bounded by the torus Fourier error. -/
theorem integral_sq_equatorLocalFourierPartialTest_sub_le  (hbox : L / 2 = R + 2)
    (f : TestFn) (s : Finset (Fin 2 → ℤ))
    (hsupp : Function.support f ⊆ ball (0 : ℂ) (R - 1)) :
    (∫ z : ℂ,
      (equatorLocalFourierPartialTest R L hR f s z - f z) ^ 2) ≤
      L ^ 2 *
        ‖torusRealFourierPartialSum L f s -
          torusFourierRealPartCLM (torusPeriodizationLp L f)‖ ^ 2 := by
  let g  := equatorLocalFourierPartialTest R L hR f s - f
  have hgsupp : Function.support g ⊆ ball (0 : ℂ) (R + 2) := equatorLocalFourierPartialTest_sub_support_subset R L hR f s hsupp
  have hgsuppBox : Function.support g ⊆ ball (0 : ℂ) (L / 2) := by
    simpa [hbox] using hgsupp
  have hplane := integral_sq_eq_torusBox L hL g hgsuppBox
  let u : Lp ℝ 2 (volume : Measure GFFUnitTorus2) :=
    torusRealFourierPartialSum L f s -
      torusFourierRealPartCLM (torusPeriodizationLp L f)
  have hpull : (fun t : GFFUnitTorus2 => g (torusBoxPoint L t)) =ᵐ[
      (volume : Measure GFFUnitTorus2)]
      (fun t => localTorusCutoff R hR (torusBoxPoint L t) * u t) := by
    filter_upwards [ae_torusRealFourierPartialSum_apply L f s,
      ae_torusFourierRealPart_periodization L f,
      Lp.coeFn_sub (torusRealFourierPartialSum L f s)
        (torusFourierRealPartCLM (torusPeriodizationLp L f))] with
      t hsum htarget hsub
    change equatorLocalFourierPartialTest R L hR f s (torusBoxPoint L t) -
      f (torusBoxPoint L t) = _
    rw [equatorLocalFourierPartialTest_torusBoxPoint R L hR hL f s t,
      ← hsum]
    rw [← localTorusCutoff_mul_eq_of_support R hR f hsupp (torusBoxPoint L t)]
    rw [← htarget]
    rw [hsub]
    simp only [Pi.sub_apply]
    ring_nf
  have hleftMeas  :=
    g.continuous.measurable.comp (measurable_torusBoxPoint L)
  have hleftBound : ∀ t : GFFUnitTorus2,
      ‖g (torusBoxPoint L t)‖ ≤ ‖(g : ℂ →ᵇ ℝ)‖ := by
    intro t
    exact (g : ℂ →ᵇ ℝ).norm_coe_le_norm (torusBoxPoint L t)
  have hleftMem : MemLp (fun t : GFFUnitTorus2 => g (torusBoxPoint L t)) 2
      (volume : Measure GFFUnitTorus2) :=
    MemLp.of_bound hleftMeas.aestronglyMeasurable ‖(g : ℂ →ᵇ ℝ)‖
      (ae_of_all _ hleftBound)
  have hleftInt : Integrable (fun t : GFFUnitTorus2 =>
      g (torusBoxPoint L t) ^ 2) (volume : Measure GFFUnitTorus2) := hleftMem.integrable_sq
  have herrMem  := Lp.memLp u
  have herrInt : Integrable (fun t : GFFUnitTorus2 => u t ^ 2)
      (volume : Measure GFFUnitTorus2) := herrMem.integrable_sq
  have hpoint : ∀ᵐ t ∂(volume : Measure GFFUnitTorus2),
      g (torusBoxPoint L t) ^ 2 ≤ u t ^ 2 := by
    filter_upwards [hpull] with t ht
    have hχ0 : 0 ≤ localTorusCutoff R hR (torusBoxPoint L t) :=
      (localTorusCutoff R hR).nonneg
    have hχ1 : localTorusCutoff R hR (torusBoxPoint L t) ≤ 1 :=
      (localTorusCutoff R hR).le_one
    have hχsq : localTorusCutoff R hR (torusBoxPoint L t) ^ 2 ≤ 1 := by
      nlinarith
    calc
      g (torusBoxPoint L t) ^ 2 =
          localTorusCutoff R hR (torusBoxPoint L t) ^ 2 * u t ^ 2 := by
        rw [ht]
        ring
      _ ≤ u t ^ 2 := by
        nlinarith
  have htorus : (∫ t : GFFUnitTorus2,
      g (torusBoxPoint L t) ^ 2) ≤ ‖u‖ ^ 2 := by
    calc
      (∫ t : GFFUnitTorus2, g (torusBoxPoint L t) ^ 2) ≤
          ∫ t : GFFUnitTorus2, u t ^ 2 := integral_mono_ae hleftInt herrInt hpoint
      _ = ‖u‖ ^ 2 := integral_sq_eq_Lp_norm_sq u
  calc
    (∫ z : ℂ, (equatorLocalFourierPartialTest R L hR f s z - f z) ^ 2) =
        ∫ z : ℂ, g z ^ 2 := rfl
    _ = L ^ 2 * ∫ t : GFFUnitTorus2, g (torusBoxPoint L t) ^ 2 := hplane
    _ ≤ L ^ 2 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_left htorus (sq_nonneg L)
    _ = L ^ 2 * ‖torusRealFourierPartialSum L f s -
        torusFourierRealPartCLM (torusPeriodizationLp L f)‖ ^ 2 := rfl

include R L hR hL in
/-- Applying the G4 field to the cutoff Fourier tests converges in `L²` to its value on the
original supported test. -/
theorem tendsto_equatorFieldL2_localFourierPartialTest  (hbox : L / 2 = R + 2)
    (f : TestFn) (hsupp : Function.support f ⊆ ball (0 : ℂ) (R - 1)) :
    Tendsto
      (fun s : Finset (Fin 2 → ℤ) =>
        equatorFieldL2 (equatorLocalFourierPartialTest R L hR f s))
      atTop (𝓝 (equatorFieldL2 f)) := by
  let target := torusFourierRealPartCLM (torusPeriodizationLp L f)
  let err : Finset (Fin 2 → ℤ) → Lp ℝ 2 (volume : Measure GFFUnitTorus2) :=
    fun s => torusRealFourierPartialSum L f s - target
  let F  :=
    fun s => equatorFieldL2 (equatorLocalFourierPartialTest R L hR f s) -
      equatorFieldL2 f
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa [err, target] using
      (torusRealFourierPartialSum_tendsto L f).sub_const target
  have herrNorm : Tendsto (fun s => ‖err s‖) atTop (𝓝 0) := by
    convert (continuous_norm.tendsto (0 : Lp ℝ 2
      (volume : Measure GFFUnitTorus2))).comp herr using 1
    · rfl
    · simp
  let Q  :=
    (∫ p : ℂ × ℂ in ball (0 : ℂ) (R + 2) ×ˢ ball (0 : ℂ) (R + 2),
      ‖gffKernel p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ)
  have hQ : 0 ≤ Q := by positivity
  let K  := Q * L ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hnormWhite (g : TestFn) :
      ‖equatorFieldL2 g‖ = ‖equatorKernelLimitMap g‖ := (GaussianFields.scaleSpaceWhiteNoiseL2 2).norm_map _
  have hbound : ∀ s : Finset (Fin 2 → ℤ),
      ‖F s‖ ≤ Real.sqrt K * ‖err s‖ := by
    intro s
    let g  := equatorLocalFourierPartialTest R L hR f s - f
    have hgsupp : Function.support g ⊆ ball (0 : ℂ) (R + 2) := equatorLocalFourierPartialTest_sub_support_subset R L hR f s hsupp
    have hfull : (∫ z : ℂ, g z ^ 2) = ∫ z in ball (0 : ℂ) (R + 2), g z ^ 2 := by
      calc
        (∫ z : ℂ, g z ^ 2) =
            ∫ z : ℂ, (ball (0 : ℂ) (R + 2)).indicator (fun z => g z ^ 2) z := by
          apply integral_congr_ae
          filter_upwards [] with z
          by_cases hz : z ∈ ball (0 : ℂ) (R + 2)
          · simp [hz]
          · have hzero : g z = 0 := by
              by_contra hne
              bound
            simp [hz, hzero]
        _ = ∫ z in ball (0 : ℂ) (R + 2), g z ^ 2 :=
          integral_indicator measurableSet_ball
    have hboxSupp : Function.support g ⊆ ball (0 : ℂ) (L / 2) := by
      simpa [hbox] using hgsupp
    have hplane := integral_sq_eq_torusBox L hL g hboxSupp
    have hlocalEnergy := norm_sq_equatorKernelLimitMap_le_localL2
      (R + 2) g hgsupp
    have htestL2 := integral_sq_equatorLocalFourierPartialTest_sub_le
      R L hR hL hbox f s hsupp
    have hkernelSq : ‖equatorKernelLimitMap g‖ ^ 2 ≤
        K * ‖err s‖ ^ 2 := by
      calc
        ‖equatorKernelLimitMap g‖ ^ 2 ≤ Q *
            (∫ z in ball (0 : ℂ) (R + 2), g z ^ 2) := by
          simpa [Q, Real.norm_eq_abs, sq_abs] using hlocalEnergy
        _ = Q * (∫ z : ℂ, g z ^ 2) := by rw [← hfull]
        _ = Q * (L ^ 2 * ∫ t : GFFUnitTorus2, g (torusBoxPoint L t) ^ 2) := by
          rw [hplane]
        _ ≤ Q * (L ^ 2 * ‖err s‖ ^ 2) := by
          have htestL2' : L ^ 2 * ∫ t : GFFUnitTorus2,
              g (torusBoxPoint L t) ^ 2 ≤ L ^ 2 * ‖err s‖ ^ 2 := by
            rw [← hplane]
            exact htestL2
          exact mul_le_mul_of_nonneg_left htestL2' hQ
        _ = K * ‖err s‖ ^ 2 := by
          dsimp [K]
          ring
    have hfield_eq : ‖F s‖ = ‖equatorKernelLimitMap g‖ := by
      change ‖equatorFieldL2 (equatorLocalFourierPartialTest R L hR f s) -
        equatorFieldL2 f‖ = _
      rw [← equatorFieldL2.map_sub]
      exact hnormWhite g
    have htargetSq : ‖F s‖ ^ 2 ≤ (Real.sqrt K * ‖err s‖) ^ 2 := by
      rw [hfield_eq]
      calc
        ‖equatorKernelLimitMap g‖ ^ 2 ≤ K * ‖err s‖ ^ 2 := hkernelSq
        _ = (Real.sqrt K * ‖err s‖) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hK]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg K) (norm_nonneg _))).1
      htargetSq
  have hupper : Tendsto (fun s => Real.sqrt K * ‖err s‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : Finset (Fin 2 → ℤ) => Real.sqrt K)
      atTop (𝓝 (Real.sqrt K))).mul herrNorm
  have hFNorm  :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun s => norm_nonneg (F s)) hbound
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hFNorm

end DOZZ

end
