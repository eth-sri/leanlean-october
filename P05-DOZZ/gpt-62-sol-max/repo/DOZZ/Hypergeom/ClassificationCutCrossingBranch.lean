/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationCutLog
public import DOZZ.Hypergeom.BasisRegularity
public import DOZZ.Hypergeom.BasisSpanning
public import DOZZ.Hypergeom.ClassificationHermitianCoefficients
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! A holomorphic second zero-basis solution across a disk centered on the negative cut. -/

@[expose] public section

open scoped ComplexConjugate
open Filter
open scoped Topology

namespace DOZZ.Proofs

/-- A fixed disk crossing the negative real cut but staying inside the unit disk. -/
def gaussNegativeCrossingDisk : Set ℂ := Metric.ball (-1 / 2 : ℂ) (1 / 4 : ℝ)

theorem gaussNegativeCrossingDisk_isOpen : IsOpen gaussNegativeCrossingDisk := Metric.isOpen_ball

theorem gaussNegativeCrossingDisk_real_bounds {z : ℂ}
    (hz : z ∈ gaussNegativeCrossingDisk) :
    -(3 / 4 : ℝ) < z.re ∧ z.re < -(1 / 4 : ℝ) := by
  have h := (Complex.abs_re_le_norm (z - (-1 / 2 : ℂ))).trans_lt
    (by simpa [gaussNegativeCrossingDisk, Metric.mem_ball, dist_eq_norm] using hz)
  norm_num [Complex.sub_re] at h
  have := abs_lt.mp h
  constructor <;> linarith

theorem gaussNegativeCrossingDisk_subset_gaussSlitPlane :
    gaussNegativeCrossingDisk ⊆ gaussSlitPlane := by
  intro z hz
  change z.im ≠ 0 ∨ z.re < 1
  exact Or.inr ((gaussNegativeCrossingDisk_real_bounds hz).2.trans (by norm_num))

theorem neg_gaussNegativeCrossingDisk_subset_slitPlane :
    ∀ z ∈ gaussNegativeCrossingDisk, -z ∈ Complex.slitPlane := by
  intro z hz
  rw [Complex.mem_slitPlane_iff]
  left
  have h := (gaussNegativeCrossingDisk_real_bounds hz).2
  simp only [Complex.neg_re]
  linarith

/-- The local logarithm branch used to cross the negative axis, with argument in `(0,2π)`.
It is holomorphic on the whole crossing disk because `-z` stays in the right half-plane. -/
noncomputable def gaussNegativeCrossingSecond
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.log (-z) * (1 - c)) *
    Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - c)) *
      H (a - c + 1) (b - c + 1) (2 - c) z

/-- The local continuation of the zero-basis Wronskian formula across the negative cut. -/
noncomputable def gaussNegativeCrossingWronskianModel
    (a b c : ℂ) (z : ℂ) : ℂ :=
  (1 - c) * (Complex.exp (Complex.log (-z) * (-c)) *
    Complex.exp ((Real.pi : ℂ) * Complex.I * (-c))) *
      Complex.exp (Complex.log (1 - z) * (c - a - b - 1))

theorem gaussFMinus_analyticOnNhd_crossingDisk
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    AnalyticOnNhd ℂ (gaussFMinus H a b c) gaussNegativeCrossingDisk :=
  ((hH a b c hc).1.analyticOnNhd gaussSlitPlane_isOpen).mono
    gaussNegativeCrossingDisk_subset_gaussSlitPlane

private theorem analyticOnNhd_negativeBranchPower (c : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (Complex.log (-z) * c) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * c)) gaussNegativeCrossingDisk := by
  have hn : AnalyticOnNhd ℂ (fun z : ℂ => -z) gaussNegativeCrossingDisk := by fun_prop
  exact (((hn.clog neg_gaussNegativeCrossingDisk_subset_slitPlane).mul
    analyticOnNhd_const).cexp).mul analyticOnNhd_const

theorem gaussNegativeCrossingSecond_analyticOnNhd
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    AnalyticOnNhd ℂ (gaussNegativeCrossingSecond H a b c) gaussNegativeCrossingDisk :=
  (analyticOnNhd_negativeBranchPower (1 - c)).mul
    (gaussFMinus_analyticOnNhd_crossingDisk hH _ _ _ (two_sub_parameter_ne_nat_neg hc))

def gaussNegativeCrossingUpper : Set ℂ :=
  gaussNegativeCrossingDisk ∩ {z | 0 < z.im}

theorem gaussNegativeCrossingUpper_isOpen : IsOpen gaussNegativeCrossingUpper :=
  gaussNegativeCrossingDisk_isOpen.inter (isOpen_Ioi.preimage Complex.continuous_im)


private theorem one_sub_gaussNegativeCrossingDisk_subset_slitPlane :
    ∀ z ∈ gaussNegativeCrossingDisk, 1 - z ∈ Complex.slitPlane := by
  intro z hz
  rw [Complex.mem_slitPlane_iff]
  left
  have hzre := (gaussNegativeCrossingDisk_real_bounds hz).2
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- The local second basis agrees with the principal zero basis in the upper half of the disk. -/
theorem gaussNegativeCrossingSecond_eq_gaussFPlus_of_im_pos
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (a b c z : ℂ) (hz : 0 < z.im) :
    gaussNegativeCrossingSecond H a b c z = gaussFPlus H a b c z := by
  dsimp [gaussNegativeCrossingSecond, gaussFPlus]
  rw [← complexCpow_eq_exp_log_neg_phase_upper hz]

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
  (hc : ∀ n : ℤ, c ≠ (n : ℂ))
include hH hc

/-- The analytic continuation of the canonical zero-basis Wronskian is explicit and nowhere
zero throughout the disk crossing the negative real axis. -/
theorem gaussNegativeCrossing_wronskian_identity :
    ∀ z ∈ gaussNegativeCrossingDisk,
      gaussCramerWronskian (gaussFMinus H a b c)
        (gaussNegativeCrossingSecond H a b c) z =
          gaussNegativeCrossingWronskianModel a b c z := by
  let f := gaussFMinus H a b c
  let g := gaussNegativeCrossingSecond H a b c
  let W := gaussCramerWronskian f g
  let D := gaussNegativeCrossingDisk
  have hf : AnalyticOnNhd ℂ f D :=
    gaussFMinus_analyticOnNhd_crossingDisk hH a b c (parameter_ne_nat_neg_of_ne_int hc)
  have hg := gaussNegativeCrossingSecond_analyticOnNhd hH a b c hc
  have hW : AnalyticOnNhd ℂ W D := analyticOnNhd_wronskian hf hg
  have hsub : AnalyticOnNhd ℂ (fun z : ℂ => 1 - z) D := by fun_prop
  have hlog := hsub.clog one_sub_gaussNegativeCrossingDisk_subset_slitPlane
  have hModel : AnalyticOnNhd ℂ (gaussNegativeCrossingWronskianModel a b c) D :=
    ((analyticOnNhd_const (v := 1 - c)).mul (analyticOnNhd_negativeBranchPower (-c))).mul
      ((hlog.mul (analyticOnNhd_const (v := c - a - b - 1))).cexp)
  have hEqOn : Set.EqOn g (gaussFPlus H a b c) gaussNegativeCrossingUpper :=
    fun z hz => gaussNegativeCrossingSecond_eq_gaussFPlus_of_im_pos a b c z hz.2
  have hUpper : Set.EqOn W (gaussNegativeCrossingWronskianModel a b c) gaussNegativeCrossingUpper := by
    intro z hz
    have hcut : z ∈ gaussCutPlane := Or.inl (ne_of_gt hz.2)
    have hw0 := Complex.slitPlane_ne_zero (one_sub_gaussNegativeCrossingDisk_subset_slitPlane z hz.1)
    dsimp only [W, gaussCramerWronskian]
    rw [hEqOn hz, hEqOn.deriv gaussNegativeCrossingUpper_isOpen hz]
    dsimp only [f]
    rw [gaussFPlus_wronskian_identity hH a b c hc z hcut,
      complexCpow_eq_exp_log_neg_phase_upper hz.2, Complex.cpow_def_of_ne_zero hw0,
      gaussNegativeCrossingWronskianModel]
  have hbase : (-1 / 2 : ℂ) + (1 / 8 : ℝ) * Complex.I ∈
      gaussNegativeCrossingUpper := by
    constructor
    · norm_num [gaussNegativeCrossingDisk, Metric.mem_ball, dist_eq_norm]
    · norm_num
  have hnear : W =ᶠ[𝓝 ((-1 / 2 : ℂ) + (1 / 8 : ℝ) * Complex.I)]
      gaussNegativeCrossingWronskianModel a b c := by
    filter_upwards [gaussNegativeCrossingUpper_isOpen.mem_nhds hbase] with z hz
    exact hUpper hz
  have hpre : IsPreconnected gaussNegativeCrossingDisk :=
    (convex_ball (-1 / 2 : ℂ) (1 / 4 : ℝ)).isPreconnected
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hW hModel hpre hbase.1 hnear)

/-- Under `c ∉ ℤ`, the crossing-disk Wronskian is nowhere zero. -/
theorem gaussNegativeCrossing_wronskian_ne_zero :
    ∀ z ∈ gaussNegativeCrossingDisk,
      gaussCramerWronskian (gaussFMinus H a b c)
        (gaussNegativeCrossingSecond H a b c) z ≠ 0 := by
  intro z hz
  rw [gaussNegativeCrossing_wronskian_identity hH a b c hc z hz]
  have hc1 : (1 : ℂ) - c ≠ 0 := by
    intro h
    apply hc 1
    exact_mod_cast (sub_eq_zero.mp h).symm
  unfold gaussNegativeCrossingWronskianModel
  exact mul_ne_zero (mul_ne_zero hc1 (mul_ne_zero (Complex.exp_ne_zero _)
    (Complex.exp_ne_zero _))) (Complex.exp_ne_zero _)

end

/-- Below the cut, the local second basis differs from the principal one by the full monodromy
phase `exp(2πi(1-c))`. -/
theorem gaussNegativeCrossingSecond_eq_phase_mul_gaussFPlus_of_im_neg
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (a b c z : ℂ) (hz : z.im < 0) :
    gaussNegativeCrossingSecond H a b c z =
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - c)) *
        gaussFPlus H a b c z := by
  dsimp [gaussNegativeCrossingSecond, gaussFPlus]
  rw [complexCpow_eq_exp_log_neg_phase_lower hz]
  have hphase : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - c)) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - c)) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - c)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    Complex.exp (Complex.log (-z) * (1 - c)) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - c)) *
          H (a - c + 1) (b - c + 1) (2 - c) z =
        Complex.exp (Complex.log (-z) * (1 - c)) *
          (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - c)) *
            Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - c))) *
          H (a - c + 1) (b - c + 1) (2 - c) z := by rw [hphase]
    _ = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - c)) *
        (Complex.exp (Complex.log (-z) * (1 - c)) *
          Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - c)) *
          H (a - c + 1) (b - c + 1) (2 - c) z) := by ring
    _ = _ := rfl

end DOZZ.Proofs
