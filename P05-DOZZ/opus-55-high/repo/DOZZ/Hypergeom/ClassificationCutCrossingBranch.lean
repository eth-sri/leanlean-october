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
import DOZZ.Hypergeom.ODE.ConnectionMidpointDerivatives

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
  have hdist : ‖z + (1 / 2)‖ < (1 / 4) := by
    change dist z _ < (1 / 4) at hz
    have hnorm : ‖z - (-1 / 2)‖ < (1 / 4) := by
      simpa [dist_eq_norm] using hz
    grind
  have habs' := (Complex.abs_re_le_norm _).trans_lt hdist
  have habs : |z.re + 1 / 2| < (1 / 4) := by
    simp_all
  grind

theorem gaussNegativeCrossingDisk_subset_gaussSlitPlane :
    gaussNegativeCrossingDisk ⊆ gaussSlitPlane := by
  intro z hz
  change z.im ≠ 0 ∨ z.re < 1
  exact Or.inr ((gaussNegativeCrossingDisk_real_bounds hz).2.trans (by norm_num))

theorem neg_gaussNegativeCrossingDisk_subset_slitPlane :
    ∀ z ∈ gaussNegativeCrossingDisk, -z ∈ Complex.slitPlane := by
  intro z hz
  left
  have h := (gaussNegativeCrossingDisk_real_bounds hz).2
  simp
  linarith

noncomputable def gaussNegativeCrossingSecond
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c z : ℂ) : ℂ :=
  Complex.exp (Complex.log (-z) * (1 - c)) *
    Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - c)) *
      H (a - c + 1) (b - c + 1) (2 - c) z

/-- The local continuation of the zero-basis Wronskian formula across the negative cut. -/
noncomputable def gaussNegativeCrossingWronskianModel
    (a b c z : ℂ) : ℂ :=
  (1 - c) * Complex.exp (Complex.log (-z) * (-c)) *
    Complex.exp ((Real.pi : ℂ) * Complex.I * (-c)) *
      Complex.exp (Complex.log (1 - z) * (c - a - b - 1))

theorem gaussNegativeCrossingSecond_analyticOnNhd
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    AnalyticOnNhd ℂ (gaussNegativeCrossingSecond H a b c)
      gaussNegativeCrossingDisk := by
  have hcNat : ∀ n : ℕ, c ≠ -n := by
    intro n heq
    apply hc (-n)
    simp_all
  have hCNat :=
    two_sub_parameter_ne_nat_neg hc
  have hq :=
    (hH (a - c + 1) (b - c + 1) _ hCNat).1.analyticOnNhd DOZZ.Proofs.gaussSlitPlane_isOpen_for_connection
  have hqD := hq.mono gaussNegativeCrossingDisk_subset_gaussSlitPlane
  have hNeg : AnalyticOnNhd ℂ (fun z => -z) gaussNegativeCrossingDisk := by
    fun_prop
  have hlog : AnalyticOnNhd ℂ (fun z => Complex.log (-z))
      gaussNegativeCrossingDisk :=
    hNeg.clog (neg_gaussNegativeCrossingDisk_subset_slitPlane)
  have hexponent : AnalyticOnNhd ℂ
      (fun z => Complex.log (-z) * (1 - c)) gaussNegativeCrossingDisk :=
    hlog.mul analyticOnNhd_const
  have hphase : AnalyticOnNhd ℂ
      (fun _ => Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - c)))
      gaussNegativeCrossingDisk := analyticOnNhd_const
  have hfactor := hexponent.cexp.mul hphase
  change AnalyticOnNhd ℂ
    (fun z => Complex.exp _ *
      Complex.exp _ *
        H _ _ _ z) gaussNegativeCrossingDisk
  fun_prop

private def gaussNegativeCrossingUpper : Set ℂ :=
  gaussNegativeCrossingDisk ∩ {z | 0 < z.im}

private theorem gaussNegativeCrossingUpper_isOpen : IsOpen gaussNegativeCrossingUpper := by
  apply gaussNegativeCrossingDisk_isOpen.inter
  exact isOpen_Ioi.preimage Complex.continuous_im


private theorem one_sub_gaussNegativeCrossingDisk_subset_slitPlane :
    ∀ z ∈ gaussNegativeCrossingDisk, 1 - z ∈ Complex.slitPlane := by
  intro z hz
  left
  have hzre := (gaussNegativeCrossingDisk_real_bounds hz).2
  simp
  linarith
section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ}
section
variable (hH : IsGaussHypergeometricFamily H) (a b c : ℂ) (hc : ∀ n : ℤ, c ≠ (n : ℂ))
include hH hc

/-- The analytic continuation of the canonical zero-basis Wronskian is explicit and nowhere
zero throughout the disk crossing the negative real axis. -/
theorem gaussNegativeCrossing_wronskian_identity
    :
    ∀ z ∈ gaussNegativeCrossingDisk,
      gaussCramerWronskian (gaussFMinus H a b c)
        (gaussNegativeCrossingSecond H a b c) z =
          gaussNegativeCrossingWronskianModel a b c z := by
  let W : ℂ → ℂ := fun z =>
    gaussCramerWronskian (gaussFMinus H a b c)
      (gaussNegativeCrossingSecond H a b c) z
  have hF : AnalyticOnNhd ℂ (gaussFMinus H a b c) gaussNegativeCrossingDisk := by
    have hcNat : ∀ n : ℕ, c ≠ -n := by
      intro n heq
      apply hc (-n)
      simp_all
    have hslitOpen : IsOpen gaussSlitPlane := by
      change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | z.re < 1})
      exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
        (isOpen_Iio.preimage Complex.continuous_re)
    have hAnalytic := (hH a b c hcNat).1.analyticOnNhd hslitOpen
    exact hAnalytic.mono gaussNegativeCrossingDisk_subset_gaussSlitPlane
  have hG :=
    gaussNegativeCrossingSecond_analyticOnNhd hH a b c hc
  have hG₁ := hG.deriv
  have hW : AnalyticOnNhd ℂ W gaussNegativeCrossingDisk := by
    dsimp [W, gaussCramerWronskian]
    exact (hF.mul hG₁).sub (hF.deriv.mul hG)
  have hNeg : AnalyticOnNhd ℂ (fun z : ℂ => -z) gaussNegativeCrossingDisk := by
    fun_prop
  have hlogNeg :=
    hNeg.clog neg_gaussNegativeCrossingDisk_subset_slitPlane
  have hOneSub : AnalyticOnNhd ℂ (fun z : ℂ => 1 - z) gaussNegativeCrossingDisk := by
    fun_prop
  have hlogOneSub : AnalyticOnNhd ℂ (fun z : ℂ => Complex.log (1 - z))
      gaussNegativeCrossingDisk :=
    hOneSub.clog one_sub_gaussNegativeCrossingDisk_subset_slitPlane
  have hModel : AnalyticOnNhd ℂ (gaussNegativeCrossingWronskianModel a b c)
      gaussNegativeCrossingDisk := by
    change AnalyticOnNhd ℂ
      (fun z => (1 - c) * Complex.exp _ *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (-c)) *
          Complex.exp _)
      gaussNegativeCrossingDisk
    have h₁ : AnalyticOnNhd ℂ
        (fun z => Complex.exp (Complex.log (-z) * (-c))) gaussNegativeCrossingDisk :=
      (hlogNeg.mul analyticOnNhd_const).cexp
    have h₂ : AnalyticOnNhd ℂ
        (fun _ : ℂ => Complex.exp ((Real.pi : ℂ) * Complex.I * (-c)))
        gaussNegativeCrossingDisk := analyticOnNhd_const
    have h₃ : AnalyticOnNhd ℂ
        (fun z => Complex.exp (Complex.log (1 - z) * (c - a - b - 1)))
        gaussNegativeCrossingDisk := (hlogOneSub.mul analyticOnNhd_const).cexp
    exact (((analyticOnNhd_const.mul h₁).mul h₂).mul h₃)
  have hUpper : ∀ z ∈ gaussNegativeCrossingUpper, W z =
      gaussNegativeCrossingWronskianModel a b c z := by
    intro z hz
    have hEqOn : Set.EqOn (gaussNegativeCrossingSecond H a b c)
        (gaussFPlus H a b c) gaussNegativeCrossingUpper := by
      intro w hw
      dsimp [gaussNegativeCrossingSecond, gaussFPlus]
      rw [← complexCpow_eq_exp_log_neg_phase_upper hw.2]
    change gaussFMinus H a b c z *
        deriv _ z -
      deriv _ z * gaussNegativeCrossingSecond H a b c z =
      gaussNegativeCrossingWronskianModel a b c z
    rw [hEqOn hz, (hEqOn.deriv gaussNegativeCrossingUpper_isOpen hz)]
    have hz0 : z ≠ 0 := by
      intro h
      have him := hz.2
      rw [h] at him
      norm_num at him
    have hw0 : 1 - z ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      have hre' : 1 - z.re = 0 := by assumption
      have hzre := (gaussNegativeCrossingDisk_real_bounds hz.1).2
      linarith
    rw [(((gauss_local_basis_zero hH a b c hc).2.2.1 z (Or.inl (ne_of_gt hz.2))).2.2), complexCpow_eq_exp_log_neg_phase_upper hz.2, Complex.cpow_def_of_ne_zero hw0 _, gaussNegativeCrossingWronskianModel]
    ring
  have hbase : (-1 / 2) + (1 / 8) * Complex.I ∈
      gaussNegativeCrossingUpper := by
    constructor
    · norm_num [gaussNegativeCrossingDisk, Metric.mem_ball, dist_eq_norm]
    · norm_num
  have hnear : W =ᶠ[𝓝 ((-1 / 2) + (1 / 8) * Complex.I)]
      gaussNegativeCrossingWronskianModel a b c := by
    filter_upwards [gaussNegativeCrossingUpper_isOpen.mem_nhds hbase] with z hz
    exact hUpper z hz
  have hpre : IsPreconnected gaussNegativeCrossingDisk :=
    (convex_ball _ (1 / 4 : ℝ)).isPreconnected
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hW hModel hpre hbase.1 hnear)

/-- Under `c ∉ ℤ`, the crossing-disk Wronskian is nowhere zero. -/
theorem gaussNegativeCrossing_wronskian_ne_zero
    :
    ∀ z ∈ gaussNegativeCrossingDisk,
      gaussCramerWronskian (gaussFMinus H a b c)
        (gaussNegativeCrossingSecond H a b c) z ≠ 0 := by
  intro z hz
  rw [gaussNegativeCrossing_wronskian_identity hH a b c hc z hz]
  have hc1 : 1 - c ≠ 0 := by
    intro h
    apply hc 1
    grind
  unfold gaussNegativeCrossingWronskianModel
  simp_all

end
section
variable (a b c z : ℂ)

/-- The local second basis agrees with the principal zero basis in the upper half of the disk. -/
theorem gaussNegativeCrossingSecond_eq_gaussFPlus_of_im_pos
    (hz : 0 < z.im) :
    gaussNegativeCrossingSecond H a b c z = gaussFPlus H a b c z := by
  dsimp [gaussNegativeCrossingSecond, gaussFPlus]
  rw [← complexCpow_eq_exp_log_neg_phase_upper hz]

/-- Below the cut, the local second basis differs from the principal one by the full monodromy
phase `exp(2πi(1-c))`. -/
theorem gaussNegativeCrossingSecond_eq_phase_mul_gaussFPlus_of_im_neg
    (hz : z.im < 0) :
    gaussNegativeCrossingSecond H a b c z =
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - c)) *
        gaussFPlus H a b c z := by
  dsimp [gaussNegativeCrossingSecond, gaussFPlus]
  rw [complexCpow_eq_exp_log_neg_phase_lower hz]
  have hphase : Complex.exp ((2 * Real.pi * Complex.I) * (1 - c)) *
      Complex.exp (-Real.pi * Complex.I * (1 - c)) =
      Complex.exp (Real.pi * Complex.I * (1 - c)) := by
    rw [← Complex.exp_add]
    ring
  grind

end

end

end DOZZ.Proofs
