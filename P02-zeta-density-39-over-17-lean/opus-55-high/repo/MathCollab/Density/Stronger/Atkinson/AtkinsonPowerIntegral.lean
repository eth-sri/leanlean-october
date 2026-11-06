module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerAmplitude
public import MathCollab.Density.Stronger.Atkinson.AtkinsonAmplitudeIntegral
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorSupport
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform cancellation for the actual power-weighted divisor source

The positive-support restriction and square change of variables are
proved for the actual phase-adjusted test. The final bound is uniform
in every real carrier parameter, including both Bessel signs.
-/

noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonPowerIntegrand (T G L α b x : ℝ) : ℂ :=
  zetaAtkinsonDivisorTest T G L x * ((x ^ (-α) : ℝ) : ℂ) *
    Complex.exp ((4 * Real.pi * b * Real.sqrt x : ℝ) * I)

def atkinsonPowerIntegral (T G L α b : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0, atkinsonPowerIntegrand T G L α b x

theorem atkinsonPowerIntegrand_sq {T y : ℝ} (hT : 0 < T) (hy : 0 < y)
    (G L α b : ℝ) :
    (2 * y : ℝ) • atkinsonPowerIntegrand T G L α b (y ^ 2) =
      2 * (atkinsonPowerWeight T G L α (y ^ 2) * atkinsonRootKernel T b y) := by
  rw [atkinsonPowerWeight_eq_amplitude hT (sq_pos_of_pos hy) G L α, Real.sqrt_sq hy.le]
  have hc := zetaAtkinsonDivisorTest_mul_carrier T G L b (sq_pos_of_pos hy)
  rw [zetaAtkinsonPhase_sq T b hy] at hc
  have hp : Complex.exp (((2 * Real.pi * atkinsonRootPhase T b y : ℝ) : ℂ) * I) =
      atkinsonRootKernel T b y := by
    unfold atkinsonRootKernel
    congr 1
    push_cast
    ring
  rw [hp] at hc
  push_cast at hc
  unfold atkinsonPowerIntegrand
  simp only [real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  grind

theorem atkinsonPowerIntegral_eq_root {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (α b : ℝ) :
    atkinsonPowerIntegral T G L α b =
      2 * ∫ y in Real.sqrt (T / 16)..Real.sqrt T,
        atkinsonPowerWeight T G L α (y ^ 2) * atkinsonRootKernel T b y := by
  have hab : Real.sqrt (T / 16) ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
  pm_6512
  have he : atkinsonPowerIntegral T G L α b =
      ∫ x in (T / 16)..T, atkinsonPowerIntegrand T G L α b x := by
    unfold atkinsonPowerIntegral
    rw [intervalIntegral.integral_of_le (by linarith : T / 16 ≤ T),
      ← integral_Icc_eq_integral_Ioc]
    pm_4382
    have hz : zetaAtkinsonDivisorTest T G L x = 0 := by
      pm_411
      pm_7094 hs
    simp [atkinsonPowerIntegrand, hz]
  have hc := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := atkinsonPowerIntegrand T G L α b) (f := fun y : ℝ => y ^ 2)
    (f' := fun y : ℝ => 2 * y) (a := Real.sqrt (T / 16)) (b := Real.sqrt T)
    (by fun_prop) (fun y _ => by simpa using! (hasDerivAt_id y).pow 2)
    (fun y hy => by
      pm_7272
      positivity)
  rw [Real.sq_sqrt (by positivity : 0 ≤ T / 16), Real.sq_sqrt hT.le] at hc
  pm_4341

theorem exists_norm_atkinsonPowerIntegral_le (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G →
      ‖atkinsonPowerIntegral T G L α b‖ ≤ C * G * T ^ (-α) := by
  obtain ⟨C, hC, hweight⟩ := exists_intervalC1Bound_atkinsonPowerWeight α
  refine ⟨16 * C, by positivity, ?_⟩
  intro T G L b hT hG hGT hL hwidth
  pm_4342
  have h := (hf.comp_sq ha.le hab).atkinsonRoot hT b ha hab
  rw [atkinsonPowerIntegral_eq_root hT hG hL hwidth α b, norm_mul, norm_ofNat]
  pm_4290 hfin mul_le_mul_of_nonneg_left h
  convert hfin using 1
  ring

end MathCollab.Density.Stronger.Atkinson
