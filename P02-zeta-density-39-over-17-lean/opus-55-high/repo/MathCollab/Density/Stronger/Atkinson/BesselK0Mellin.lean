module
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from DFIBesselMellin.lean,
exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/BESSEL_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain
Apache-2.0 attribution. No Estermann or general-modulus source closure is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselK0Convergence
import WeylPort.Analytic.RealLaplace

public section

open Complex Set MeasureTheory
open scoped Topology Interval
namespace MathCollab.Density.Stronger.Atkinson

/-- Fubini evaluation of the Mellin transform of the positive DFI kernel,
before simplifying the beta factor. -/
theorem integral_cpow_mul_dfiBesselK0_Ioi_eq_beta
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * (dfiBesselK0 x : ℂ)) =
      ((1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) (s / 2)) *
        Gamma s := by
  pm_4394
  pm_6750
  pm_4395
  pm_4389
  calc
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * (dfiBesselK0 x : ℂ)) =
        ∫ x : ℝ in Set.Ioi 0, ∫ t : ℝ in Set.Ioi 0, F (x, t) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          change (x : ℂ) ^ (s - 1) * (dfiBesselK0 x : ℂ) =
            ∫ t : ℝ in Set.Ioi 0, F (x, t)
          rw [dfiBesselK0_ofReal_eq_integral,
            ← MeasureTheory.integral_const_mul]
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ x : ℝ in Set.Ioi 0, F (x, t) := hswap
    _ = ∫ t : ℝ in Set.Ioi 0,
          ((1 / Real.cosh t : ℝ) : ℂ) ^ s * Gamma s := by
          pm_6011
          convert integral_cpow_mul_exp_neg_mul_Ioi_eq hs (Real.cosh_pos t) using 1
          grind
          simp_all
    _ = (∫ t : ℝ in Set.Ioi 0,
          ((1 / Real.cosh t : ℝ) : ℂ) ^ s) * Gamma s := by
          rw [MeasureTheory.integral_mul_const]
    _ = ((1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) (s / 2)) *
          Gamma s := by rw [integral_inv_cosh_cpow_Ioi_eq]

section
variable {s : ℂ} (hs : 0 < s.re)
include s hs
/-- The duplication formula simplifies the beta factor to the standard
Mellin symbol of `K₀`. -/
theorem half_beta_mul_Gamma_eq_besselK0MellinSymbol :
    ((1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) (s / 2)) * Gamma s =
      dfiBesselK0MellinSymbol s := by
  have hsHalf : 0 < (s / 2).re := by
    have hre : (s / 2).re = s.re / 2 := by
      norm_num [div_re, normSq]
    rw [hre]
    linarith
  have hdenRe : 0 < (s / 2 + (1 / 2 : ℂ)).re := by
    have hre : (s / 2 + (1 / 2 : ℂ)).re = s.re / 2 + 1 / 2 := by
      norm_num [div_re, normSq]
    rw [hre]
    linarith
  have hden : Gamma (s / 2 + (1 / 2 : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hdenRe
  have hden' : Gamma ((s + 1) / 2) ≠ 0 := by
    pm_1180
    exact hden
  have hdup :
      Gamma (s / 2) * Gamma (s / 2 + (1 / 2 : ℂ)) =
        Gamma s * (2 : ℂ) ^ (1 - s) * (Real.sqrt Real.pi : ℂ) := by
    have h := Complex.Gamma_mul_Gamma_add_half (s / 2)
    convert h using 1
    all_goals ring_nf
  have hp : (2 : ℂ) ^ (s - 2) * (2 : ℂ) ^ (1 - s) = 1 / 2 := by
    pm_4390
    rw [show s - 2 + (1 - s) = (-1 : ℂ) by ring,
      Complex.cpow_neg_one]
    norm_num
  pm_4391
  have hcore :
      (Real.sqrt Real.pi : ℂ) * Gamma (s / 2) * Gamma s =
        2 * ((2 : ℂ) ^ (s - 2) * Gamma (s / 2) ^ 2 *
          Gamma (s / 2 + (1 / 2 : ℂ))) := by
    symm
    calc
      2 * ((2 : ℂ) ^ (s - 2) * Gamma (s / 2) ^ 2 *
          Gamma (s / 2 + (1 / 2 : ℂ))) =
          2 * (2 : ℂ) ^ (s - 2) * Gamma (s / 2) *
            (Gamma (s / 2) * Gamma (s / 2 + (1 / 2 : ℂ))) := by ring
      _ = 2 * (2 : ℂ) ^ (s - 2) * Gamma (s / 2) *
            (Gamma s * (2 : ℂ) ^ (1 - s) *
              (Real.sqrt Real.pi : ℂ)) := by rw [hdup]
      _ = (Real.sqrt Real.pi : ℂ) * Gamma (s / 2) * Gamma s := by
        rw [show 2 * (2 : ℂ) ^ (s - 2) * Gamma (s / 2) *
              (Gamma s * (2 : ℂ) ^ (1 - s) *
                (Real.sqrt Real.pi : ℂ)) =
            2 * ((2 : ℂ) ^ (s - 2) * (2 : ℂ) ^ (1 - s)) *
              Gamma (s / 2) * Gamma s * (Real.sqrt Real.pi : ℂ) by ring,
          hp]
        ring
  rw [Complex.betaIntegral_eq_Gamma_mul_div (1 / 2) (s / 2)
    (by norm_num) hsHalf, show (1 / 2 : ℂ) + s / 2 =
      s / 2 + (1 / 2 : ℂ) by ring, hhalf]
  unfold dfiBesselK0MellinSymbol
  field_simp [hden, hden']
  pm_1180
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hcore

/-- The classical Mellin transform of the Macdonald kernel on its absolute
convergence half-plane. This is the analytic identity used in the positive
Voronoi transform. -/
theorem integral_cpow_mul_dfiBesselK0_Ioi_eq :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * (dfiBesselK0 x : ℂ)) =
      dfiBesselK0MellinSymbol s := by
  rw [integral_cpow_mul_dfiBesselK0_Ioi_eq_beta hs,
    half_beta_mul_Gamma_eq_besselK0MellinSymbol hs]
end

/-- Mellin transform of the square-root-scaled Macdonald kernel.  This is
the exact change of variables required when DFI's literal kernel
`K₀(A√x)` is compared with its Mellin--Barnes multiplier. -/
theorem mellin_dfiBesselK0_mul_sqrt
    {A : ℝ} (hA : 0 < A) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => (dfiBesselK0 (A * Real.sqrt x) : ℂ)) s =
      2 * (A : ℂ) ^ (-(2 * s)) * dfiBesselK0MellinSymbol (2 * s) := by
  pm_4392 dfiBesselK0
  have hs2 : 0 < (2 * s).re := by
    have hre : (2 * s).re = 2 * s.re := by norm_num
    rw [hre]
    linarith
  have hk : mellin (fun y : ℝ => (dfiBesselK0 y : ℂ)) (2 * s) =
      dfiBesselK0MellinSymbol (2 * s) := by
    unfold mellin
    simpa only [smul_eq_mul] using
      integral_cpow_mul_dfiBesselK0_Ioi_eq hs2
  rw [hk]
  change 2 * ((A : ℂ) ^ (-(2 * s)) * dfiBesselK0MellinSymbol (2 * s)) = _
  ring


end MathCollab.Density.Stronger.Atkinson
