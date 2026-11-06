module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiMellinInversion
public import Mathlib.Analysis.Complex.PhragmenLindelof
import WeylPort.Analytic.RealLaplace

public section

open Complex Finset Set Filter Topology MeasureTheory Asymptotics
open scoped Topology
open Classical
namespace MathCollab.Density.Stronger.Atkinson

section
variable {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
include g hg
/-- On each fixed vertical line, the Mellin transform of a DFI test
function decays faster than every prescribed power. -/
theorem DFIVoronoiTestFunction.mellin_polynomial_decay (σ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      |u| ^ n * ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  let F : SchwartzMap ℝ ℂ :=
    SchwartzMap.fourierTransformCLM ℂ (dfiVoronoiMellinKernelSchwartz hg σ)
  pm_524
  pm_165 hC C
  refine ⟨C, hC, ?_⟩
  intro u
  have hSem := SchwartzMap.le_seminorm' (𝕜 := ℝ) n 0 F
    (u / (2 * Real.pi))
  rw [iteratedDeriv_zero] at hSem
  pm_1228 u
  rw [hg.mellin_eq_fourier_mellinKernel σ u]
  change |u| ^ n * ‖F (u / (2 * Real.pi))‖ ≤ C
  pm_4895 hpi Real.pi
  have hAbs : |u| = (2 * Real.pi) * ‖u / (2 * Real.pi)‖ := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpi]
    grind
  rw [hAbs, mul_pow]
  dsimp only [C]
  calc
    (2 * Real.pi) ^ n * ‖u / (2 * Real.pi)‖ ^ n *
          ‖F (u / (2 * Real.pi))‖ =
        (2 * Real.pi) ^ n *
          (‖u / (2 * Real.pi)‖ ^ n * ‖F (u / (2 * Real.pi))‖) := by ring
    _ ≤ (2 * Real.pi) ^ n * SchwartzMap.seminorm ℝ n 0 F :=
      mul_le_mul_of_nonneg_left hSem' (pow_nonneg hpi.le n)

/-- Compact support gives a Mellin bound uniform on any prescribed finite
vertical strip.  This general form is needed when a Voronoi dual contour is
moved farther left to obtain arbitrary decay in its discrete frequency. -/
theorem DFIVoronoiTestFunction.exists_mellin_interval_bound
    (c d : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ), c ≤ σ → σ ≤ d → ∀ u : ℝ,
      ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  let Fleft : SchwartzMap ℝ ℂ :=
    dfiVoronoiMellinKernelSchwartz hg c
  let Fright : SchwartzMap ℝ ℂ :=
    dfiVoronoiMellinKernelSchwartz hg d
  let C : ℝ := (∫ v : ℝ, ‖Fleft v‖) + ∫ v : ℝ, ‖Fright v‖
  have hLeftInt : Integrable (fun v : ℝ ↦ ‖Fleft v‖) := Fleft.integrable.norm
  have hRightInt : Integrable (fun v : ℝ ↦ ‖Fright v‖) := Fright.integrable.norm
  pm_165 hC C
  pm_486 C hC σ hσLower hσUpper u
  let Fσ : SchwartzMap ℝ ℂ := dfiVoronoiMellinKernelSchwartz hg σ
  have hPoint : ∀ v : ℝ, ‖Fσ v‖ ≤ ‖Fleft v‖ + ‖Fright v‖ := by
    intro v
    have hExp : Real.exp (-σ * v) ≤
        Real.exp (-c * v) + Real.exp (-d * v) := by
      by_cases hv : 0 ≤ v
      · have hlin : -σ * v ≤ -c * v := by nlinarith
        pm_8292 le_add_of_nonneg_right
      · have hv' : v < 0 := lt_of_not_ge hv
        have hlin : -σ * v ≤ -d * v := by nlinarith
        pm_8292 le_add_of_nonneg_left
    change ‖(Real.exp (-σ * v) : ℂ) * g (Real.exp (-v))‖ ≤
      ‖(Real.exp (-c * v) : ℂ) * g (Real.exp (-v))‖ +
      ‖(Real.exp (-d * v) : ℂ) * g (Real.exp (-v))‖
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    nlinarith [norm_nonneg (g (Real.exp (-v)))]
  have hLone : ‖Fσ.toLp 1‖ ≤ C := by
    rw [SchwartzMap.norm_toLp_one]
    calc
      (∫ v : ℝ, ‖Fσ v‖) ≤
          ∫ v : ℝ, (‖Fleft v‖ + ‖Fright v‖) := by
        exact integral_mono Fσ.integrable.norm
          (hLeftInt.add hRightInt) hPoint
      _ = C := by
        rw [integral_add hLeftInt hRightInt]
  rw [hg.mellin_eq_fourier_mellinKernel σ u]
  exact (SchwartzMap.norm_fourier_apply_le_toLp_one Fσ
    (u / (2 * Real.pi))).trans hLone

/-- The compact support gives a bound for the Mellin transform uniform on
the complete DFI contour-shift strip. -/
theorem DFIVoronoiTestFunction.exists_mellin_strip_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 3 / 2 → ∀ u : ℝ,
      ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C :=
  hg.exists_mellin_interval_bound (-(1 / 2 : ℝ)) (3 / 2 : ℝ)

theorem DFIVoronoiTestFunction.differentiable_mellin :
    Differentiable ℂ (mellin g) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow
    (hg.continuous.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0))
    (hg.isBigO_atTop (s.re + 1)) (by linarith)
    (hg.isBigO_atZero (s.re - 1)) (by linarith)

/-- Arbitrary-order polynomial Mellin bound on either boundary of the
standard DFI strip. -/
theorem DFIVoronoiTestFunction.exists_mellin_pow_boundary_bound (j : ℕ) (σ : ℝ)
    (hσLower : -(1 / 2 : ℝ) ≤ σ) (hσUpper : σ ≤ 3 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖(((σ : ℂ) + (u : ℂ) * I) - 3) ^ j *
        mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨M, hM, hMellin⟩ := hg.exists_mellin_strip_bound
  pm_98 D hD hDecay hg.mellin_polynomial_decay σ j
  refine ⟨4 ^ j * 2 ^ (j - 1) * (M + D), by positivity, ?_⟩
  intro u
  pm_256 s σ u I
  pm_7366 hSigma σ
  have hsNorm : ‖s - 3‖ ≤ 4 * (1 + |u|) := by
    calc
      ‖s - 3‖ ≤ |(s - 3).re| + |(s - 3).im| :=
        Complex.norm_le_abs_re_add_abs_im (s - 3)
      _ = |σ - 3| + |u| := by simp [s]
      _ ≤ 4 * (1 + |u|) := by nlinarith [abs_nonneg u]
  have hPow : ‖s - 3‖ ^ j ≤ 4 ^ j * (1 + |u|) ^ j := by
    simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg (s - 3)) hsNorm j
  have hBinom : (1 + |u|) ^ j ≤ 2 ^ (j - 1) * (1 + |u| ^ j) := by
    simpa using add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg u) j
  have hMu : ‖mellin g s‖ ≤ M := hMellin σ hσLower hσUpper u
  have hDu : |u| ^ j * ‖mellin g s‖ ≤ D := hDecay u
  have hCombined : (1 + |u| ^ j) * ‖mellin g s‖ ≤ M + D := by
    calc
      (1 + |u| ^ j) * ‖mellin g s‖ =
          ‖mellin g s‖ + |u| ^ j * ‖mellin g s‖ := by ring
      _ ≤ M + D := add_le_add hMu hDu
  rw [norm_mul, norm_pow]
  calc
    ‖s - 3‖ ^ j * ‖mellin g s‖ ≤
        (4 ^ j * (1 + |u|) ^ j) * ‖mellin g s‖ :=
      mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
    _ ≤ (4 ^ j * (2 ^ (j - 1) * (1 + |u| ^ j))) *
        ‖mellin g s‖ := by gcongr
    _ = 4 ^ j * 2 ^ (j - 1) *
        ((1 + |u| ^ j) * ‖mellin g s‖) := by ring
    _ ≤ 4 ^ j * 2 ^ (j - 1) * (M + D) := by gcongr

/-- Phragmén--Lindelöf makes the arbitrary-order boundary estimate uniform
throughout the standard DFI strip. -/
theorem DFIVoronoiTestFunction.exists_mellin_pow_strip_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 3 / 2 → ∀ u : ℝ,
      ‖(((σ : ℂ) + (u : ℂ) * I) - 3) ^ j *
        mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨Ca, hCa, hBoundA⟩ :=
    hg.exists_mellin_pow_boundary_bound j (-(1 / 2 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨Cb, hCb, hBoundB⟩ :=
    hg.exists_mellin_pow_boundary_bound j (3 / 2 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨M, hM, hMellin⟩ := hg.exists_mellin_strip_bound
  let f : ℂ → ℂ := fun s ↦ (s - 3) ^ j * mellin g s
  let strip : Set ℂ := Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (3 / 2 : ℝ)
  let l : Filter ℂ := comap (abs ∘ Complex.im) atTop ⊓ Filter.principal strip
  have hDiff : Differentiable ℂ f := by
    dsimp [f]
    exact ((differentiable_id.sub_const 3).pow j).mul hg.differentiable_mellin
  have hStripEventually : ∀ᶠ z : ℂ in l, z ∈ strip := by
    exact (show ∀ᶠ z : ℂ in Filter.principal strip, z ∈ strip by
      simp).filter_mono inf_le_right
  have hFPoly : f =O[l] (fun z : ℂ ↦ (4 + |z.im|) ^ j) := by
    apply IsBigO.of_bound M
    filter_upwards [hStripEventually] with z hz
    have hzLower : -(1 / 2 : ℝ) ≤ z.re := hz.1.le
    have hzUpper : z.re ≤ 3 / 2 := hz.2.le
    pm_7366 hRe z.re
    have hzNorm : ‖z - 3‖ ≤ 4 + |z.im| := by
      calc
        ‖z - 3‖ ≤ |(z - 3).re| + |(z - 3).im| :=
          Complex.norm_le_abs_re_add_abs_im (z - 3)
        _ = |z.re - 3| + |z.im| := by simp
        _ ≤ 4 + |z.im| := by linarith
    have hPow : ‖z - 3‖ ^ j ≤ (4 + |z.im|) ^ j := by
      simpa using pow_le_pow_left₀ (norm_nonneg (z - 3)) hzNorm j
    have hMellinZ : ‖mellin g z‖ ≤ M := by
      have hzEq : ((z.re : ℂ) + (z.im : ℂ) * I) = z := by
        apply Complex.ext <;> simp
      rw [← hzEq]
      exact hMellin z.re hzLower hzUpper z.im
    change ‖(z - 3) ^ j * mellin g z‖ ≤ M * ‖(4 + |z.im|) ^ j‖
    rw [norm_mul, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (4 + |z.im|) ^ j)]
    calc
      ‖z - 3‖ ^ j * ‖mellin g z‖ ≤
          (4 + |z.im|) ^ j * ‖mellin g z‖ :=
        mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
      _ ≤ (4 + |z.im|) ^ j * M :=
        mul_le_mul_of_nonneg_left hMellinZ (by positivity)
      _ = M * (4 + |z.im|) ^ j := by ring
  have hRealPoly :
      (fun t : ℝ ↦ (4 + t) ^ j) =O[atTop]
        (fun t : ℝ ↦ Real.exp (Real.exp t)) := by
    have hShift := (Real.isLittleO_pow_exp_atTop (n := j)).comp_tendsto
      (tendsto_atTop_add_const_left atTop (4 : ℝ) tendsto_id)
    have hFirst : (fun t : ℝ ↦ (4 + t) ^ j) =O[atTop]
        (fun t : ℝ ↦ Real.exp (t + 4)) := by
      simpa [add_comm, Function.comp_def] using hShift.isBigO
    have hSecond : (fun t : ℝ ↦ Real.exp (t + 4)) =O[atTop]
        (fun t : ℝ ↦ Real.exp (Real.exp t)) := by
      apply IsBigO.of_bound (Real.exp 4)
      filter_upwards with t
      have htExp : t ≤ Real.exp t :=
        (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)).trans
          (Real.add_one_le_exp t)
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [Real.exp_add]
      calc
        Real.exp t * Real.exp 4 = Real.exp 4 * Real.exp t := by ring
        _ ≤ Real.exp 4 * Real.exp (Real.exp t) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htExp)
            (Real.exp_pos 4).le
    exact hFirst.trans hSecond
  have hToTop : Tendsto (abs ∘ Complex.im) l atTop := by
    exact tendsto_comap.mono_left inf_le_left
  have hPolyComplex :
      (fun z : ℂ ↦ (4 + |z.im|) ^ j) =O[l]
        (fun z : ℂ ↦ Real.exp (Real.exp |z.im|)) := by
    simpa [Function.comp_def] using hRealPoly.comp_tendsto hToTop
  have hGrowth : ∃ c < Real.pi / ((3 / 2 : ℝ) - (-(1 / 2 : ℝ))), ∃ B,
      f =O[l] (fun z ↦ Real.exp (B * Real.exp (c * |z.im|))) := by
    refine ⟨1, ?_, 1, ?_⟩
    · nlinarith [Real.pi_gt_three]
    · simpa using hFPoly.trans hPolyComplex
  refine ⟨Ca + Cb, add_nonneg hCa hCb, ?_⟩
  intro σ hσLower hσUpper u
  pm_256 z σ u I
  have hPL := PhragmenLindelof.vertical_strip
    (f := f) (a := -(1 / 2 : ℝ)) (b := (3 / 2 : ℝ))
    (C := Ca + Cb) hDiff.diffContOnCl (by simpa [l, strip] using hGrowth)
    (fun w hw ↦ by
      have hwEq : (-(1 / 2 : ℂ) + (w.im : ℂ) * I) = w := by
        apply Complex.ext
        · norm_num
          exact hw.symm
        · simp
      pm_8445 hBoundA le_add_of_nonneg_right hCb
      exact h)
    (fun w hw ↦ by
      have hwEq : ((3 / 2 : ℂ) + (w.im : ℂ) * I) = w := by
        apply Complex.ext
        · norm_num
          exact hw.symm
        · simp
      pm_8445 hBoundB le_add_of_nonneg_left hCa
      exact h)
    (z := z) (by simpa [z] using hσLower) (by simpa [z] using hσUpper)
  simpa [f, z] using hPL

/-- Arbitrary Mellin decay uniformly throughout the actual q=1 contour strip. -/
theorem DFIVoronoiTestFunction.exists_mellin_weighted_strip_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, -(1/2 : ℝ) ≤ σ → σ ≤ 3/2 → ∀ u : ℝ,
      (1 + |u|)^j * ‖mellin g ((σ : ℂ) + (u : ℂ)*I)‖ ≤ C := by
  obtain ⟨D,hD,hbound⟩ := hg.exists_mellin_pow_strip_bound j
  refine ⟨2^j * D, by positivity, ?_⟩
  intro σ hσ hσ' u
  let z : ℂ := (σ : ℂ) + (u : ℂ)*I
  have hn1 : 1 ≤ ‖z-3‖ := by
    have h := Complex.abs_re_le_norm (z-3)
    have hr : (z-3).re = σ-3 := by simp [z]
    rw [hr, abs_of_nonpos (by linarith : σ-3 ≤ 0)] at h
    linarith
  have hnu : |u| ≤ ‖z-3‖ := by simpa [z] using Complex.abs_im_le_norm (z-3)
  have hpow : (1+|u|)^j ≤ 2^j * ‖z-3‖^j := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) j
  have hb := hbound σ hσ hσ' u
  rw [norm_mul, norm_pow] at hb
  calc
    _ ≤ (2^j * ‖z-3‖^j) * ‖mellin g z‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = 2^j * (‖z-3‖^j * ‖mellin g z‖) := by ring
    _ ≤ 2^j * D := mul_le_mul_of_nonneg_left hb (by positivity)
end

end MathCollab.Density.Stronger.Atkinson
