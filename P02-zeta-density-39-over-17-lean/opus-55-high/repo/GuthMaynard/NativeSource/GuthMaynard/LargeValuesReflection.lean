module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import GuthMaynard.NativeSource.GuthMaynard.LargeValuesPoisson
public import MathCollab.Density.Oscillatory
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex MeasureTheory Real Set
open scoped ContDiff FourierTransform SchwartzMap

namespace GuthMaynard.NativeMoment

private theorem traceSchwartz_coe (cutoff : GMSmoothCutoff) (t : ℝ) :
    (gmTraceKernelSchwartz cutoff t : ℝ → ℂ) = gmTraceKernel cutoff t :=
  funext (gmTraceKernelSchwartz_apply cutoff t)

/-!
# Smooth reflection for the Guth--Maynard trace kernel

This module proves the source-normalized finite identities and oscillatory
integral estimates used in Guth--Maynard Lemma 6.2.  In particular, the
Fourier coefficient is first restricted to the common interval used in the
paper and then rescaled so that the remaining oscillatory integral is
independent of the positive Fourier mode.
-/

/-- Falling coefficient in the repeated derivative of `x^z`. -/
noncomputable def gmCpowDerivativeCoeff (z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => z * gmCpowDerivativeCoeff (z - 1) n

section
variable (z : ℂ)
include z
@[simp]
theorem gmCpowDerivativeCoeff_zero :
    gmCpowDerivativeCoeff z 0 = 1 := by
  rfl

theorem gmCpowDerivativeCoeff_succ (n : ℕ) :
    gmCpowDerivativeCoeff z (n + 1) =
      z * gmCpowDerivativeCoeff (z - 1) n := by
  rfl

/-- Repeated real derivative of a complex power on the positive axis. -/
theorem iteratedDeriv_ofReal_cpow (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (fun y : ℝ => (y : ℂ) ^ z) x =
      gmCpowDerivativeCoeff z n * (x : ℂ) ^ (z - n) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv :
          deriv (fun y : ℝ => (y : ℂ) ^ z) =ᶠ[nhds x]
            fun y : ℝ => z * (y : ℂ) ^ (z - 1) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        pm_5458 hz z
        · exact Complex.deriv_ofReal_cpow_const hy.ne' hz
      rw [hderiv.iteratedDeriv_eq]
      rw [iteratedDeriv_const_mul_field, ih (z := z - 1)]
      rw [gmCpowDerivativeCoeff_succ]
      have hexponent : z - 1 - (n : ℂ) = z - ((n + 1 : ℕ) : ℂ) := by
        push_cast
        ring
      rw [hexponent]
      ring

/-- Polynomial growth of the falling coefficient, uniform in the exponent. -/
theorem norm_gmCpowDerivativeCoeff_le (n : ℕ) :
    ‖gmCpowDerivativeCoeff z n‖ ≤ (‖z‖ + n) ^ n := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [gmCpowDerivativeCoeff_succ, norm_mul]
      have hshift : ‖z - 1‖ + n ≤ ‖z‖ + (n + 1) := by
        have hnorm : ‖z - 1‖ ≤ ‖z‖ + 1 := by
          calc
            ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = ‖z‖ + 1 := by simp
        linarith
      calc
        ‖z‖ * ‖gmCpowDerivativeCoeff (z - 1) n‖ ≤
            ‖z‖ * (‖z - 1‖ + n) ^ n :=
          mul_le_mul_of_nonneg_left (ih (z - 1)) (norm_nonneg _)
        _ ≤ (‖z‖ + (n + 1)) * (‖z‖ + (n + 1)) ^ n := by
          gcongr
          exact le_add_of_nonneg_right (by positivity)
        _ = (‖z‖ + ((n : ℝ) + 1)) ^ (n + 1) := by
          rw [pow_succ']
        _ = (‖z‖ + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
          norm_num
end

private noncomputable def gmCutoffSqComplex
    (cutoff : GMSmoothCutoff) (x : ℝ) : ℂ :=
  (cutoff x : ℂ) ^ 2

private theorem contDiff_gmCutoffSqComplex (cutoff : GMSmoothCutoff) :
    ContDiff ℝ ∞ (gmCutoffSqComplex cutoff) := by
  exact (Complex.ofRealCLM.contDiff.comp cutoff.smooth).pow 2

private theorem hasCompactSupport_gmCutoffSqComplex
    (cutoff : GMSmoothCutoff) :
    HasCompactSupport (gmCutoffSqComplex cutoff) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  by_contra hnot
  apply hx
  have hcut : cutoff x = 0 := by
    by_contra hne
    exact hnot (cutoff.support hne)
  simp [gmCutoffSqComplex, hcut]

private noncomputable def gmCutoffSqSchwartz
    (cutoff : GMSmoothCutoff) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_gmCutoffSqComplex cutoff).toSchwartzMap
    (contDiff_gmCutoffSqComplex cutoff)

@[simp]
private theorem gmCutoffSqSchwartz_apply (cutoff : GMSmoothCutoff) (x : ℝ) :
    gmCutoffSqSchwartz cutoff x = gmCutoffSqComplex cutoff x := rfl

private theorem gmTraceKernel_eq_cutoffSq_mul_cpow
    (cutoff : GMSmoothCutoff) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    gmTraceKernel cutoff t x =
      gmCutoffSqComplex cutoff x * (x : ℂ) ^ ((t : ℂ) * I) := by
  unfold gmTraceKernel gmCutoffSqComplex
  pm_4851 hx.ne' hx.le
  congr 2
  push_cast
  ring

/-- Uniform derivative bound for the Mellin oscillation on the cutoff
support. -/
theorem norm_iteratedDeriv_ofReal_cpow_mul_I_le
    (t : ℝ) (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖iteratedDeriv n (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x‖ ≤
      (|t| + n) ^ n := by
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  pm_5480 t hxPos
  have hpow : ‖(x : ℂ) ^ ((t : ℂ) * I - n)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
    pm_1352 t
    exact Real.rpow_le_one_of_one_le_of_nonpos hx
      (neg_nonpos.mpr (Nat.cast_nonneg n))
  calc
    ‖gmCpowDerivativeCoeff ((t : ℂ) * I) n‖ *
          ‖(x : ℂ) ^ ((t : ℂ) * I - n)‖ ≤
        (‖((t : ℂ) * I)‖ + n) ^ n * 1 :=
      mul_le_mul hcoeff hpow (norm_nonneg _) (by positivity)
    _ = (|t| + n) ^ n := by
      simp [Real.norm_eq_abs]

private theorem mellinDerivativePower_le (t : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    (|t| + k) ^ k ≤
      (n + 1 : ℝ) ^ n * (1 + |t|) ^ n := by pm_4852 hn0

private theorem contDiffAt_ofReal_cpow_mul_I
    (t : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ n (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x := by
  have hEq :
      (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) =ᶠ[nhds x]
        fun y : ℝ => Complex.exp ((((t * Real.log y : ℝ) : ℂ) * I)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    pm_4853
  pm_4854 t x hx.ne'

/-- Guth--Maynard Lemma 4.3 in the exact two-parameter form needed to make
the smooth-reflection frequency truncation uniform. -/
theorem gmTraceKernel_uniform_iteratedFDeriv (cutoff : GMSmoothCutoff)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x : ℝ,
      ‖iteratedFDeriv ℝ n (gmTraceKernel cutoff t) x‖ ≤
        C * (1 + |t|) ^ n := by
  let C : ℝ := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) *
      SchwartzMap.seminorm ℝ 0 i (gmCutoffSqSchwartz cutoff) *
        (n + 1 : ℝ) ^ n
  pm_4855
  refine ⟨C, hC, ?_⟩
  intro t x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hxLow : x < 1
  · have hzero : gmTraceKernel cutoff t =ᶠ[nhds x] 0 := by
      filter_upwards [Iio_mem_nhds hxLow] with y hy
      simp [gmTraceKernel, gmSmoothCutoff_eq_zero_of_lt_one cutoff hy]
    rw [hzero.iteratedDeriv_eq]
    simp
    positivity
  by_cases hxHigh : 2 < x
  · have hzero : gmTraceKernel cutoff t =ᶠ[nhds x] 0 := by
      filter_upwards [Ioi_mem_nhds hxHigh] with y hy
      simp [gmTraceKernel,
        gmSmoothCutoff_eq_zero_of_two_le cutoff (le_of_lt hy)]
    rw [hzero.iteratedDeriv_eq]
    simp
    positivity
  have hxIcc : x ∈ Set.Icc (1 : ℝ) 2 := ⟨le_of_not_gt hxLow, le_of_not_gt hxHigh⟩
  have hxPos : 0 < x := zero_lt_one.trans_le hxIcc.1
  have hlocal : gmTraceKernel cutoff t =ᶠ[nhds x]
      fun y : ℝ => gmCutoffSqComplex cutoff y *
        (y : ℂ) ^ ((t : ℂ) * I) := by
    filter_upwards [Ioi_mem_nhds hxPos] with y hy
    exact gmTraceKernel_eq_cutoffSq_mul_cpow cutoff t hy
  rw [hlocal.iteratedDeriv_eq]
  have hcutSmooth : ContDiffAt ℝ n (gmCutoffSqComplex cutoff) x :=
    (contDiff_gmCutoffSqComplex cutoff).contDiffAt.of_le (by exact_mod_cast le_top)
  have hphaseSmooth := contDiffAt_ofReal_cpow_mul_I t n hxPos
  change ‖iteratedDeriv n
      (gmCutoffSqComplex cutoff * fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x‖ ≤
    C * (1 + |t|) ^ n
  rw [iteratedDeriv_mul hcutSmooth hphaseSmooth]
  calc
    ‖∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * iteratedDeriv i (gmCutoffSqComplex cutoff) x *
          iteratedDeriv (n - i) (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        ‖(n.choose i : ℂ) * iteratedDeriv i (gmCutoffSqComplex cutoff) x *
          iteratedDeriv (n - i) (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) *
          SchwartzMap.seminorm ℝ 0 i (gmCutoffSqSchwartz cutoff) *
            (n + 1 : ℝ) ^ n) * (1 + |t|) ^ n := by
      pm_4856
      pm_4947 hcut gmCutoffSqSchwartz cutoff gmCutoffSqComplex norm_iteratedDeriv_ofReal_cpow_mul_I_le mellinDerivativePower_le
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        (n.choose i : ℝ) * ‖iteratedDeriv i (gmCutoffSqComplex cutoff) x‖ *
            ‖iteratedDeriv (n - i)
              (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x‖ ≤
          (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (gmCutoffSqSchwartz cutoff) *
              (|t| + ((n - i : ℕ) : ℝ)) ^ (n - i) := by
            gcongr
        _ ≤ (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (gmCutoffSqSchwartz cutoff) *
              ((n + 1 : ℝ) ^ n * (1 + |t|) ^ n) := by
            gcongr
        _ = ((n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (gmCutoffSqSchwartz cutoff) *
              (n + 1 : ℝ) ^ n) * (1 + |t|) ^ n := by ring
    _ = C * (1 + |t|) ^ n := by
      dsimp only [C]
      rw [Finset.sum_mul]

private theorem integral_norm_iteratedFDeriv_gmTraceKernel_le
    (cutoff : GMSmoothCutoff) (p : ℕ) {D : ℝ}
    (hbound : ∀ t x : ℝ,
      ‖iteratedFDeriv ℝ p (gmTraceKernel cutoff t) x‖ ≤
        D * (1 + |t|) ^ p) (t : ℝ) :
    (∫ x : ℝ, ‖iteratedFDeriv ℝ p (gmTraceKernel cutoff t) x‖) ≤
      D * (1 + |t|) ^ p := by
  pm_4991 gmTraceKernel cutoff traceSchwartz_coe gmTraceKernelSchwartz
  have hsupport : Function.support f ⊆ Set.Icc (1 : ℝ) 2 := by
    intro x hx
    pm_5901 hxOutside x hxLow hxUpper
    have hzero : gmTraceKernel cutoff t =ᶠ[nhds x] 0 := by
      pm_5320 hxOutside hxLow hxHigh gmTraceKernel
    apply hx
    pm_4857
  pm_582 x hx
  pm_1341 gmTraceKernel cutoff
  calc
    (∫ x : ℝ in Set.Icc 1 2, f x) ≤
        ∫ _x : ℝ in Set.Icc 1 2, D * (1 + |t|) ^ p := by
      pm_4858
      · intro x hx
        exact hbound t x
    _ = D * (1 + |t|) ^ p := by
      simp
      ring

set_option hygiene false in
macro "pc_94" x1:ident x2:ident x3:ident x4:ident x5:ident x6:ident : tactic => `(tactic| (
  refine ⟨C, hC, ?_⟩
  intro t ξ
  have hIntegrable : ∀ (k p : ℕ), k ≤ (0 : ℕ∞) → p ≤ (⊤ : ℕ∞) →
      Integrable (fun x : ℝ =>
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ p ($x1:ident $x2:ident t) x‖) := by
    intro k p _hk _hp
    simpa only [$x3:ident] using
      (SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
        ($x4:ident $x2:ident t) k p)
  have hFourier := pow_mul_norm_iteratedFDeriv_fourier_le
    (f := $x1:ident $x2:ident t)
    (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞))
    ($x5:ident $x2:ident t) hIntegrable
    (k := 0) (n := n) (by norm_num) (by simp) ξ
  simp only [pow_zero, one_mul, zero_add, Finset.range_one,
    norm_iteratedFDeriv_zero, Finset.singleton_product, Finset.sum_map,
    Function.Embedding.sectR_apply] at hFourier
  have hFourier' : |ξ| ^ n * ‖$x6:ident $x2:ident t ξ‖ ≤
      2 ^ n * ∑ p ∈ Finset.range (n + 1),
        ∫ x : ℝ, ‖iteratedFDeriv ℝ p ($x1:ident $x2:ident t) x‖ := by
    convert hFourier using 1
    · simp [$x6:ident, Real.norm_eq_abs, SchwartzMap.fourier_coe, $x3:ident]
    · congr 1
      norm_num))
/-- Uniform two-parameter Fourier decay.  The constant depends only on the
fixed cutoff and derivative order, while the complete `t` dependence is the
source polynomial `(1+|t|)^n`. -/
theorem gmTraceFourier_uniform_decay (cutoff : GMSmoothCutoff) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ,
      |ξ| ^ n * ‖gmTraceFourier cutoff t ξ‖ ≤
        C * (1 + |t|) ^ n := by
  choose D hD hDbound using fun p : ℕ =>
    gmTraceKernel_uniform_iteratedFDeriv cutoff p
  let C : ℝ := 2 ^ n * ∑ p ∈ Finset.range (n + 1), D p
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun p _ => hD p)
  pc_94 gmTraceKernel cutoff traceSchwartz_coe gmTraceKernelSchwartz contDiff_gmTraceKernel gmTraceFourier

  calc
    |ξ| ^ n * ‖gmTraceFourier cutoff t ξ‖ ≤
        2 ^ n * ∑ p ∈ Finset.range (n + 1),
          ∫ x : ℝ, ‖iteratedFDeriv ℝ p (gmTraceKernel cutoff t) x‖ := hFourier'
    _ ≤ 2 ^ n * ∑ p ∈ Finset.range (n + 1),
        D p * (1 + |t|) ^ n := by
      pm_4859
      have hint := integral_norm_iteratedFDeriv_gmTraceKernel_le
        cutoff p (hDbound p) t
      calc
        (∫ x : ℝ, ‖iteratedFDeriv ℝ p (gmTraceKernel cutoff t) x‖) ≤
            D p * (1 + |t|) ^ p := hint
        _ ≤ D p * (1 + |t|) ^ n := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by nlinarith [abs_nonneg t]) hpn) (hD p)
    _ = C * (1 + |t|) ^ n := by
      dsimp only [C]
      rw [← Finset.sum_mul]
      ring

/-- Reversing the Fourier frequency is complex conjugation together with
reversal of the Mellin ordinate.  This supplies the negative-frequency half
of the smooth-reflection expansion from the positive-frequency formula. -/
theorem gmTraceFourier_neg_eq_conj (cutoff : GMSmoothCutoff) (t ξ : ℝ) :
    gmTraceFourier cutoff t (-ξ) =
      star (gmTraceFourier cutoff (-t) ξ) := by
  pm_4958 gmTraceFourier I gmTraceKernelSchwartz cutoff
  have hConj : (∫ x : ℝ, star (f x)) = star (∫ x : ℝ, f x) := by
    convert (integral_conj (f := f) (μ := volume)) using 1 <;> rfl
  rw [← hConj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  dsimp only [f]
  simp only [Real.inner_apply, gmTraceKernelSchwartz_apply, Complex.star_def,
    smul_eq_mul]
  unfold gmTraceKernel
  rw [map_mul, map_mul, map_pow, conj_ofReal, ← Complex.exp_conj,
    ← Complex.exp_conj]
  push_cast
  ring_nf
  pm_93 map_neg map_mul map_ofNat conj_ofReal conj_I
  ring_nf

/-- The `gmCutoffMellin` definition used by the source-facing construction in `LargeValuesReflection`. -/
noncomputable def gmCutoffMellin
    (cutoff : GMSmoothCutoff) (r : ℝ) : ℂ :=
  mellin (fun y : ℝ => ((cutoff y : ℂ) ^ 2))
    ((1 : ℂ) + (r : ℂ) * I)

set_option hygiene false in
macro "pb_2675" : tactic => `(tactic| (
  rw [mellin_eq_fourier, SchwartzMap.fourier_coe]
  simp
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (r / (2 * Real.pi)))
  funext u))
theorem gmCutoffMellin_eq_fourier
    (cutoff : GMSmoothCutoff) (r : ℝ) :
    gmCutoffMellin cutoff r =
      𝓕 (gmMellinKernelSchwartz cutoff) (r / (2 * Real.pi)) := by
  unfold gmCutoffMellin
  pb_2675
  rw [gmMellinKernelSchwartz_apply]
  simp [gmMellinKernel, Complex.ofReal_exp]

theorem continuous_gmCutoffMellin (cutoff : GMSmoothCutoff) :
    Continuous (gmCutoffMellin cutoff) := by
  have hEq : gmCutoffMellin cutoff = fun r : ℝ =>
      𝓕 (gmMellinKernelSchwartz cutoff) (r / (2 * Real.pi)) := by
    funext r
    exact gmCutoffMellin_eq_fourier cutoff r
  rw [hEq]
  exact (𝓕 (gmMellinKernelSchwartz cutoff)).continuous.comp
    (continuous_id.div_const (2 * Real.pi))

/-- The fixed Mellin weight has arbitrary polynomial decay.  This is the
quantitative input used to truncate the Mellin ordinate in the published
smooth-reflection argument. -/
theorem gmCutoffMellin_polynomial_decay
    (cutoff : GMSmoothCutoff) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      |r| ^ n * ‖gmCutoffMellin cutoff r‖ ≤ C := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 (gmMellinKernelSchwartz cutoff)
  pm_524
  pm_165 hC C
  pm_4862
  have hSem' : ‖r / (2 * Real.pi)‖ ^ n *
      ‖F (r / (2 * Real.pi))‖ ≤ SchwartzMap.seminorm ℝ n 0 F := by
    exact hSem
  rw [gmCutoffMellin_eq_fourier]
  pm_4861

private noncomputable def gmMellinReflectionIntegrand
    (cutoff : GMSmoothCutoff) (t q : ℝ) (v r : ℝ) : ℂ :=
  (v / q : ℂ)⁻¹ *
    Complex.exp (-(((r * Real.log (v / q) : ℝ) : ℂ) * I)) *
      gmCutoffMellin cutoff r *
        Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))

private theorem integrable_gmMellinReflectionIntegrand
    (cutoff : GMSmoothCutoff) (t : ℝ) {N m M : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    Integrable (Function.uncurry
      (gmMellinReflectionIntegrand cutoff t (N * m)))
      ((volume.restrict (Set.uIoc (N : ℝ) (2 * N * M))).prod volume) := by
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    pm_4863
    pm_4864
    nlinarith
  pm_6201 hH
  have hConst : Integrable
      (fun _v : ℝ => (m : ℝ))
      (volume.restrict (Set.uIoc (N : ℝ) (2 * N * M))) := by
    exact MeasureTheory.integrableOn_const (hs := by simp)
  have hDom := hConst.mul_prod hH.norm
  apply hDom.mono'
  · have hElementary : AEStronglyMeasurable
        (fun z : ℝ × ℝ =>
          (z.1 / (N * m) : ℂ)⁻¹ *
            Complex.exp (-(((z.2 * Real.log (z.1 / (N * m)) : ℝ) : ℂ) * I)) *
              Complex.exp ((((t * Real.log z.1 - 2 * Real.pi * z.1 : ℝ) : ℂ) * I)))
        ((volume.restrict (Set.uIoc (N : ℝ) (2 * N * M))).prod volume) := by
      exact (by measurability : StronglyMeasurable fun z : ℝ × ℝ =>
        (z.1 / (N * m) : ℂ)⁻¹ *
          Complex.exp (-(((z.2 * Real.log (z.1 / (N * m)) : ℝ) : ℂ) * I)) *
            Complex.exp ((((t * Real.log z.1 - 2 * Real.pi * z.1 : ℝ) : ℂ) * I)))
        |>.aestronglyMeasurable
    pm_6206 gmMellinReflectionIntegrand
  · rw [Measure.ae_prod_iff_ae_ae (by
      apply measurableSet_le
      · have hHM : Measurable fun z : ℝ × ℝ => gmCutoffMellin cutoff z.2 :=
          (continuous_gmCutoffMellin cutoff).measurable.comp measurable_snd
        unfold gmMellinReflectionIntegrand Function.uncurry
        measurability
      · exact ((continuous_gmCutoffMellin cutoff).norm.comp continuous_snd
          |>.const_mul (m : ℝ)).measurable)]
    pm_8131
    let z : ℝ × ℝ := (v, r)
    have hvIoc : v ∈ Set.Ioc (N : ℝ) (2 * N * M) := by
      simpa only [Set.uIoc_of_le hAB] using hv
    have hvLower : (N : ℝ) ≤ z.1 := by
      simpa only [z] using hvIoc.1.le
    have hvPos : 0 < z.1 := (by exact_mod_cast hN : (0 : ℝ) < N).trans_le hvLower
    rw [show ‖Function.uncurry
        (gmMellinReflectionIntegrand cutoff t (N * m)) z‖ =
        ((N * m : ℝ) / z.1) * ‖gmCutoffMellin cutoff z.2‖ by
      unfold gmMellinReflectionIntegrand Function.uncurry
      simp only [norm_mul, norm_inv]
      simp [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hvPos, inv_div]]
    have hratio : (N * m : ℝ) / z.1 ≤ m := by
      rw [div_le_iff₀ hvPos]
      pm_96 hmReal m
      nlinarith
    exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)

/-- Mellin inversion on the source line `Re s = 1`, expanded as the literal
vertical integral used in Guth--Maynard Lemma 6.2. -/
theorem gmCutoffSq_eq_verticalMellinIntegral (cutoff : GMSmoothCutoff)
    {x : ℝ} (hx : 0 < x) :
    (cutoff x : ℂ) ^ 2 =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          (x : ℂ) ^ (-((1 : ℂ) + (r : ℂ) * I)) *
            mellin (fun y : ℝ => ((cutoff y : ℂ) ^ 2))
              ((1 : ℂ) + (r : ℂ) * I) := by
  rw [← gmCutoffSq_mellinInversion cutoff hx]
  unfold mellinInv
  simp only [smul_eq_mul]
  norm_num

export MathCollab.Density (norm_gmReflectionIntegral_le_endpoint_variation gmReflectionIntegral_eq_parts norm_gmReflectionIntegral_le_right norm_gmReflectionIntegral_le_left norm_gmReflectionIntegral_le_length_div gmReflectionRatio_mul_primitiveDeriv intervalIntegrable_gmReflectionIntegrand norm_gmReflectionIntegrand gmReflectionIntegral gmReflectionPrimitive norm_gmReflectionRatio gmReflectionRatio norm_gmReflectionPrimitive gmReflectionRatioReal)

private theorem gmCutoffPhase_eq_mellinIntegral
    (cutoff : GMSmoothCutoff) (t q : ℝ) {v : ℝ}
    (hv : 0 < v) (hq : 0 < q) :
    (cutoff (v / q) : ℂ) ^ 2 *
        Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ, gmMellinReflectionIntegrand cutoff t q v r := by
  pm_5440 hratio v q hv hq
  rw [gmCutoffSq_eq_verticalMellinIntegral cutoff hratio]
  pm_7017
  unfold gmMellinReflectionIntegrand gmCutoffMellin
  pm_4851 hratio.ne' hratio.le
  have hExpLog : Complex.exp ((Real.log (v / q) : ℝ) : ℂ) = (v / q : ℝ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hratio]
  have hRatioInv : (((v / q : ℝ) : ℂ))⁻¹ = (q : ℂ) * (v : ℂ)⁻¹ := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  have hRatioInvC : ((v : ℂ) / (q : ℂ))⁻¹ = (q : ℂ) * (v : ℂ)⁻¹ := by
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  pm_4865
  rw [hRatioInv]
  rw [hRatioInvC]

/-- Exact Mellin-reflection identity for the cutoff-weighted common
interval.  This is the Fubini step in Guth--Maynard Lemma 6.2. -/
theorem gmRescaledCutoffIntegral_eq_mellinReflection
    (cutoff : GMSmoothCutoff) (t : ℝ) {N m M : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    (∫ v in (N : ℝ)..(2 * N * M : ℝ),
        (cutoff (v / (N * m)) : ℂ) ^ 2 *
          Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          ((N * m : ℕ) : ℂ) *
            ((N * m : ℕ) : ℂ) ^ (((r : ℂ) * I)) *
              gmCutoffMellin cutoff r *
                gmReflectionIntegral (t - r) N (2 * N * M) := by
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    pm_4863
    pm_4864
    nlinarith
  pm_4863
  pm_4867
  calc
    (∫ v in (N : ℝ)..(2 * N * M : ℝ),
        (cutoff (v / (N * m)) : ℂ) ^ 2 *
          Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) =
      ∫ v in (N : ℝ)..(2 * N * M : ℝ),
        (1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ, gmMellinReflectionIntegrand cutoff t (N * m) v r := by
        apply intervalIntegral.integral_congr
        intro v hv
        have hvPos : 0 < v := hNReal.trans_le
          ((Set.uIcc_of_le hAB ▸ hv).1)
        exact gmCutoffPhase_eq_mellinIntegral cutoff t (N * m) hvPos hqReal
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ v in (N : ℝ)..(2 * N * M : ℝ),
          ∫ r : ℝ, gmMellinReflectionIntegrand cutoff t (N * m) v r := by
        rw [intervalIntegral.integral_smul]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ, ∫ v in (N : ℝ)..(2 * N * M : ℝ),
          gmMellinReflectionIntegrand cutoff t (N * m) v r := by
        rw [MeasureTheory.intervalIntegral_integral_swap
          (integrable_gmMellinReflectionIntegrand cutoff t hN hm hmM)]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          ((N * m : ℕ) : ℂ) *
            ((N * m : ℕ) : ℂ) ^ (((r : ℂ) * I)) *
              gmCutoffMellin cutoff r *
                gmReflectionIntegral (t - r) N (2 * N * M) := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with r
        pm_4866

theorem hasDerivAt_gmReflectionPrimitive {tau v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (gmReflectionPrimitive tau)
      (((tau / v - 2 * Real.pi : ℝ) : ℂ) *
        Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) v := by
  have hReal : HasDerivAt
      (fun x : ℝ => tau * Real.log x - 2 * Real.pi * x)
      (tau / v - 2 * Real.pi) v := by
    convert (Real.hasDerivAt_log hv).const_mul tau |>.fun_sub
      ((hasDerivAt_id v).const_mul (2 * Real.pi)) using 1
    all_goals simp only [div_eq_mul_inv, mul_one, id_eq]
  pm_1432
  · funext y
    rfl
  · field_simp [Complex.I_ne_zero]

section
variable {tau v : ℝ} (hv : tau - 2 * Real.pi * v ≠ 0)
include tau v hv
theorem hasDerivAt_gmReflectionRatio :
    HasDerivAt (gmReflectionRatio tau)
      (((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ)) v := by
  pm_4868
  pm_950
  · push_cast
    field_simp

theorem hasDerivAt_gmReflectionRatioReal :
    HasDerivAt (gmReflectionRatioReal tau)
      (2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2) v := by
  pm_4868
  pm_828
end

/-- Global logarithmic majorant for the reflection integral.  This is the
nonoscillatory estimate used only on the omitted Mellin range in Lemma 6.2. -/
theorem norm_gmReflectionIntegral_le_log {tau a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ‖gmReflectionIntegral tau a b‖ ≤ Real.log (b / a) := by
  unfold gmReflectionIntegral
  have hb : 0 < b := ha.trans_le hab
  have hInv : IntervalIntegrable (fun v : ℝ => v⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    pm_445 continuousOn_inv₀.mono v hv Set.uIcc_of_le hab
    exact ne_of_gt (ha.trans_le hv.1)
  calc
    ‖∫ v in a..b,
        (v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))‖ ≤
        ∫ v in a..b, v⁻¹ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab _ hInv
      filter_upwards with v hv
      have hvPos : 0 < v := ha.trans (Set.mem_Ioc.mp hv).1
      rw [norm_gmReflectionIntegrand hvPos]
    _ = Real.log (b / a) := integral_inv_of_pos ha hb

/-- Pointwise identification of the inner Fubini integral used in the Mellin
reflection formula.  Naming this equality is essential for retaining the
finite Dirichlet polynomial inside the outer Mellin integral. -/
private theorem intervalIntegral_gmMellinReflectionIntegrand_eq
    (cutoff : GMSmoothCutoff) (t r : ℝ) {N m M : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    (∫ v in (N : ℝ)..(2 * N * M : ℝ),
        gmMellinReflectionIntegrand cutoff t (N * m) v r) =
      ((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
        gmCutoffMellin cutoff r *
          gmReflectionIntegral (t - r) N (2 * N * M) := by
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    pm_4863
    pm_4864
    nlinarith
  pm_4863
  pm_4867
  pm_4866

/-- Uniform first/second-derivative estimate for the common reflection
integral.  This is the `T₀⁻¹/²` analytic core of Guth--Maynard Lemma 6.2. -/
theorem norm_gmReflectionIntegral_le_ten_div_sqrt {tau A B : ℝ}
    (htau : 1 ≤ tau) (hA : 0 < A) (hAB : A ≤ B) :
    ‖gmReflectionIntegral tau A B‖ ≤ 10 / Real.sqrt tau := by
  pm_5316 x0 tau Real.pi
  let delta : ℝ := Real.sqrt tau / (4 * Real.pi)
  let L : ℝ := x0 - delta
  let R : ℝ := x0 + delta
  have htauPos : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  pm_4891 hsqrtPos tau htauPos
  pm_7878 hsqrtSq tau htauPos.le
  have hsqrtLe : Real.sqrt tau ≤ tau := by
    nlinarith [Real.sqrt_nonneg tau]
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    positivity
  have hLR : L < R := by dsimp only [L, R]; linarith
  have hLFormula : L = (2 * tau - Real.sqrt tau) / (4 * Real.pi) := by
    pm_5507 L
  have hLLower : tau / (4 * Real.pi) ≤ L := by
    rw [hLFormula]
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 4 * Real.pi)).2
    linarith
  have hLPos : 0 < L := (div_pos htauPos (by positivity)).trans_le hLLower
  have hLeftDen : tau - 2 * Real.pi * L = Real.sqrt tau / 2 := by
    pm_5507 L
  have hRightDen : 2 * Real.pi * R - tau = Real.sqrt tau / 2 := by
    pm_5507 R
  by_cases hEntireLeft : B ≤ L
  · have hDenPos : 0 < tau - 2 * Real.pi * B := by
      pm_4870 hScaled hEntireLeft
      nlinarith [hLeftDen, hsqrtPos]
    pm_6375 hLeft norm_gmReflectionIntegral_le_left
    calc
      ‖gmReflectionIntegral tau A B‖ ≤ 2 / (tau - 2 * Real.pi * B) := hLeft
      _ ≤ 4 / Real.sqrt tau := by
        have hDen : Real.sqrt tau / 2 ≤ tau - 2 * Real.pi * B := by
          pm_7662 hLeftDen hEntireLeft
        apply (div_le_div_iff₀ hDenPos hsqrtPos).2
        nlinarith
      _ ≤ 10 / Real.sqrt tau := by
        exact div_le_div_of_nonneg_right (by norm_num) hsqrtPos.le
  by_cases hEntireRight : R ≤ A
  · have hDenPos : 0 < 2 * Real.pi * A - tau := by
      pm_4870 hScaled hEntireRight
      nlinarith [hRightDen, hsqrtPos]
    pm_6375 hRight norm_gmReflectionIntegral_le_right
    calc
      ‖gmReflectionIntegral tau A B‖ ≤ 2 / (2 * Real.pi * A - tau) := hRight
      _ ≤ 4 / Real.sqrt tau := by
        have hDen : Real.sqrt tau / 2 ≤ 2 * Real.pi * A - tau := by
          pm_7662 hRightDen hEntireRight
        apply (div_le_div_iff₀ hDenPos hsqrtPos).2
        nlinarith
      _ ≤ 10 / Real.sqrt tau := by
        exact div_le_div_of_nonneg_right (by norm_num) hsqrtPos.le
  · have hLB : L < B := lt_of_not_ge hEntireLeft
    pm_4869
    have hLeftPiece : ‖gmReflectionIntegral tau A l‖ ≤
        4 / Real.sqrt tau := by
      pm_5116 l A gmReflectionIntegral
      · have hAL : A < L := by
          pm_5041 L A hLA max_eq_left
        have hlEq : l = L := max_eq_right hAL.le
        rw [hlEq]
        have hBound := norm_gmReflectionIntegral_le_left hAL.le hA (by
          rw [← sub_pos, hLeftDen]
          positivity)
        pm_5392 hLeftDen A L
    have hRightPiece : ‖gmReflectionIntegral tau r B‖ ≤
        4 / Real.sqrt tau := by
      pm_5116 r B gmReflectionIntegral
      · have hRB : R < B := by
          pm_5041 B R hBR min_eq_left
        have hrEq : r = R := min_eq_right hRB.le
        rw [hrEq]
        have hBound := norm_gmReflectionIntegral_le_right hRB.le
          (hLPos.trans hLR) (by
          rw [← sub_pos, hRightDen]
          positivity)
        pm_5392 hRightDen R B
    have hMiddlePiece : ‖gmReflectionIntegral tau l r‖ ≤
        2 / Real.sqrt tau := by
      have hTauLowerL : tau / (4 * Real.pi) ≤ l :=
        hLLower.trans (le_max_right _ _)
      have hLength : r - l ≤ Real.sqrt tau / (2 * Real.pi) := by
        have hlL : L ≤ l := le_max_right _ _
        have hrR : r ≤ R := min_le_right _ _
        have hRL : R - L = Real.sqrt tau / (2 * Real.pi) := by
          dsimp only [R, L, delta]
          ring
        linarith
      have hTrivial := norm_gmReflectionIntegral_le_length_div (tau := tau) hlr
        (div_pos htauPos (by positivity : 0 < 4 * Real.pi)) hTauLowerL
      calc
        ‖gmReflectionIntegral tau l r‖ ≤
            (r - l) / (tau / (4 * Real.pi)) := hTrivial
        _ ≤ (Real.sqrt tau / (2 * Real.pi)) /
            (tau / (4 * Real.pi)) := by
          gcongr
        _ = 2 / Real.sqrt tau := by
          field_simp [Real.pi_ne_zero, hsqrtPos.ne', htauPos.ne']
          nlinarith
    have hIntAl := intervalIntegrable_gmReflectionIntegrand (tau := tau) hAl hA
    have hIntlR := intervalIntegrable_gmReflectionIntegrand (tau := tau) hlr hlPos
    have hIntrB := intervalIntegrable_gmReflectionIntegrand (tau := tau) hrB hrPos
    have hSplit : gmReflectionIntegral tau A B =
        gmReflectionIntegral tau A l + gmReflectionIntegral tau l r +
          gmReflectionIntegral tau r B := by
      unfold gmReflectionIntegral
      pm_6313
    rw [hSplit]
    calc
      ‖gmReflectionIntegral tau A l + gmReflectionIntegral tau l r +
          gmReflectionIntegral tau r B‖ ≤
          ‖gmReflectionIntegral tau A l‖ + ‖gmReflectionIntegral tau l r‖ +
            ‖gmReflectionIntegral tau r B‖ := by
        pm_395 norm_add_le
      _ ≤ 4 / Real.sqrt tau + 2 / Real.sqrt tau + 4 / Real.sqrt tau := by
        gcongr
      _ = 10 / Real.sqrt tau := by ring

/-- A bounded-variation amplitude may be inserted into the logarithmic
reflection integral without losing the square-root cancellation.  This is
the weighted van der Corput estimate needed by the Type-I B-process: the
coefficient is the bare `10 / sqrt tau` bound multiplied by the endpoint value
and total variation of the amplitude.

The statement is deliberately quantitative.  It does not package a desired
reflection conclusion as a hypothesis; `w'` is the actual derivative of the
concrete amplitude and the right side is its literal interval integral. -/
theorem norm_weighted_gmReflectionIntegral_le
    {tau A B : ℝ} (htau : 1 ≤ tau) (hA : 0 < A) (hAB : A ≤ B)
    (w w' : ℝ → ℂ)
    (hw : ∀ x ∈ Set.Icc A B, HasDerivAt w (w' x) x)
    (hw' : IntervalIntegrable w' volume A B) :
    ‖∫ v in A..B, w v *
        ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))‖ ≤
      (10 / Real.sqrt tau) *
        (‖w B‖ + ∫ v in A..B, ‖w' v‖) := by
  pm_4873 I
  have hkInt : IntervalIntegrable k volume A B := by
    simpa only [k] using intervalIntegrable_gmReflectionIntegrand hAB hA
  pm_4871
  have hFDeriv : ∀ x ∈ Set.Icc A B, HasDerivAt F (k x) x := by
    intro x hx
    have hkAx : IntervalIntegrable k volume A x := by
      simpa only [k] using
        intervalIntegrable_gmReflectionIntegrand hx.1 hA
    pm_6524
  pm_4872
  have hFB : F B = gmReflectionIntegral tau A B := by
    rfl
  have hFBound : ∀ x ∈ Set.Icc A B, ‖F x‖ ≤ 10 / Real.sqrt tau := by
    intro x hx
    simpa only [F, k, gmReflectionIntegral] using
      norm_gmReflectionIntegral_le_ten_div_sqrt htau hA hx.1
  have hvariationNonneg : 0 ≤ ∫ v in A..B, ‖w' v‖ := by
    exact intervalIntegral.integral_nonneg hAB fun _ _ => norm_nonneg _
  have hweightedVariation :
      ‖∫ v in A..B, w' v * F v‖ ≤
        (10 / Real.sqrt tau) * ∫ v in A..B, ‖w' v‖ := by
    calc
      ‖∫ v in A..B, w' v * F v‖ ≤
          |∫ v in A..B, ‖w' v * F v‖| :=
        intervalIntegral.norm_integral_le_abs_integral_norm
      _ = ∫ v in A..B, ‖w' v * F v‖ := by
        pm_7562
      _ ≤ ∫ v in A..B, ‖w' v‖ * (10 / Real.sqrt tau) := by
        pm_7288
        · exact hw'.norm.mul_const (10 / Real.sqrt tau)
        pm_5719 v hv hFBound
      _ = (10 / Real.sqrt tau) * ∫ v in A..B, ‖w' v‖ := by
        rw [intervalIntegral.integral_mul_const]
        ring
  rw [hparts, hFA, hFB]
  simp only [mul_zero, sub_zero]
  calc
    ‖w B * gmReflectionIntegral tau A B - ∫ v in A..B, w' v * F v‖ ≤
        ‖w B * gmReflectionIntegral tau A B‖ +
          ‖∫ v in A..B, w' v * F v‖ := norm_sub_le _ _
    _ ≤ ‖w B‖ * (10 / Real.sqrt tau) +
          (10 / Real.sqrt tau) * ∫ v in A..B, ‖w' v‖ := by
      gcongr
      rw [norm_mul]
      gcongr
      exact norm_gmReflectionIntegral_le_ten_div_sqrt htau hA hAB
    _ = (10 / Real.sqrt tau) *
          (‖w B‖ + ∫ v in A..B, ‖w' v‖) := by ring

/-- The real power amplitude occurring after Mellin reflection.  Writing it
as an exponential keeps the derivative and its parameter dependence
literal, including at nonintegral `sigma`. -/
noncomputable def gmReflectionPowerWeight (sigma v : ℝ) : ℂ :=
  Complex.exp (((-sigma * Real.log v : ℝ) : ℂ))

section
variable {sigma v : ℝ} (hv : 0 < v)
include sigma v hv
theorem hasDerivAt_gmReflectionPowerWeight :
    HasDerivAt (gmReflectionPowerWeight sigma)
      (((-sigma / v : ℝ) : ℂ) * gmReflectionPowerWeight sigma v) v := by
  unfold gmReflectionPowerWeight
  have hReal : HasDerivAt (fun x : ℝ => -sigma * Real.log x) (-sigma / v) v := by
    simpa only [div_eq_mul_inv] using
      (Real.hasDerivAt_log hv.ne').const_mul (-sigma)
  convert hReal.ofReal_comp.cexp using 1
  all_goals ring

theorem norm_gmReflectionPowerWeight :
    ‖gmReflectionPowerWeight sigma v‖ = v ^ (-sigma) := by
  unfold gmReflectionPowerWeight
  rw [Complex.norm_exp]
  simp only [ofReal_re]
  rw [Real.rpow_def_of_pos hv]
  congr 1
  ring
end

/-- Weighted logarithmic B-process estimate for the exact power amplitude.
The variation integral is left visible: downstream scale arithmetic may use
either its exact antiderivative or a sharper restricted-window estimate. -/
theorem norm_powerWeighted_gmReflectionIntegral_le
    {tau sigma A B : ℝ} (htau : 1 ≤ tau) (hA : 0 < A) (hAB : A ≤ B) :
    ‖∫ v in A..B, gmReflectionPowerWeight sigma v *
        ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))‖ ≤
      (10 / Real.sqrt tau) *
        (B ^ (-sigma) +
          ∫ v in A..B,
            ‖(((-sigma / v : ℝ) : ℂ) *
              gmReflectionPowerWeight sigma v)‖) := by
  let w' : ℝ → ℂ := fun v =>
    (((-sigma / v : ℝ) : ℂ) * gmReflectionPowerWeight sigma v)
  have hw : ∀ x ∈ Set.Icc A B,
      HasDerivAt (gmReflectionPowerWeight sigma) (w' x) x := by
    intro x hx
    exact hasDerivAt_gmReflectionPowerWeight (hA.trans_le hx.1)
  have hw' : IntervalIntegrable w' volume A B := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    pm_4874
    exact (Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div continuousAt_id hxPos.ne')).mul
      (hasDerivAt_gmReflectionPowerWeight hxPos).continuousAt
  have hBase := norm_weighted_gmReflectionIntegral_le htau hA hAB
    (gmReflectionPowerWeight sigma) w' hw hw'
  simpa only [w', norm_gmReflectionPowerWeight (hA.trans_le hAB)] using hBase

theorem star_gmReflectionPowerWeight (sigma v : ℝ) :
    star (gmReflectionPowerWeight sigma v) =
      gmReflectionPowerWeight sigma v := by
  unfold gmReflectionPowerWeight
  rw [Complex.star_def, ← Complex.exp_conj]
  simp

/-- Conjugated form of the power-weighted B-process estimate.  This is the
Fourier sign produced by the medium Type-I block. -/
theorem norm_conj_powerWeighted_gmReflectionIntegral_le
    {tau sigma A B : ℝ} (htau : 1 ≤ tau) (hA : 0 < A) (hAB : A ≤ B) :
    ‖∫ v in A..B, gmReflectionPowerWeight sigma v *
        star ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))‖ ≤
      (10 / Real.sqrt tau) *
        (B ^ (-sigma) +
          ∫ v in A..B,
            ‖(((-sigma / v : ℝ) : ℂ) *
              gmReflectionPowerWeight sigma v)‖) := by
  let f : ℝ → ℂ := fun v =>
    gmReflectionPowerWeight sigma v *
      ((v : ℂ)⁻¹ * Complex.exp
        ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))
  have hfInt : IntervalIntegrable f volume A B := by
    pm_4875
    exact (hasDerivAt_gmReflectionPowerWeight hvPos).continuousAt.mul
      ((Complex.continuous_ofReal.continuousAt.comp continuousAt_id).inv₀
          (Complex.ofReal_ne_zero.mpr hvPos.ne') |>.mul
        ((Complex.continuous_ofReal.continuousAt.comp hPhase).mul
          continuousAt_const).cexp)
  have hConj := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hfInt
  have hPointwise : (fun v : ℝ => star (f v)) = fun v =>
      gmReflectionPowerWeight sigma v *
        star ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by
    funext v
    dsimp only [f]
    rw [Complex.star_def, map_mul]
    pm_126 hs star_gmReflectionPowerWeight sigma v Complex.star_def
    rw [hs]
  have hConj' : (∫ v in A..B, star (f v)) =
      star (∫ v in A..B, f v) := by
    convert hConj using 1 <;> rfl
  rw [← hPointwise, hConj']
  rw [Complex.star_def, Complex.norm_conj]
  exact norm_powerWeighted_gmReflectionIntegral_le htau hA hAB

section
variable (cutoff : GMSmoothCutoff)
include cutoff
/-- Positive Fourier modes may be integrated over the common source interval
`[1/m, 2M/m]`.  Its endpoints were chosen so that the support `[1,2]` is
contained in the interval for every `1 ≤ m ≤ M`. -/
theorem gmTraceFourier_pos_eq_interval
    (t N : ℝ) {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    gmTraceFourier cutoff t (N * m) =
      ∫ u in (1 : ℝ) / m..(2 : ℝ) * M / m,
        Complex.exp (((-2 * Real.pi * (u * (N * m)) : ℝ) : ℂ) * I) *
          gmTraceKernel cutoff t u := by
  rw [gmTraceFourier, SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [Real.inner_apply, gmTraceKernelSchwartz_apply]
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro u hu
  have hcut : cutoff u ≠ 0 := by
    intro hzero
    apply hu
    simp [gmTraceKernel, hzero]
  have huRange := cutoff.support hcut
  rw [Set.mem_Ioc]
  constructor
  · have hmPos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    pm_77 hmOne m hm
    have hInv : (1 : ℝ) / m ≤ 1 := by
      rw [div_le_one hmPos]
      exact hmOne
    rcases hInv.eq_or_lt with hEq | hLt
    · have hmEq : m = 1 := by
        norm_num [div_eq_iff (ne_of_gt hmPos)] at hEq
        exact_mod_cast hEq
      subst m
      simp only [Nat.cast_one, div_one]
      exact lt_of_le_of_ne huRange.1 fun huEq =>
        hcut (huEq ▸ gmSmoothCutoff_eq_zero_at_one cutoff)
    · exact hLt.trans_le huRange.1
  · have hmPos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    pm_106 hmMReal m M hmM
    apply huRange.2.trans
    rw [le_div_iff₀ hmPos]
    nlinarith

/-- Exact source rescaling of a positive Fourier coefficient.  The phase
factor `(mN)^(-it)` contains the logarithmic dependence on the mode outside
the common integral `[N,2NM]`; the remaining occurrence of the mode is only
in the smooth cutoff. -/
theorem gmTraceFourier_pos_rescale
    (t : ℝ) {N m M : ℕ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    gmTraceFourier cutoff t ((N : ℝ) * m) =
      ((N * m : ℕ) : ℂ)⁻¹ *
        ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
        ∫ v in (N : ℝ)..(2 * N * M : ℝ),
          (cutoff (v / (N * m)) : ℂ) ^ 2 *
            Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) := by
  rw [gmTraceFourier_pos_eq_interval cutoff t (N : ℝ) hm hmM]
  have hNmNat : 0 < N * m := Nat.mul_pos hN (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hNm : (0 : ℝ) < N * m := by exact_mod_cast hNmNat
  let f : ℝ → ℂ := fun u =>
    Complex.exp (((-2 * Real.pi * (u * ((N : ℝ) * m)) : ℝ) : ℂ) * I) *
      gmTraceKernel cutoff t u
  have hChange := intervalIntegral.integral_comp_div_add
    (f := fun u : ℝ =>
      Complex.exp (((-2 * Real.pi * (u * ((N : ℝ) * m)) : ℝ) : ℂ) * I) *
        gmTraceKernel cutoff t u)
    (a := (N : ℝ)) (b := (2 * N * M : ℝ)) hNm.ne' 0
  simp only [add_zero] at hChange
  have hLower : (N : ℝ) / (N * m) = (1 : ℝ) / m := by field_simp
  have hUpper : (2 * N * M : ℝ) / (N * m) = (2 : ℝ) * M / m := by
    field_simp
  rw [hLower, hUpper, Complex.real_smul] at hChange
  have hSolve :
      (∫ u in (1 : ℝ) / m..(2 : ℝ) * M / m,
          Complex.exp (((-2 * Real.pi * (u * ((N : ℝ) * m)) : ℝ) : ℂ) * I) *
            gmTraceKernel cutoff t u) =
        (((N * m : ℕ) : ℂ))⁻¹ *
          ∫ v in (N : ℝ)..(2 * N * M : ℝ),
            Complex.exp (((-2 * Real.pi * ((v / ((N : ℝ) * m)) *
              ((N : ℝ) * m)) : ℝ) : ℂ) * I) *
              gmTraceKernel cutoff t (v / ((N : ℝ) * m)) := by
    apply (eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hNmNat.ne')).2
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Complex.ofReal_natCast,
      Complex.ofReal_mul] using hChange.symm
  have hIntegralFactor :
      (∫ v in (N : ℝ)..(2 * N * M : ℝ),
          Complex.exp (((-2 * Real.pi * ((v / ((N : ℝ) * m)) *
            ((N : ℝ) * m)) : ℝ) : ℂ) * I) *
            gmTraceKernel cutoff t (v / ((N : ℝ) * m))) =
        ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
          ∫ v in (N : ℝ)..(2 * N * M : ℝ),
            (cutoff (v / (N * m)) : ℂ) ^ 2 *
              Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    have hvPos : 0 < v := by
      pm_4863
      have hNUpper : (N : ℝ) ≤ 2 * N * M := by
        pm_4864
        nlinarith [mul_nonneg hNReal.le (sub_nonneg.mpr hMReal)]
      exact hNReal.trans_le
        (Set.uIcc_of_le hNUpper ▸ hv).1
    have hNmComplex : ((((N : ℝ) * m : ℝ) : ℂ)) = ((N * m : ℕ) : ℂ) := by
      norm_num
    pm_7663 hNmComplexNe hNmNat.ne'
    unfold gmTraceKernel
    have hLogDiv : Real.log (v / ((N : ℝ) * m)) =
        Real.log v - Real.log ((N : ℝ) * m) := Real.log_div hvPos.ne' hNm.ne'
    have hCpow : ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) =
        Complex.exp (-((t : ℂ) * I) * Complex.log ((N * m : ℕ) : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero hNmComplexNe]
      congr 1
      ring
    have hCancel : v / ((N : ℝ) * m) * ((N : ℝ) * m) = v := by
      exact div_mul_cancel₀ v hNm.ne'
    change
      Complex.exp (((-2 * Real.pi *
          ((v / ((N : ℝ) * m)) * ((N : ℝ) * m)) : ℝ) : ℂ) * I) *
          ((cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 *
            Complex.exp ((((t * Real.log (v / ((N : ℝ) * m)) : ℝ) : ℂ) * I))) =
        ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
          ((cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 *
            Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))
    rw [hCancel, hCpow, hLogDiv]
    rw [← hNmComplex]
    rw [← Complex.ofReal_log hNm.le]
    let A : ℂ := ((-2 * Real.pi * v : ℝ) : ℂ) * I
    let B : ℂ := ((t * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I
    let C : ℂ := -((t : ℂ) * I) * (Real.log ((N : ℝ) * m) : ℂ)
    let D : ℂ := ((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I
    change Complex.exp A *
        ((cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 * Complex.exp B) =
      Complex.exp C *
        ((cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 * Complex.exp D)
    calc
      Complex.exp A *
          ((cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 * Complex.exp B) =
          (cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 *
            (Complex.exp A * Complex.exp B) := by ring
      _ = (cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 * Complex.exp (A + B) := by
        rw [Complex.exp_add]
      _ = (cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 * Complex.exp (C + D) := by
        congr 2
        dsimp only [A, B, C, D]
        push_cast
        ring
      _ = (cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 *
          (Complex.exp C * Complex.exp D) := by rw [Complex.exp_add]
      _ = Complex.exp C *
          ((cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 * Complex.exp D) := by ring
  rw [hSolve, hIntegralFactor]
  ring

/-- Exact positive-mode form of Guth--Maynard smooth reflection.  All
dependence on the Fourier mode is outside the common oscillatory integral. -/
theorem gmTraceFourier_pos_eq_mellinReflection
    (t : ℝ) {N m M : ℕ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    gmTraceFourier cutoff t ((N : ℝ) * m) =
      ((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
        ((1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ,
            ((N * m : ℕ) : ℂ) *
              ((N * m : ℕ) : ℂ) ^ (((r : ℂ) * I)) *
                gmCutoffMellin cutoff r *
                  gmReflectionIntegral (t - r) N (2 * N * M)) := by
  rw [gmTraceFourier_pos_rescale cutoff t hN hm hmM]
  rw [gmRescaledCutoffIntegral_eq_mellinReflection cutoff t hN hm hmM]
end

/-- One positive reflected mode before summing over the Fourier frequency.
The normalization is arranged so that the natural-number scale cancels
inside the aggregate sum. -/
noncomputable def gmPositiveDualModeIntegrand (cutoff : GMSmoothCutoff)
    (t : ℝ) (N M m : ℕ) (r : ℝ) : ℂ :=
  ((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
    ((1 / (2 * Real.pi) : ℝ) •
      (((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
        gmCutoffMellin cutoff r *
          gmReflectionIntegral (t - r) N (2 * N * M)))

/-- The common finite Dirichlet polynomial retained inside the Mellin
integral.  This is the cancellation-bearing object missing from a
mode-by-mode triangle inequality. -/
noncomputable def gmPositiveDualDirichletPoly
    (t : ℝ) (N M : ℕ) (r : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    ((N * m : ℕ) : ℂ) ^ ((((r - t : ℝ) : ℂ) * I))

/-- The coefficient-one Dirichlet polynomial in Guth--Maynard Lemma 6.2. -/
noncomputable def gmReflectionDirichletPoly
    (t : ℝ) (M : ℕ) (u : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    (m : ℂ) ^ (-((((t + u : ℝ) : ℂ) * I)))

section
variable (t r : ℝ) {N M : ℕ} (hN : 0 < N)
include t r N M hN
/-- Factoring the common physical scale out of the reflected polynomial.
The equality is exact; no coefficient or cardinality estimate is used. -/
theorem gmPositiveDualDirichletPoly_eq_scale_mul :
    gmPositiveDualDirichletPoly t N M r =
      (N : ℂ) ^ ((((r - t : ℝ) : ℂ) * I)) *
        gmReflectionDirichletPoly t M (-r) := by
  rw [gmPositiveDualDirichletPoly, gmReflectionDirichletPoly,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1
  have hExp : -((((t + -r : ℝ) : ℂ) * I)) =
      (((r - t : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [hExp]
  have hNr : 0 ≤ (N : ℝ) := by positivity
  have hmr : 0 ≤ (m : ℝ) := by positivity
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Complex.ofReal_natCast] using
    (Complex.mul_cpow_ofReal_nonneg hNr hmr
      ((((r - t : ℝ) : ℂ) * I)))

/-- The common scale has unit modulus, so the exact source polynomial and
the reflected physical polynomial have equal norms. -/
theorem norm_gmPositiveDualDirichletPoly_eq :
    ‖gmPositiveDualDirichletPoly t N M r‖ =
      ‖gmReflectionDirichletPoly t M (-r)‖ := by
  rw [gmPositiveDualDirichletPoly_eq_scale_mul t r hN, norm_mul]
  have hScale : ‖(N : ℂ) ^ ((((r - t : ℝ) : ℂ) * I))‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hN]
    simp
  rw [hScale, one_mul]
end

/-- Conjugating the coefficient-one polynomial changes both signs and
therefore preserves its norm. -/
theorem norm_gmReflectionDirichletPoly_neg_time
    (t u : ℝ) (M : ℕ) :
    ‖gmReflectionDirichletPoly (-t) M u‖ =
      ‖gmReflectionDirichletPoly t M (-u)‖ := by
  have hstar : gmReflectionDirichletPoly (-t) M u =
      star (gmReflectionDirichletPoly t M (-u)) := by
    rw [gmReflectionDirichletPoly, gmReflectionDirichletPoly, star_sum]
    apply Finset.sum_congr rfl
    intro m hm
    let z : ℂ := -((((t + -u : ℝ) : ℂ) * I))
    have hmArg : Complex.arg (m : ℂ) ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    have hExp : -((((-t + u : ℝ) : ℂ) * I)) = star z := by
      dsimp only [z]
      pm_188 Complex.star_def map_neg map_mul Complex.conj_ofReal Complex.conj_I
      push_cast
      ring
    rw [hExp]
    simpa [z, Complex.star_def] using Complex.cpow_conj (m : ℂ) z hmArg
  rw [hstar, norm_star]

/-- The retained dual polynomial has the elementary cardinality bound.  The
quantitative reflection theorem keeps the polynomial itself on the core
Mellin range and uses this estimate only on the omitted tail. -/
theorem norm_gmPositiveDualDirichletPoly_le
    (t : ℝ) {N M : ℕ} (hN : 0 < N) (r : ℝ) :
    ‖gmPositiveDualDirichletPoly t N M r‖ ≤ M := by
  rw [gmPositiveDualDirichletPoly]
  calc
    ‖∑ m ∈ Finset.Icc 1 M,
        ((N * m : ℕ) : ℂ) ^ ((((r - t : ℝ) : ℂ) * I))‖ ≤
        ∑ m ∈ Finset.Icc 1 M,
          ‖((N * m : ℕ) : ℂ) ^ ((((r - t : ℝ) : ℂ) * I))‖ :=
      norm_sum_le _ _
    _ = ∑ _m ∈ Finset.Icc 1 M, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmPos : 0 < N * m :=
        Nat.mul_pos hN (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1)
      rw [Complex.norm_natCast_cpow_of_pos hmPos]
      simp
    _ = M := by simp

section
variable {t r T₀ A B : ℝ} (hT₀ : 4 ≤ T₀) (ht : T₀ ≤ t) (hr : |r| ≤ T₀ / 2) (hA : 0 < A) (hAB : A ≤ B)
include t r T₀ A B hT₀ ht hr hA hAB
/-- Uniform `T₀⁻¹ᐟ²` stationary bound on the core Mellin window for the
positive reflected phase. -/
theorem norm_gmReflectionIntegral_pos_core_le :
    ‖gmReflectionIntegral (t - r) A B‖ ≤
      10 / Real.sqrt (T₀ / 2) := by
  have hrUpper : r ≤ T₀ / 2 := le_trans (le_abs_self r) hr
  have hTau : 1 ≤ t - r := by linarith
  have hBase := norm_gmReflectionIntegral_le_ten_div_sqrt
    hTau hA hAB
  have hSqrt : Real.sqrt (T₀ / 2) ≤ Real.sqrt (t - r) := by
    exact Real.sqrt_le_sqrt (by linarith)
  exact hBase.trans (div_le_div_of_nonneg_left (by norm_num)
    (Real.sqrt_pos.2 (by linarith)) hSqrt)

/-- The opposite signed phase is nonstationary on the same core window and
obeys the same (deliberately loose) `T₀⁻¹ᐟ²` majorant. -/
theorem norm_gmReflectionIntegral_neg_core_le :
    ‖gmReflectionIntegral (-t - r) A B‖ ≤
      10 / Real.sqrt (T₀ / 2) := by
  have hrLower : -(T₀ / 2) ≤ r := by
    exact (neg_le_neg hr).trans (neg_abs_le r)
  have hPhase : -t - r < 2 * Real.pi * A := by
    nlinarith [Real.pi_pos]
  have hBase := norm_gmReflectionIntegral_le_right hAB hA hPhase
  have hDenom : T₀ / 2 ≤ 2 * Real.pi * A - (-t - r) := by
    nlinarith [Real.pi_pos]
  have hDenomPos : 0 < 2 * Real.pi * A - (-t - r) := by linarith
  have hT₀Pos : 0 < T₀ := by linarith
  have hFirst : 2 / (2 * Real.pi * A - (-t - r)) ≤ 4 / T₀ := by
    rw [div_le_iff₀ hDenomPos, div_eq_mul_inv]
    calc
      (2 : ℝ) ≤ (4 / T₀) * (T₀ / 2) := by
        field_simp
        norm_num
      _ ≤ (4 / T₀) * (2 * Real.pi * A - (-t - r)) := by
        gcongr
  have hSqrtPos : 0 < Real.sqrt (T₀ / 2) := Real.sqrt_pos.2 (by linarith)
  have hSquare : Real.sqrt (T₀ / 2) ^ 2 = T₀ / 2 := by
    rw [sq_sqrt (by linarith)]
  have hSecond : 4 / T₀ ≤ 10 / Real.sqrt (T₀ / 2) := by
    rw [div_le_div_iff₀ hT₀Pos hSqrtPos]
    nlinarith [hSquare, Real.sqrt_nonneg (T₀ / 2)]
  exact hBase.trans (hFirst.trans hSecond)
end

section
variable (cutoff : GMSmoothCutoff) (t : ℝ) {N m M : ℕ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M)
include cutoff t N m M hN hm hmM
theorem integrable_gmPositiveDualModeIntegrand :
    Integrable (gmPositiveDualModeIntegrand cutoff t N M m) := by
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    pm_4863
    pm_4864
    nlinarith
  have hProd := integrable_gmMellinReflectionIntegrand cutoff t hN hm hmM
  have hInner : Integrable (fun r : ℝ =>
      ∫ v in (N : ℝ)..(2 * N * M : ℝ),
        gmMellinReflectionIntegrand cutoff t (N * m) v r) := by
    simpa only [intervalIntegral.integral_of_le hAB, Set.uIoc_of_le hAB,
      Function.uncurry_apply_pair] using
      hProd.integral_prod_right
  have hSimplified : Integrable (fun r : ℝ =>
      ((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
        gmCutoffMellin cutoff r *
          gmReflectionIntegral (t - r) N (2 * N * M)) := by
    apply hInner.congr
    filter_upwards with r
    exact intervalIntegral_gmMellinReflectionIntegrand_eq
      cutoff t r hN hm hmM
  have hMul := hSimplified.const_mul
    (((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
      ((1 / (2 * Real.pi) : ℝ) : ℂ))
  convert hMul using 1
  funext r
  rw [gmPositiveDualModeIntegrand, Complex.real_smul]
  ring

/-- Each positive Fourier coefficient is the integral of its normalized
dual-mode integrand. -/
theorem gmTraceFourier_pos_eq_integral_dualMode :
    gmTraceFourier cutoff t ((N : ℝ) * m) =
      ∫ r : ℝ, gmPositiveDualModeIntegrand cutoff t N M m r := by
  rw [gmTraceFourier_pos_eq_mellinReflection cutoff t hN hm hmM]
  unfold gmPositiveDualModeIntegrand
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_smul]
end

/-- Exact aggregate positive-mode identity with the finite Dirichlet
polynomial kept inside the single Mellin integral. -/
theorem gmTraceFourier_pos_sum_eq_integral_dualPoly
    (cutoff : GMSmoothCutoff) (t : ℝ) {N M : ℕ} (hN : 0 < N) :
    (∑ m ∈ Finset.Icc 1 M, gmTraceFourier cutoff t ((N : ℝ) * m)) =
      ∫ r : ℝ, ∑ m ∈ Finset.Icc 1 M,
        gmPositiveDualModeIntegrand cutoff t N M m r := by
  calc
    (∑ m ∈ Finset.Icc 1 M, gmTraceFourier cutoff t ((N : ℝ) * m)) =
        ∑ m ∈ Finset.Icc 1 M,
          ∫ r : ℝ, gmPositiveDualModeIntegrand cutoff t N M m r := by
      apply Finset.sum_congr rfl
      pm_5355 gmTraceFourier_pos_eq_integral_dualMode
    _ = ∫ r : ℝ, ∑ m ∈ Finset.Icc 1 M,
        gmPositiveDualModeIntegrand cutoff t N M m r := by
      symm
      apply MeasureTheory.integral_finsetSum
      pm_5355 integrable_gmPositiveDualModeIntegrand

/-- Algebraic cancellation of the scale factors in the aggregate integrand.
The remaining finite sum is precisely one Dirichlet polynomial. -/
theorem sum_gmPositiveDualModeIntegrand_eq
    (cutoff : GMSmoothCutoff) (t r : ℝ) {N M : ℕ} (hN : 0 < N) :
    (∑ m ∈ Finset.Icc 1 M,
        gmPositiveDualModeIntegrand cutoff t N M m r) =
      (1 / (2 * Real.pi) : ℝ) •
        (gmCutoffMellin cutoff r *
          gmReflectionIntegral (t - r) N (2 * N * M) *
            gmPositiveDualDirichletPoly t N M r) := by
  rw [gmPositiveDualDirichletPoly]
  rw [Complex.real_smul]
  pm_1063 Finset.mul_sum m hm
  have hmPos : 0 < N * m := by
    exact Nat.mul_pos hN (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1)
  pm_7663 hq hmPos.ne'
  rw [gmPositiveDualModeIntegrand]
  have hpow :
      ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
          ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) =
        ((N * m : ℕ) : ℂ) ^ ((((r - t : ℝ) : ℂ) * I)) := by
    rw [← Complex.cpow_add _ _ hq]
    congr 2
    push_cast
    ring
  simp_rw [Complex.real_smul]
  have hqCancel : ((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ) = 1 :=
    inv_mul_cancel₀ hq
  calc
    ((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
              gmCutoffMellin cutoff r *
                gmReflectionIntegral (t - r) N (2 * N * M))) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ)) *
          (((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
            ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I)) *
          gmCutoffMellin cutoff r *
            gmReflectionIntegral (t - r) N (2 * N * M)) := by ring
    _ = (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (gmCutoffMellin cutoff r *
          gmReflectionIntegral (t - r) N (2 * N * M) *
            ((N * m : ℕ) : ℂ) ^ ((((r - t : ℝ) : ℂ) * I)))) := by
      rw [hqCancel, hpow]
      ring

section
variable (cutoff : GMSmoothCutoff) (t : ℝ) {N M : ℕ} (hN : 0 < N)
include cutoff t N M hN
/-- Integrability of the exact cancellation-preserving aggregate integrand.
This is the measurable input needed to split its Mellin integral into a core
and a complementary tail. -/
theorem integrable_norm_gmPositiveDualAggregate :
    Integrable (fun r : ℝ =>
      (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
          ‖gmPositiveDualDirichletPoly t N M r‖) := by
  have hsum : Integrable (fun r : ℝ =>
      ∑ m ∈ Finset.Icc 1 M,
        gmPositiveDualModeIntegrand cutoff t N M m r) := by
    apply integrable_finsetSum
    pm_5355 integrable_gmPositiveDualModeIntegrand
  have hnorm := hsum.norm
  apply hnorm.congr
  pm_4876

/-- Cancellation-preserving norm form of the positive half of Guth--Maynard
Lemma 6.2.  No factor equal to the number of Fourier modes is introduced. -/
theorem norm_gmTraceFourier_pos_sum_le_dualPoly :
    ‖∑ m ∈ Finset.Icc 1 M, gmTraceFourier cutoff t ((N : ℝ) * m)‖ ≤
      ∫ r : ℝ, (1 / (2 * Real.pi) : ℝ) *
        ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly t N M r‖ := by
  rw [gmTraceFourier_pos_sum_eq_integral_dualPoly cutoff t hN]
  calc
    ‖∫ r : ℝ, ∑ m ∈ Finset.Icc 1 M,
        gmPositiveDualModeIntegrand cutoff t N M m r‖ ≤
        ∫ r : ℝ, ‖∑ m ∈ Finset.Icc 1 M,
          gmPositiveDualModeIntegrand cutoff t N M m r‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ r : ℝ, (1 / (2 * Real.pi) : ℝ) *
        ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly t N M r‖ := by
      apply MeasureTheory.integral_congr_ae
      pm_4876

/-- The negative Fourier modes satisfy the conjugate cancellation-preserving
bound.  In particular, no factor equal to the number of modes is introduced
on the negative half either. -/
theorem norm_gmTraceFourier_neg_sum_le_dualPoly :
    ‖∑ m ∈ Finset.Icc 1 M,
        gmTraceFourier cutoff t (-((N : ℝ) * m))‖ ≤
      ∫ r : ℝ, (1 / (2 * Real.pi) : ℝ) *
        ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly (-t) N M r‖ := by
  have hsum :
      (∑ m ∈ Finset.Icc 1 M,
          gmTraceFourier cutoff t (-((N : ℝ) * m))) =
        star (∑ m ∈ Finset.Icc 1 M,
          gmTraceFourier cutoff (-t) ((N : ℝ) * m)) := by
    calc
      (∑ m ∈ Finset.Icc 1 M,
          gmTraceFourier cutoff t (-((N : ℝ) * m))) =
          ∑ m ∈ Finset.Icc 1 M,
            star (gmTraceFourier cutoff (-t) ((N : ℝ) * m)) := by
        apply Finset.sum_congr rfl
        intro m _
        exact gmTraceFourier_neg_eq_conj cutoff t ((N : ℝ) * m)
      _ = star (∑ m ∈ Finset.Icc 1 M,
          gmTraceFourier cutoff (-t) ((N : ℝ) * m)) := by simp
  rw [hsum, norm_star]
  exact norm_gmTraceFourier_pos_sum_le_dualPoly cutoff (-t) hN

/-- Cancellation-preserving estimate for the complete retained signed window.
This removes the spurious mode-cardinality loss from
`norm_gmSmoothReflection_native_le`.  The uniform `T₀⁻¹ᐟ²` extraction and the
summed omitted-frequency remainder required by the published Lemma 6.2 remain
separate obligations. -/
theorem norm_gmTraceFourier_signed_sum_le_dualPoly :
    ‖∑ m ∈ Finset.Icc 1 M,
        (gmTraceFourier cutoff t ((N : ℝ) * m) +
          gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ ≤
      (∫ r : ℝ, (1 / (2 * Real.pi) : ℝ) *
        ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly t N M r‖) +
      ∫ r : ℝ, (1 / (2 * Real.pi) : ℝ) *
        ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly (-t) N M r‖ := by
  rw [Finset.sum_add_distrib]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_gmTraceFourier_pos_sum_le_dualPoly cutoff t hN)
    (norm_gmTraceFourier_neg_sum_le_dualPoly cutoff t hN))
end

end GuthMaynard.NativeMoment
