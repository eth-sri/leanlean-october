module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import MathCollab.Density.Oscillatory
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import GuthMaynard.NativeSource.GuthMaynard.LargeValuesPoisson

@[expose] public section

open Complex MeasureTheory Real Set
open scoped ContDiff FourierTransform SchwartzMap

namespace GuthMaynard.NativeMoment
open MathCollab.Density (gmReflectionIntegral gmReflectionPrimitive gmReflectionRatio gmReflectionRatioReal hasDerivAt_gmReflectionPrimitive hasDerivAt_gmReflectionRatio hasDerivAt_gmReflectionRatioReal gmReflectionRatio_mul_primitiveDeriv gmReflectionIntegral_eq_parts norm_gmReflectionPrimitive norm_gmReflectionRatio norm_gmReflectionIntegrand norm_gmReflectionIntegral_le_endpoint_variation norm_gmReflectionIntegral_le_left norm_gmReflectionIntegral_le_right norm_gmReflectionIntegral_le_length_div intervalIntegrable_gmReflectionIntegrand)

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

@[simp]
theorem gmCpowDerivativeCoeff_zero (z : ℂ) :
    gmCpowDerivativeCoeff z 0 = 1 := by
  rfl

theorem gmCpowDerivativeCoeff_succ (z : ℂ) (n : ℕ) :
    gmCpowDerivativeCoeff z (n + 1) =
      z * gmCpowDerivativeCoeff (z - 1) n := by
  rfl

/-- Repeated real derivative of a complex power on the positive axis. -/
theorem iteratedDeriv_ofReal_cpow (z : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
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
        by_cases hz : z = 0
        · subst z
          simp
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
theorem norm_gmCpowDerivativeCoeff_le (z : ℂ) (n : ℕ) :
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


private theorem gmTraceKernel_eq_cutoffSq_mul_cpow
    (cutoff : GMSmoothCutoff) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    gmTraceKernel cutoff t x =
      gmCutoffSqComplex cutoff x * (x : ℂ) ^ ((t : ℂ) * I) := by
  unfold gmTraceKernel gmCutoffSqComplex
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  congr 2
  push_cast
  ring

theorem contDiffAt_ofReal_cpow_mul_I
    (t : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ n (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x := by
  have hEq :
      (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) =ᶠ[nhds x]
        fun y : ℝ => Complex.exp ((((t * Real.log y : ℝ) : ℂ) * I)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
    rw [← Complex.ofReal_log hy.le]
    congr 1
    push_cast
    ring
  have hExp : ContDiffAt ℝ n
      (fun y : ℝ => Complex.exp ((((t * Real.log y : ℝ) : ℂ) * I))) x := by
    have hReal : ContDiffAt ℝ n (fun y : ℝ => t * Real.log y) x :=
      contDiffAt_const.mul (Real.contDiffAt_log.mpr hx.ne')
    have hComplex : ContDiffAt ℝ n
        (fun y : ℝ => ((t * Real.log y : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hReal
    exact (hComplex.mul contDiffAt_const).cexp
  exact hExp.congr_of_eventuallyEq hEq

/-- Derivatives of the Mellin phase on a half-line bounded away from zero. -/
theorem norm_iteratedDeriv_mellinPhase_le (t : ℝ) (n : ℕ)
    {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) :
    ‖iteratedDeriv n (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x‖ ≤
      a⁻¹ ^ n * (|t| + n) ^ n := by
  have hx₀ := ha.trans_le hx
  rw [iteratedDeriv_ofReal_cpow _ _ hx₀, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx₀, mul_comm (a⁻¹ ^ n)]
  have hp : x ^ (-(n : ℝ)) ≤ a⁻¹ ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg_eq_inv_rpow]
    exact Real.rpow_le_rpow_of_nonpos ha hx (neg_nonpos.mpr (Nat.cast_nonneg n))
  exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_gmCpowDerivativeCoeff_le ((t : ℂ) * I) n)
    (by simpa using hp) (by positivity) (by positivity)

theorem mellinDerivativePower_le (t : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    (|t| + k) ^ k ≤ (n + 1 : ℝ) ^ n * (1 + |t|) ^ n := by
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn : (0 : ℝ) ≤ n := by positivity
  rw [← mul_pow]
  exact (pow_le_pow_left₀ (by positivity) (show |t| + k ≤ (n + 1) * (1 + |t|) by
    nlinarith [abs_nonneg t]) k).trans (pow_le_pow_right₀ (by nlinarith [abs_nonneg t]) hkn)

/-- The Leibniz bound for the product of an amplitude and a Mellin phase. -/
noncomputable def mellinDerivativeConstant (w : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i w *
    a⁻¹ ^ (n - i) * (n + 1 : ℝ) ^ n

theorem mellinDerivativeConstant_nonneg (w : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 ≤ mellinDerivativeConstant w a n := by unfold mellinDerivativeConstant; positivity

private theorem eventuallyEq_zero_off_Icc {f : ℝ → ℂ} {a b x : ℝ}
    (h : Function.support f ⊆ Icc a b) (hx : x ∉ Icc a b) : f =ᶠ[nhds x] 0 := by
  filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
  exact not_ne_iff.mp (fun hne => hy (h hne))

theorem norm_iteratedDeriv_mellinKernel_le (w : 𝓢(ℝ, ℂ)) {a b : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hs : Function.support f ⊆ Icc a b) (t : ℝ)
    (hf : ∀ x, 0 < x → f x = w x * (x : ℂ) ^ ((t : ℂ) * I)) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n f x‖ ≤ mellinDerivativeConstant w a n * (1 + |t|) ^ n := by
  by_cases hx : x ∈ Icc a b
  · have hx₀ := ha.trans_le hx.1
    have hl : f =ᶠ[nhds x] ((w : ℝ → ℂ) * fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) := by
      filter_upwards [Ioi_mem_nhds hx₀] with y hy using hf y hy
    rw [hl.iteratedDeriv_eq, iteratedDeriv_mul (w.smooth n).contDiffAt
      (contDiffAt_ofReal_cpow_mul_I t n hx₀), mellinDerivativeConstant, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hw := SchwartzMap.le_seminorm' (𝕜 := ℝ) 0 i w x
    simp only [pow_zero, one_mul] at hw
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i w *
          (a⁻¹ ^ (n - i) * (|t| + (n - i : ℕ)) ^ (n - i)) := by
        gcongr
        exact norm_iteratedDeriv_mellinPhase_le t _ ha hx.1
      _ ≤ _ := by
        rw [mul_assoc ((n.choose i : ℝ) * _ * _) _ _, ← mul_assoc ((n.choose i : ℝ) * _)]
        gcongr
        exact mellinDerivativePower_le t (Nat.sub_le n i)
  · rw [(eventuallyEq_zero_off_Icc hs hx).iteratedDeriv_eq, iteratedDeriv_const_zero, norm_zero]
    exact mul_nonneg (mellinDerivativeConstant_nonneg w ha n) (by positivity)

private theorem integral_norm_iteratedFDeriv_of_support (f : 𝓢(ℝ, ℂ)) (p : ℕ)
    {a b D : ℝ} (hab : a ≤ b) (h : Function.support (f : ℝ → ℂ) ⊆ Icc a b)
    (hD : ∀ x, ‖iteratedFDeriv ℝ p (f : ℝ → ℂ) x‖ ≤ D) :
    (∫ x : ℝ, ‖iteratedFDeriv ℝ p (f : ℝ → ℂ) x‖) ≤ (b - a) * D := by
  let g (x : ℝ) := ‖iteratedFDeriv ℝ p (f : ℝ → ℂ) x‖
  have hg : Integrable g := by
    simpa only [g, pow_zero, one_mul] using f.integrable_pow_mul_iteratedFDeriv volume 0 p
  have hEq : (Icc a b).indicator g = g := by
    funext x
    by_cases hx : x ∈ Icc a b
    · simp [hx]
    · simp [g, hx, (eventuallyEq_zero_off_Icc h hx).iteratedFDeriv ℝ p |>.eq_of_nhds]
  change (∫ x, g x) ≤ _
  calc
    (∫ x, g x) = ∫ x in Icc a b, g x := by rw [← integral_indicator measurableSet_Icc, hEq]
    _ ≤ ∫ _x in Icc a b, D := setIntegral_mono_on hg.integrableOn
      (integrableOn_const (hs := measure_Icc_lt_top.ne)) measurableSet_Icc (fun x _ => hD x)
    _ = (b - a) * D := by simp [max_eq_left (sub_nonneg.mpr hab)]

/-- Fourier decay is uniform in a parameter when all derivative bounds are uniform. -/
theorem schwartz_family_fourier_decay (f : ℝ → 𝓢(ℝ, ℂ)) {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ t, Function.support (f t : ℝ → ℂ) ⊆ Icc a b)
    (hD : ∀ p : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ t x : ℝ,
      ‖iteratedFDeriv ℝ p (f t : ℝ → ℂ) x‖ ≤ D * (1 + |t|) ^ p) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, |ξ| ^ n * ‖𝓕 (f t) ξ‖ ≤ C * (1 + |t|) ^ n := by
  choose D hD₀ hDb using hD
  refine ⟨2 ^ n * ∑ p ∈ Finset.range (n + 1), (b - a) * D p, mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ => mul_nonneg (sub_nonneg.mpr hab) (hD₀ p)), ?_⟩
  intro t ξ
  have hF := pow_mul_norm_iteratedFDeriv_fourier_le
    (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞)) ((f t).smooth ⊤)
    (fun k p _ _ => (f t).integrable_pow_mul_iteratedFDeriv volume k p)
    (k := 0) (n := n) (by norm_num) (by simp) ξ
  simp only [pow_zero, one_mul, zero_add, Finset.range_one, norm_iteratedFDeriv_zero,
    Finset.singleton_product, Finset.sum_map, Function.Embedding.sectR_apply] at hF
  have hF' : |ξ| ^ n * ‖𝓕 (f t) ξ‖ ≤
      2 ^ n * ∑ p ∈ Finset.range (n + 1), ∫ x : ℝ, ‖iteratedFDeriv ℝ p (f t : ℝ → ℂ) x‖ := by
    convert hF using 1
    · simp [Real.norm_eq_abs, SchwartzMap.fourier_coe]
    · congr 1
      norm_num
  refine hF'.trans ?_
  rw [mul_assoc, Finset.sum_mul]
  gcongr with p hp
  exact (integral_norm_iteratedFDeriv_of_support (f t) p hab (hs t) (hDb p t)).trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg t])
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp))) (hD₀ p)) (sub_nonneg.mpr hab))

/-- Polynomial decay of a fixed Schwartz function after rescaling. -/
theorem schwartz_rescale_polynomial_decay (F : 𝓢(ℝ, ℂ)) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |r| ^ n * ‖F (r / c)‖ ≤ C := by
  refine ⟨c ^ n * SchwartzMap.seminorm ℝ n 0 F, by positivity, fun r => ?_⟩
  have hSem := SchwartzMap.le_seminorm' (𝕜 := ℝ) n 0 F (r / c)
  rw [iteratedDeriv_zero] at hSem
  have h : |r| = c * ‖r / c‖ := by rw [Real.norm_eq_abs, abs_div, abs_of_pos hc]; field_simp
  conv_lhs => rw [h, mul_pow, mul_assoc]
  gcongr
  simpa only [Real.norm_eq_abs] using hSem

private theorem gmTraceKernel_support (cutoff : GMSmoothCutoff) (t : ℝ) :
    Function.support (gmTraceKernel cutoff t) ⊆ Icc 1 2 := by
  intro x hx
  by_contra hn
  have hz : cutoff x = 0 := not_ne_iff.mp (fun h => hn (cutoff.support h))
  exact hx (by simp [gmTraceKernel, hz])

/-- Guth--Maynard Lemma 4.3 in the exact two-parameter form needed to make
the smooth-reflection frequency truncation uniform. -/
theorem gmTraceKernel_uniform_iteratedFDeriv (cutoff : GMSmoothCutoff)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x : ℝ,
      ‖iteratedFDeriv ℝ n (gmTraceKernel cutoff t) x‖ ≤
        C * (1 + |t|) ^ n := by
  refine ⟨mellinDerivativeConstant (gmCutoffSqSchwartz cutoff) 1 n,
    mellinDerivativeConstant_nonneg _ (by norm_num) _, fun t x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact norm_iteratedDeriv_mellinKernel_le _ (by norm_num) (gmTraceKernel_support cutoff t) t
    (fun y hy => gmTraceKernel_eq_cutoffSq_mul_cpow cutoff t hy) n x

/-- Uniform two-parameter Fourier decay.  The constant depends only on the
fixed cutoff and derivative order, while the complete `t` dependence is the
source polynomial `(1+|t|)^n`. -/
theorem gmTraceFourier_uniform_decay (cutoff : GMSmoothCutoff) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ,
      |ξ| ^ n * ‖gmTraceFourier cutoff t ξ‖ ≤
        C * (1 + |t|) ^ n :=
  schwartz_family_fourier_decay (gmTraceKernelSchwartz cutoff) (by norm_num)
    (gmTraceKernel_support cutoff) (gmTraceKernel_uniform_iteratedFDeriv cutoff) n

/-- A polynomial Fourier decay bound sums over omitted integer frequencies. -/
theorem fourier_tail_bound_order
    (F : ℝ → ℝ → ℂ) (n : ℕ)
    (decay : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ,
      |ξ| ^ (n + 2) * ‖F t ξ‖ ≤ C * (1 + |t|) ^ (n + 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ), 0 < N → 0 < M → ∀ t : ℝ,
      ‖(∑' m : ℤ, if M < m.natAbs then F t ((N : ℝ) * (m : ℝ)) else 0)‖ ≤
        K * (1 + |t|) ^ (n + 2) /
          ((N : ℝ) ^ (n + 2) * (M : ℝ) ^ n) := by
  obtain ⟨C₀, hC₀, hDecay⟩ := decay
  let C : ℝ := C₀ + 1
  have hC : 0 < C := by dsimp only [C]; linarith
  have hPSeries : Summable (fun m : ℤ => ‖1 / (m : ℂ) ^ 2‖) := by
    have hNorm : (fun m : ℤ => ‖1 / (m : ℂ) ^ 2‖) =
        fun m : ℤ => |1 / (m : ℝ) ^ 2| := by
      funext m
      simp only [norm_div, norm_one, norm_pow, Complex.norm_intCast,
        abs_div, abs_one, pow_abs]
    rw [hNorm, summable_abs_iff]
    exact Real.summable_one_div_int_pow.mpr (by norm_num)
  let B : ℝ := ∑' m : ℤ, ‖1 / (m : ℂ) ^ 2‖
  have hB : 0 ≤ B := tsum_nonneg fun m => norm_nonneg _
  refine ⟨C * B + 1, by positivity, ?_⟩
  intro N M hN hM t
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  let scale : ℝ := C * (1 + |t|) ^ (n + 2) /
    ((N : ℝ) ^ (n + 2) * (M : ℝ) ^ n)
  have hPointwise : ∀ m : ℤ, M < m.natAbs →
      ‖F t ((N : ℝ) * (m : ℝ))‖ ≤
        scale * ‖1 / (m : ℂ) ^ 2‖ := by
    intro m hm
    have hmNatPos : 0 < m.natAbs := hM.trans hm
    have hmNe : m ≠ 0 := Int.natAbs_ne_zero.mp hmNatPos.ne'
    have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hmNe
    have hmAbsPos : 0 < |(m : ℝ)| := abs_pos.mpr hmReal
    have hmAbs : (M : ℝ) ≤ |(m : ℝ)| := by
      have hcast : (M : ℝ) ≤ (m.natAbs : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hm)
      simpa using hcast
    have hFreqAbs : |(N : ℝ) * (m : ℝ)| =
        (N : ℝ) * |(m : ℝ)| := by
      rw [abs_mul, abs_of_pos hNr]
    have hFreqPos : 0 < |(N : ℝ) * (m : ℝ)| := by
      rw [hFreqAbs]
      positivity
    have hFourier :
        ‖F t ((N : ℝ) * (m : ℝ))‖ ≤
          C₀ * (1 + |t|) ^ (n + 2) /
            |(N : ℝ) * (m : ℝ)| ^ (n + 2) := by
      rw [le_div_iff₀ (pow_pos hFreqPos (n + 2))]
      simpa [mul_comm] using hDecay t ((N : ℝ) * (m : ℝ))
    have hpow : (M : ℝ) ^ n * |(m : ℝ)| ^ 2 ≤
        |(m : ℝ)| ^ (n + 2) := by
      calc
        (M : ℝ) ^ n * |(m : ℝ)| ^ 2 ≤
            |(m : ℝ)| ^ n * |(m : ℝ)| ^ 2 := by gcongr
        _ = |(m : ℝ)| ^ (n + 2) := by rw [pow_add]
    rw [norm_div, norm_one, norm_pow, Complex.norm_intCast]
    calc
      ‖F t ((N : ℝ) * (m : ℝ))‖ ≤
          C₀ * (1 + |t|) ^ (n + 2) /
            |(N : ℝ) * (m : ℝ)| ^ (n + 2) := hFourier
      _ ≤ C * (1 + |t|) ^ (n + 2) /
          ((N : ℝ) ^ (n + 2) * |(m : ℝ)| ^ (n + 2)) := by
        rw [hFreqAbs, mul_pow]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith)
            (by positivity)) (by positivity)
      _ ≤ C * (1 + |t|) ^ (n + 2) /
          ((N : ℝ) ^ (n + 2) *
            ((M : ℝ) ^ n * |(m : ℝ)| ^ 2)) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = scale * (1 / |(m : ℝ)| ^ 2) := by
        dsimp only [scale]
        field_simp [hNr.ne', hMr.ne', hmAbsPos.ne']
  have hComparison : ∀ m : ℤ,
      ‖if M < m.natAbs then
          F t ((N : ℝ) * (m : ℝ)) else 0‖ ≤
        scale * ‖1 / (m : ℂ) ^ 2‖ := by
    intro m
    by_cases hm : M < m.natAbs
    · simpa only [ite_eq_left hm] using hPointwise m hm
    · have hscale : 0 ≤ scale := by dsimp only [scale]; positivity
      rw [ite_eq_right hm, norm_zero]
      exact mul_nonneg hscale (norm_nonneg _)
  have hScaled : Summable (fun m : ℤ => scale * ‖1 / (m : ℂ) ^ 2‖) :=
    hPSeries.mul_left scale
  have hBound := tsum_of_norm_bounded hScaled.hasSum hComparison
  rw [tsum_mul_left] at hBound
  change ‖(∑' m : ℤ, if M < m.natAbs then F t ((N : ℝ) * (m : ℝ)) else 0)‖ ≤ scale * B at hBound
  have hDen : 0 < (N : ℝ) ^ (n + 2) * (M : ℝ) ^ n := by positivity
  calc
    ‖(∑' m : ℤ, if M < m.natAbs then F t ((N : ℝ) * (m : ℝ)) else 0)‖ ≤ scale * B := hBound
    _ ≤ (C * B + 1) * (1 + |t|) ^ (n + 2) /
          ((N : ℝ) ^ (n + 2) * (M : ℝ) ^ n) := by
      dsimp only [scale]
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hDen).2
      have hpowNonneg : 0 ≤ (1 + |t|) ^ (n + 2) := by positivity
      nlinarith

/-- Reversing the Fourier frequency is complex conjugation together with
reversal of the Mellin ordinate.  This supplies the negative-frequency half
of the smooth-reflection expansion from the positive-frequency formula. -/
theorem gmTraceFourier_neg_eq_conj (cutoff : GMSmoothCutoff) (t ξ : ℝ) :
    gmTraceFourier cutoff t (-ξ) =
      star (gmTraceFourier cutoff (-t) ξ) := by
  rw [gmTraceFourier, SchwartzMap.fourier_coe, Real.fourier_eq',
    gmTraceFourier, SchwartzMap.fourier_coe, Real.fourier_eq']
  let f : ℝ → ℂ := fun x =>
    Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * I) •
      gmTraceKernelSchwartz cutoff (-t) x
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
  simp only [map_neg, map_mul, map_ofNat, conj_ofReal, conj_I]
  ring_nf

/-- The `gmCutoffMellin` definition used by the source-facing construction in `LargeValuesReflection`. -/
noncomputable def gmCutoffMellin
    (cutoff : GMSmoothCutoff) (r : ℝ) : ℂ :=
  mellin (fun y : ℝ => ((cutoff y : ℂ) ^ 2))
    ((1 : ℂ) + (r : ℂ) * I)

theorem gmCutoffMellin_eq_fourier
    (cutoff : GMSmoothCutoff) (r : ℝ) :
    gmCutoffMellin cutoff r =
      𝓕 (gmMellinKernelSchwartz cutoff) (r / (2 * Real.pi)) := by
  unfold gmCutoffMellin
  rw [mellin_eq_fourier, SchwartzMap.fourier_coe]
  simp
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (r / (2 * Real.pi)))
  funext u
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
  simpa only [gmCutoffMellin_eq_fourier] using
    schwartz_rescale_polynomial_decay (𝓕 (gmMellinKernelSchwartz cutoff)) (by positivity) n

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
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hm.trans hmM
    nlinarith
  have hH : Integrable (gmCutoffMellin cutoff) := by
    unfold gmCutoffMellin
    simpa only [VerticalIntegrable, Complex.ofReal_one] using
      verticalIntegrable_mellin_gmCutoffSq_one cutoff
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
    exact (hElementary.mul (hH.aestronglyMeasurable.comp_snd)).congr
      (Filter.Eventually.of_forall fun z => by
        simp [gmMellinReflectionIntegrand, Function.uncurry_def]
        ring)
  · rw [Measure.ae_prod_iff_ae_ae (by
      apply measurableSet_le
      · have hHM : Measurable fun z : ℝ × ℝ => gmCutoffMellin cutoff z.2 :=
          (continuous_gmCutoffMellin cutoff).measurable.comp measurable_snd
        unfold gmMellinReflectionIntegrand Function.uncurry
        measurability
      · exact ((continuous_gmCutoffMellin cutoff).norm.comp continuous_snd
          |>.const_mul (m : ℝ)).measurable)]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with v hv
    filter_upwards with r
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
      have hmReal : (0 : ℝ) ≤ m := by positivity
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

private theorem gmCutoffPhase_eq_mellinIntegral
    (cutoff : GMSmoothCutoff) (t q : ℝ) {v : ℝ}
    (hv : 0 < v) (hq : 0 < q) :
    (cutoff (v / q) : ℂ) ^ 2 *
        Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ, gmMellinReflectionIntegrand cutoff t q v r := by
  have hratio : 0 < v / q := div_pos hv hq
  rw [gmCutoffSq_eq_verticalMellinIntegral cutoff hratio]
  rw [smul_mul_assoc]
  congr 1
  rw [← MeasureTheory.integral_mul_const]
  congr 1
  funext r
  unfold gmMellinReflectionIntegrand gmCutoffMellin
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hratio.ne')]
  rw [← Complex.ofReal_log hratio.le]
  have hExpLog : Complex.exp ((Real.log (v / q) : ℝ) : ℂ) = (v / q : ℝ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hratio]
  have hRatioInv : (((v / q : ℝ) : ℂ))⁻¹ = (q : ℂ) * (v : ℂ)⁻¹ := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  have hRatioInvC : ((v : ℂ) / (q : ℂ))⁻¹ = (q : ℂ) * (v : ℂ)⁻¹ := by
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  have hsplit :
      (Real.log (v / q) : ℂ) * -((1 : ℂ) + (r : ℂ) * I) =
        -(Real.log (v / q) : ℂ) +
          -(((r * Real.log (v / q) : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_neg, hExpLog]
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
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hm.trans hmM
    nlinarith
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hqNat : 0 < N * m := Nat.mul_pos hN (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hqReal : (0 : ℝ) < N * m := by exact_mod_cast hqNat
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
        unfold gmReflectionIntegral
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro v hv
        have hvPos : 0 < v := hNReal.trans_le
          ((Set.uIcc_of_le hAB ▸ hv).1)
        unfold gmMellinReflectionIntegrand
        change
          ((v : ℂ) / (((N : ℝ) * m : ℝ) : ℂ))⁻¹ *
                Complex.exp (-(((r * Real.log (v / ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
              gmCutoffMellin cutoff r *
                Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
            ((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
              gmCutoffMellin cutoff r *
                ((v : ℂ)⁻¹ * Complex.exp
                  (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))
        have hlog : Real.log (v / ((N : ℝ) * m)) =
            Real.log v - Real.log ((N : ℝ) * m) :=
          Real.log_div hvPos.ne' hqReal.ne'
        rw [hlog]
        have hqComplex : (((N : ℝ) * m : ℝ) : ℂ) = ((N * m : ℕ) : ℂ) := by
          norm_num
        rw [← hqComplex]
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqReal.ne')]
        rw [← Complex.ofReal_log hqReal.le]
        have hRatioInv :
            ((v : ℂ) / (((N : ℝ) * m : ℝ) : ℂ))⁻¹ =
              (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ := by
          field_simp [Complex.ofReal_ne_zero.mpr hqReal.ne',
            Complex.ofReal_ne_zero.mpr hvPos.ne']
        have hExpEq :
            Complex.exp (-(((r * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
                Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
              Complex.exp ((Real.log ((N : ℝ) * m) : ℂ) * ((r : ℂ) * I)) *
                Complex.exp (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [hRatioInv]
        calc
          (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ *
                Complex.exp (-(((r * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
              gmCutoffMellin cutoff r *
                Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
            (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ * gmCutoffMellin cutoff r *
              (Complex.exp (-(((r * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
                Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by ring
          _ = (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ * gmCutoffMellin cutoff r *
              (Complex.exp ((Real.log ((N : ℝ) * m) : ℂ) * ((r : ℂ) * I)) *
                Complex.exp (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by
            rw [hExpEq]
          _ = (((N : ℝ) * m : ℝ) : ℂ) *
                Complex.exp ((Real.log ((N : ℝ) * m) : ℂ) * ((r : ℂ) * I)) *
              gmCutoffMellin cutoff r *
                ((v : ℂ)⁻¹ * Complex.exp
                  (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by ring

/-- Global logarithmic majorant for the reflection integral.  This is the
nonoscillatory estimate used only on the omitted Mellin range in Lemma 6.2. -/
theorem norm_gmReflectionIntegral_le_log {tau a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ‖gmReflectionIntegral tau a b‖ ≤ Real.log (b / a) := by
  unfold gmReflectionIntegral
  have hb : 0 < b := ha.trans_le hab
  have hInv : IntervalIntegrable (fun v : ℝ => v⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_inv₀.mono
    intro v hv
    rw [Set.uIcc_of_le hab] at hv
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

private theorem intervalIntegral_gmMellinReflectionIntegrand_eq
    (cutoff : GMSmoothCutoff) (t r : ℝ) {N m M : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    (∫ v in (N : ℝ)..(2 * N * M : ℝ),
        gmMellinReflectionIntegrand cutoff t (N * m) v r) =
      ((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
        gmCutoffMellin cutoff r *
          gmReflectionIntegral (t - r) N (2 * N * M) := by
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hm.trans hmM
    nlinarith
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hqNat : 0 < N * m := Nat.mul_pos hN (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hqReal : (0 : ℝ) < N * m := by exact_mod_cast hqNat
  unfold gmReflectionIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  have hvPos : 0 < v := hNReal.trans_le
    ((Set.uIcc_of_le hAB ▸ hv).1)
  unfold gmMellinReflectionIntegrand
  change
    ((v : ℂ) / (((N : ℝ) * m : ℝ) : ℂ))⁻¹ *
          Complex.exp (-(((r * Real.log (v / ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
        gmCutoffMellin cutoff r *
          Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
      ((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
        gmCutoffMellin cutoff r *
          ((v : ℂ)⁻¹ * Complex.exp
            (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))
  have hlog : Real.log (v / ((N : ℝ) * m)) =
      Real.log v - Real.log ((N : ℝ) * m) :=
    Real.log_div hvPos.ne' hqReal.ne'
  rw [hlog]
  have hqComplex : (((N : ℝ) * m : ℝ) : ℂ) = ((N * m : ℕ) : ℂ) := by
    norm_num
  rw [← hqComplex]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqReal.ne')]
  rw [← Complex.ofReal_log hqReal.le]
  have hRatioInv :
      ((v : ℂ) / (((N : ℝ) * m : ℝ) : ℂ))⁻¹ =
        (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ := by
    field_simp [Complex.ofReal_ne_zero.mpr hqReal.ne',
      Complex.ofReal_ne_zero.mpr hvPos.ne']
  have hExpEq :
      Complex.exp (-(((r * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
          Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
        Complex.exp ((Real.log ((N : ℝ) * m) : ℂ) * ((r : ℂ) * I)) *
          Complex.exp (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hRatioInv]
  calc
    (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ *
          Complex.exp (-(((r * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
        gmCutoffMellin cutoff r *
          Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
      (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ * gmCutoffMellin cutoff r *
        (Complex.exp (-(((r * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
          Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by ring
    _ = (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ * gmCutoffMellin cutoff r *
        (Complex.exp ((Real.log ((N : ℝ) * m) : ℂ) * ((r : ℂ) * I)) *
          Complex.exp (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by
      rw [hExpEq]
    _ = (((N : ℝ) * m : ℝ) : ℂ) *
          Complex.exp ((Real.log ((N : ℝ) * m) : ℂ) * ((r : ℂ) * I)) *
        gmCutoffMellin cutoff r *
          ((v : ℂ)⁻¹ * Complex.exp
            (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by ring

/-- Uniform first/second-derivative estimate for the common reflection
integral.  This is the `T₀⁻¹/²` analytic core of Guth--Maynard Lemma 6.2. -/
theorem norm_gmReflectionIntegral_le_ten_div_sqrt {tau A B : ℝ}
    (htau : 1 ≤ tau) (hA : 0 < A) (hAB : A ≤ B) :
    ‖gmReflectionIntegral tau A B‖ ≤ 10 / Real.sqrt tau := by
  let x0 : ℝ := tau / (2 * Real.pi)
  let delta : ℝ := Real.sqrt tau / (4 * Real.pi)
  let L : ℝ := x0 - delta
  let R : ℝ := x0 + delta
  have htauPos : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  have hsqrtPos : 0 < Real.sqrt tau := Real.sqrt_pos.2 htauPos
  have hsqrtSq : (Real.sqrt tau) ^ 2 = tau := Real.sq_sqrt htauPos.le
  have hsqrtLe : Real.sqrt tau ≤ tau := by
    nlinarith [Real.sqrt_nonneg tau]
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    positivity
  have hLR : L < R := by dsimp only [L, R]; linarith
  have hLFormula : L = (2 * tau - Real.sqrt tau) / (4 * Real.pi) := by
    dsimp only [L, x0, delta]
    field_simp [Real.pi_ne_zero]
    ring
  have hLLower : tau / (4 * Real.pi) ≤ L := by
    rw [hLFormula]
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 4 * Real.pi)).2
    linarith
  have hLPos : 0 < L := (div_pos htauPos (by positivity)).trans_le hLLower
  have hLeftDen : tau - 2 * Real.pi * L = Real.sqrt tau / 2 := by
    dsimp only [L, x0, delta]
    field_simp [Real.pi_ne_zero]
    ring
  have hRightDen : 2 * Real.pi * R - tau = Real.sqrt tau / 2 := by
    dsimp only [R, x0, delta]
    field_simp [Real.pi_ne_zero]
    ring
  by_cases hEntireLeft : B ≤ L
  · have hDenPos : 0 < tau - 2 * Real.pi * B := by
      have hScaled := mul_le_mul_of_nonneg_left hEntireLeft
        (by positivity : 0 ≤ 2 * Real.pi)
      nlinarith [hLeftDen, hsqrtPos]
    have hLeft := norm_gmReflectionIntegral_le_left (tau := tau)
      (a := A) (b := B) hAB hA (by linarith)
    calc
      ‖gmReflectionIntegral tau A B‖ ≤ 2 / (tau - 2 * Real.pi * B) := hLeft
      _ ≤ 4 / Real.sqrt tau := by
        have hDen : Real.sqrt tau / 2 ≤ tau - 2 * Real.pi * B := by
          rw [← hLeftDen]
          nlinarith [mul_le_mul_of_nonneg_left hEntireLeft
            (by positivity : 0 ≤ 2 * Real.pi)]
        apply (div_le_div_iff₀ hDenPos hsqrtPos).2
        nlinarith
      _ ≤ 10 / Real.sqrt tau := by
        exact div_le_div_of_nonneg_right (by norm_num) hsqrtPos.le
  by_cases hEntireRight : R ≤ A
  · have hDenPos : 0 < 2 * Real.pi * A - tau := by
      have hScaled := mul_le_mul_of_nonneg_left hEntireRight
        (by positivity : 0 ≤ 2 * Real.pi)
      nlinarith [hRightDen, hsqrtPos]
    have hRight := norm_gmReflectionIntegral_le_right (tau := tau)
      (a := A) (b := B) hAB hA (by linarith)
    calc
      ‖gmReflectionIntegral tau A B‖ ≤ 2 / (2 * Real.pi * A - tau) := hRight
      _ ≤ 4 / Real.sqrt tau := by
        have hDen : Real.sqrt tau / 2 ≤ 2 * Real.pi * A - tau := by
          rw [← hRightDen]
          nlinarith [mul_le_mul_of_nonneg_left hEntireRight
            (by positivity : 0 ≤ 2 * Real.pi)]
        apply (div_le_div_iff₀ hDenPos hsqrtPos).2
        nlinarith
      _ ≤ 10 / Real.sqrt tau := by
        exact div_le_div_of_nonneg_right (by norm_num) hsqrtPos.le
  · have hLB : L < B := lt_of_not_ge hEntireLeft
    have hAR : A < R := lt_of_not_ge hEntireRight
    let l : ℝ := max A L
    let r : ℝ := min B R
    have hAl : A ≤ l := le_max_left _ _
    have hlB : l ≤ B := max_le hAB hLB.le
    have hAr : A ≤ r := le_min hAB hAR.le
    have hrB : r ≤ B := min_le_left _ _
    have hlr : l ≤ r := by
      apply max_le
      · exact hAr
      · exact le_min hLB.le hLR.le
    have hlPos : 0 < l := hA.trans_le hAl
    have hrPos : 0 < r := hlPos.trans_le hlr
    have hLeftPiece : ‖gmReflectionIntegral tau A l‖ ≤
        4 / Real.sqrt tau := by
      by_cases hEq : l = A
      · rw [hEq]
        simp [gmReflectionIntegral]
        positivity
      · have hAL : A < L := by
          have hnot : ¬ L ≤ A := by
            intro hLA
            apply hEq
            exact max_eq_left hLA
          exact lt_of_not_ge hnot
        have hlEq : l = L := max_eq_right hAL.le
        rw [hlEq]
        have hBound := norm_gmReflectionIntegral_le_left hAL.le hA (by
          rw [← sub_pos, hLeftDen]
          positivity)
        rw [hLeftDen] at hBound
        calc
          ‖gmReflectionIntegral tau A L‖ ≤ 2 / (Real.sqrt tau / 2) := hBound
          _ = 4 / Real.sqrt tau := by field_simp; norm_num
    have hRightPiece : ‖gmReflectionIntegral tau r B‖ ≤
        4 / Real.sqrt tau := by
      by_cases hEq : r = B
      · rw [hEq]
        simp [gmReflectionIntegral]
        positivity
      · have hRB : R < B := by
          have hnot : ¬ B ≤ R := by
            intro hBR
            apply hEq
            exact min_eq_left hBR
          exact lt_of_not_ge hnot
        have hrEq : r = R := min_eq_right hRB.le
        rw [hrEq]
        have hBound := norm_gmReflectionIntegral_le_right hRB.le
          (hLPos.trans hLR) (by
          rw [← sub_pos, hRightDen]
          positivity)
        rw [hRightDen] at hBound
        calc
          ‖gmReflectionIntegral tau R B‖ ≤ 2 / (Real.sqrt tau / 2) := hBound
          _ = 4 / Real.sqrt tau := by field_simp; norm_num
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
      rw [← intervalIntegral.integral_add_adjacent_intervals hIntAl
        (hIntlR.trans hIntrB)]
      rw [← intervalIntegral.integral_add_adjacent_intervals hIntlR hIntrB]
      ring
    rw [hSplit]
    calc
      ‖gmReflectionIntegral tau A l + gmReflectionIntegral tau l r +
          gmReflectionIntegral tau r B‖ ≤
          ‖gmReflectionIntegral tau A l‖ + ‖gmReflectionIntegral tau l r‖ +
            ‖gmReflectionIntegral tau r B‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
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
  let k : ℝ → ℂ := fun v =>
    (v : ℂ)⁻¹ * Complex.exp
      ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))
  let F : ℝ → ℂ := fun x => ∫ v in A..x, k v
  have hkInt : IntervalIntegrable k volume A B := by
    simpa only [k] using intervalIntegrable_gmReflectionIntegrand hAB hA
  have hkContinuousPos : ContinuousOn k (Set.Ioi 0) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hxPos : 0 < x := hx
    have hPhase : ContinuousAt
        (fun y : ℝ => tau * Real.log y - 2 * Real.pi * y) x :=
      (continuousAt_const.mul (Real.continuousAt_log hxPos.ne')).sub
        (continuousAt_const.mul continuousAt_id)
    exact (Complex.continuous_ofReal.continuousAt.comp continuousAt_id).inv₀
        (Complex.ofReal_ne_zero.mpr hxPos.ne') |>.mul
      ((Complex.continuous_ofReal.continuousAt.comp hPhase).mul
        continuousAt_const).cexp
  have hkContinuousAt : ∀ x ∈ Set.Icc A B, ContinuousAt k x := by
    intro x hx
    have hxPos : 0 < x := hA.trans_le hx.1
    exact (hkContinuousPos x hxPos).continuousAt (Ioi_mem_nhds hxPos)
  have hkContinuous : ContinuousOn k (Set.Icc A B) :=
    fun x hx => (hkContinuousAt x hx).continuousWithinAt
  have hFDeriv : ∀ x ∈ Set.Icc A B, HasDerivAt F (k x) x := by
    intro x hx
    have hkAx : IntervalIntegrable k volume A x := by
      simpa only [k] using
        intervalIntegrable_gmReflectionIntegrand hx.1 hA
    exact intervalIntegral.integral_hasDerivAt_right hkAx
      (hkContinuousPos.stronglyMeasurableAtFilter isOpen_Ioi x
        (hA.trans_le hx.1))
      (hkContinuousAt x hx)
  have hFContinuous : ContinuousOn F (Set.Icc A B) :=
    fun x hx => (hFDeriv x hx).continuousAt.continuousWithinAt
  have hFContinuousU : ContinuousOn F (Set.uIcc A B) := by
    simpa only [Set.uIcc_of_le hAB] using hFContinuous
  have hwU : ∀ x ∈ Set.uIcc A B, HasDerivAt w (w' x) x := by
    simpa only [Set.uIcc_of_le hAB] using hw
  have hFDerivU : ∀ x ∈ Set.uIcc A B, HasDerivAt F (k x) x := by
    simpa only [Set.uIcc_of_le hAB] using hFDeriv
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hwU hFDerivU hw' hkInt
  have hFA : F A = 0 := by simp [F]
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
        rw [abs_of_nonneg]
        exact intervalIntegral.integral_nonneg hAB fun _ _ => norm_nonneg _
      _ ≤ ∫ v in A..B, ‖w' v‖ * (10 / Real.sqrt tau) := by
        apply intervalIntegral.integral_mono_on hAB
        · simpa only [norm_mul] using
            (hw'.norm.mul_continuousOn hFContinuousU.norm)
        · exact hw'.norm.mul_const (10 / Real.sqrt tau)
        · intro v hv
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hFBound v hv) (norm_nonneg _)
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

theorem hasDerivAt_gmReflectionPowerWeight
    {sigma v : ℝ} (hv : 0 < v) :
    HasDerivAt (gmReflectionPowerWeight sigma)
      (((-sigma / v : ℝ) : ℂ) * gmReflectionPowerWeight sigma v) v := by
  unfold gmReflectionPowerWeight
  have hReal : HasDerivAt (fun x : ℝ => -sigma * Real.log x) (-sigma / v) v := by
    simpa only [div_eq_mul_inv] using
      (Real.hasDerivAt_log hv.ne').const_mul (-sigma)
  convert hReal.ofReal_comp.cexp using 1
  all_goals ring

theorem norm_gmReflectionPowerWeight {sigma v : ℝ} (hv : 0 < v) :
    ‖gmReflectionPowerWeight sigma v‖ = v ^ (-sigma) := by
  unfold gmReflectionPowerWeight
  rw [Complex.norm_exp]
  simp only [ofReal_re]
  rw [Real.rpow_def_of_pos hv]
  congr 1
  ring

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
    intro x hx
    have hxIcc : x ∈ Set.Icc A B := by
      simpa only [Set.uIcc_of_le hAB] using hx
    have hxPos : 0 < x := hA.trans_le hxIcc.1
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
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro v hv
    have hvIcc : v ∈ Set.Icc A B := by
      simpa only [Set.uIcc_of_le hAB] using hv
    have hvPos : 0 < v := hA.trans_le hvIcc.1
    have hPhase : ContinuousAt
        (fun x : ℝ => tau * Real.log x - 2 * Real.pi * x) v :=
      (continuousAt_const.mul (Real.continuousAt_log hvPos.ne')).sub
        (continuousAt_const.mul continuousAt_id)
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
    have hs := star_gmReflectionPowerWeight sigma v
    rw [Complex.star_def] at hs
    rw [hs]
  have hConj' : (∫ v in A..B, star (f v)) =
      star (∫ v in A..B, f v) := by
    convert hConj using 1 <;> rfl
  rw [← hPointwise, hConj']
  rw [Complex.star_def, Complex.norm_conj]
  exact norm_powerWeighted_gmReflectionIntegral_le htau hA hAB

/-- Positive Fourier modes may be integrated over the common source interval
`[1/m, 2M/m]`.  Its endpoints were chosen so that the support `[1,2]` is
contained in the interval for every `1 ≤ m ≤ M`. -/
theorem gmTraceFourier_pos_eq_interval (cutoff : GMSmoothCutoff)
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
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
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
    have hmMReal : (m : ℝ) ≤ M := by exact_mod_cast hmM
    apply huRange.2.trans
    rw [le_div_iff₀ hmPos]
    nlinarith

/-- Exact source rescaling of a positive Fourier coefficient.  The phase
factor `(mN)^(-it)` contains the logarithmic dependence on the mode outside
the common integral `[N,2NM]`; the remaining occurrence of the mode is only
in the smooth cutoff. -/
theorem gmTraceFourier_pos_rescale (cutoff : GMSmoothCutoff)
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
      have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
      have hNUpper : (N : ℝ) ≤ 2 * N * M := by
        have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hm.trans hmM
        nlinarith [mul_nonneg hNReal.le (sub_nonneg.mpr hMReal)]
      exact hNReal.trans_le
        (Set.uIcc_of_le hNUpper ▸ hv).1
    have hNmComplex : ((((N : ℝ) * m : ℝ) : ℂ)) = ((N * m : ℕ) : ℂ) := by
      norm_num
    have hNmComplexNe : ((N * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNmNat.ne'
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
theorem gmTraceFourier_pos_eq_mellinReflection (cutoff : GMSmoothCutoff)
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

/-- Factoring the common physical scale out of the reflected polynomial.
The equality is exact; no coefficient or cardinality estimate is used. -/
theorem gmPositiveDualDirichletPoly_eq_scale_mul
    (t r : ℝ) {N M : ℕ} (hN : 0 < N) :
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
theorem norm_gmPositiveDualDirichletPoly_eq
    (t r : ℝ) {N M : ℕ} (hN : 0 < N) :
    ‖gmPositiveDualDirichletPoly t N M r‖ =
      ‖gmReflectionDirichletPoly t M (-r)‖ := by
  rw [gmPositiveDualDirichletPoly_eq_scale_mul t r hN, norm_mul]
  have hScale : ‖(N : ℂ) ^ ((((r - t : ℝ) : ℂ) * I))‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hN]
    simp
  rw [hScale, one_mul]

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
      simp only [Complex.star_def, map_neg, map_mul, Complex.conj_ofReal,
        Complex.conj_I]
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

/-- Uniform `T₀⁻¹ᐟ²` stationary bound on the core Mellin window for the
positive reflected phase. -/
theorem norm_gmReflectionIntegral_pos_core_le
    {t r T₀ A B : ℝ} (hT₀ : 4 ≤ T₀) (ht : T₀ ≤ t)
    (hr : |r| ≤ T₀ / 2) (hA : 0 < A) (hAB : A ≤ B) :
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
theorem norm_gmReflectionIntegral_neg_core_le
    {t r T₀ A B : ℝ} (hT₀ : 4 ≤ T₀) (ht : T₀ ≤ t)
    (hr : |r| ≤ T₀ / 2) (hA : 0 < A) (hAB : A ≤ B) :
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

theorem integrable_gmPositiveDualModeIntegrand
    (cutoff : GMSmoothCutoff) (t : ℝ) {N m M : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    Integrable (gmPositiveDualModeIntegrand cutoff t N M m) := by
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hm.trans hmM
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
theorem gmTraceFourier_pos_eq_integral_dualMode (cutoff : GMSmoothCutoff)
    (t : ℝ) {N m M : ℕ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    gmTraceFourier cutoff t ((N : ℝ) * m) =
      ∫ r : ℝ, gmPositiveDualModeIntegrand cutoff t N M m r := by
  rw [gmTraceFourier_pos_eq_mellinReflection cutoff t hN hm hmM]
  unfold gmPositiveDualModeIntegrand
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_smul]

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
      intro m hm
      have hmRange := Finset.mem_Icc.mp hm
      exact gmTraceFourier_pos_eq_integral_dualMode cutoff t hN
        hmRange.1 hmRange.2
    _ = ∫ r : ℝ, ∑ m ∈ Finset.Icc 1 M,
        gmPositiveDualModeIntegrand cutoff t N M m r := by
      symm
      apply MeasureTheory.integral_finsetSum
      intro m hm
      have hmRange := Finset.mem_Icc.mp hm
      exact integrable_gmPositiveDualModeIntegrand cutoff t hN
        hmRange.1 hmRange.2

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
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < N * m := by
    exact Nat.mul_pos hN (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1)
  have hq : ((N * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hmPos.ne'
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

/-- Integrability of the exact cancellation-preserving aggregate integrand.
This is the measurable input needed to split its Mellin integral into a core
and a complementary tail. -/
theorem integrable_norm_gmPositiveDualAggregate
    (cutoff : GMSmoothCutoff) (t : ℝ) {N M : ℕ} (hN : 0 < N) :
    Integrable (fun r : ℝ =>
      (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
          ‖gmPositiveDualDirichletPoly t N M r‖) := by
  have hsum : Integrable (fun r : ℝ =>
      ∑ m ∈ Finset.Icc 1 M,
        gmPositiveDualModeIntegrand cutoff t N M m r) := by
    apply integrable_finsetSum
    intro m hm
    have hmRange := Finset.mem_Icc.mp hm
    exact integrable_gmPositiveDualModeIntegrand cutoff t hN
      hmRange.1 hmRange.2
  have hnorm := hsum.norm
  apply hnorm.congr
  filter_upwards with r
  rw [sum_gmPositiveDualModeIntegrand_eq cutoff t r hN]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity :
    0 < (1 / (2 * Real.pi) : ℝ)), norm_mul, norm_mul]
  ring

/-- Cancellation-preserving norm form of the positive half of Guth--Maynard
Lemma 6.2.  No factor equal to the number of Fourier modes is introduced. -/
theorem norm_gmTraceFourier_pos_sum_le_dualPoly
    (cutoff : GMSmoothCutoff) (t : ℝ) {N M : ℕ} (hN : 0 < N) :
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
      filter_upwards with r
      rw [sum_gmPositiveDualModeIntegrand_eq cutoff t r hN]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity :
        0 < (1 / (2 * Real.pi) : ℝ)), norm_mul, norm_mul]
      ring

/-- The negative Fourier modes satisfy the conjugate cancellation-preserving
bound.  In particular, no factor equal to the number of modes is introduced
on the negative half either. -/
theorem norm_gmTraceFourier_neg_sum_le_dualPoly
    (cutoff : GMSmoothCutoff) (t : ℝ) {N M : ℕ} (hN : 0 < N) :
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
theorem norm_gmTraceFourier_signed_sum_le_dualPoly
    (cutoff : GMSmoothCutoff) (t : ℝ) {N M : ℕ} (hN : 0 < N) :
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

end GuthMaynard.NativeMoment

namespace GuthMaynard.NativeMoment
export MathCollab.Density (
  gmReflectionIntegral
  gmReflectionPrimitive
  gmReflectionRatio
  gmReflectionRatioReal
  hasDerivAt_gmReflectionPrimitive
  hasDerivAt_gmReflectionRatio
  hasDerivAt_gmReflectionRatioReal
  gmReflectionRatio_mul_primitiveDeriv
  gmReflectionIntegral_eq_parts
  norm_gmReflectionPrimitive
  norm_gmReflectionRatio
  norm_gmReflectionIntegrand
  norm_gmReflectionIntegral_le_endpoint_variation
  norm_gmReflectionIntegral_le_left
  norm_gmReflectionIntegral_le_right
  norm_gmReflectionIntegral_le_length_div
  intervalIntegrable_gmReflectionIntegrand)
end GuthMaynard.NativeMoment
