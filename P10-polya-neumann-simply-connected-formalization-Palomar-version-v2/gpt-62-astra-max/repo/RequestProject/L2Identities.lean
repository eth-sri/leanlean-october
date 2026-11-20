module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Two integral identities for working with representatives in L². -/

public section

namespace PolyaNeumann
open MeasureTheory Filter

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

/-- The real L² seminorm is the square root of the integral of the squared norm. -/
lemma lpNorm_two_eq {f : α → E} (hf : MemLp f 2 μ) :
    lpNorm f 2 μ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp [Real.sqrt_eq_rpow, one_div]

lemma lpNorm_two_sq {f : α → E} (hf : MemLp f 2 μ) :
    lpNorm f 2 μ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [lpNorm_two_eq hf, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

theorem integral_norm_sq_lp (f : Lp E 2 μ) : ∫ x, ‖f x‖ ^ 2 ∂μ = ‖f‖ ^ 2 :=
  (lpNorm_two_sq (Lp.memLp f)).symm

theorem norm_sq_toLp_eq_integral {f : α → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by rw [Lp.norm_toLp, toReal_eLpNorm, lpNorm_two_sq hf]

lemma integral_norm_mul_le_lpNorm {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤ lpNorm f 2 μ * lpNorm g 2 μ := by
  rw [lpNorm_two_eq hf, lpNorm_two_eq hg]
  simpa [Real.sqrt_eq_rpow] using integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf : MemLp f (ENNReal.ofReal 2) μ) (by simpa using hg : MemLp g (ENNReal.ofReal 2) μ)

lemma norm_integral_mul_le_eLpNorm {A B : α → ℂ} (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) :
    ‖∫ x, A x * B x ∂μ‖ ≤ (eLpNorm A 2 μ).toReal * (eLpNorm B 2 μ).toReal := by
  simp only [toReal_eLpNorm]
  exact (norm_integral_le_integral_norm _).trans (by simpa using integral_norm_mul_le_lpNorm hA hB)

lemma norm_sq_integral_le [NormedSpace ℝ E] [IsFiniteMeasure μ] {f : α → E} (hf : MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ μ.real Set.univ * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h1 : MemLp (fun _ : α => (1 : ℝ)) 2 μ := memLp_const 1
  have h := integral_norm_mul_le_lpNorm h1 hf.norm
  simp only [norm_one, one_mul, norm_norm, lpNorm_norm hf.aestronglyMeasurable] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) ((norm_integral_le_integral_norm f).trans h) 2
  rw [mul_pow, lpNorm_two_sq h1, lpNorm_two_sq hf] at hsq
  simpa using hsq

lemma norm_add_sq_le (x y : E) : ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2).trans add_sq_le

lemma integral_norm_add_sq_le {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, ‖(f + g) x‖ ^ 2 ∂μ ≤ 2 * ∫ x, ‖f x‖ ^ 2 ∂μ + 2 * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  rw [← mul_add, ← integral_add hf.norm.integrable_sq hg.norm.integrable_sq, ← integral_const_mul]
  exact integral_mono (hf.add hg).norm.integrable_sq
    ((hf.norm.integrable_sq.add hg.norm.integrable_sq).const_mul 2) fun _ => norm_add_sq_le ..

lemma norm_sq_intervalIntegral_le [NormedSpace ℝ E] {f : ℝ → E} {s t : ℝ} (hst : s ≤ t)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc s t))) :
    ‖∫ x in s..t, f x‖ ^ 2 ≤ (t - s) * ∫ x in s..t, ‖f x‖ ^ 2 := by
  simpa [intervalIntegral.integral_of_le hst, Measure.real, hst] using norm_sq_integral_le hf

theorem integral_toLp_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) (g : α → ℂ) :
    ∫ x, hf.toLp f x * g x ∂μ = ∫ x, f x * g x ∂μ :=
  integral_congr_ae (hf.coeFn_toLp.mul (EventuallyEq.rfl (f := g)))

end PolyaNeumann
