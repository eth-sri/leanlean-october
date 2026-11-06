module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Convergence of products of strongly convergent `L²` functions

This file records convergence of scalar product integrals under strong `L²`
convergence and stability of strong `L²` convergence under a fixed `L∞`
multiplier.
-/

@[expose] public section


open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace HypoellipticAleksandrov.Analysis

private theorem norm_integral_mul_le_eLpNorm_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f (2 : ℝ≥0∞) μ)
    (hg : MemLp g (2 : ℝ≥0∞) μ) :
    ‖∫ x, f x * g x ∂μ‖ ≤
      (eLpNorm f (2 : ℝ≥0∞) μ).toReal *
        (eLpNorm g (2 : ℝ≥0∞) μ).toReal := by
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    constructor <;> norm_num
  have hf' : MemLp f (ENNReal.ofReal (2)) μ := by simp_all
  have hg' : MemLp g (ENNReal.ofReal (2)) μ := by simp_all
  have hraw := integral_mul_norm_le_Lp_mul_Lq hholder hf' hg'
  have hfNorm :
      (eLpNorm f (2) μ).toReal =
        (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    have h := congrArg ENNReal.toReal
      (hf.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top)
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    simp_all
  have hgNorm :
      (eLpNorm g (2) μ).toReal =
        (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    have h := congrArg ENNReal.toReal
      (hg.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top)
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    simp_all
  calc
    ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x * g x‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
      simp
    _ ≤ (∫ x, ‖f x‖ ^ (2) ∂μ) ^ (1 / (2)) *
        (∫ x, ‖g x‖ ^ (2) ∂μ) ^ (1 / (2)) := hraw
    _ = _ := by simp_all

/-- Strong `L²` convergence of both factors implies convergence of their
scalar product integrals. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm_two
    {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι}
    (f g : ι → α → ℝ) (f₀ g₀ : α → ℝ)
    (hf : ∀ᶠ n in l, MemLp (f n) (2 : ℝ≥0∞) μ)
    (hg : ∀ᶠ n in l, MemLp (g n) (2 : ℝ≥0∞) μ)
    (hf₀ : MemLp f₀ (2 : ℝ≥0∞) μ)
    (hg₀ : MemLp g₀ (2 : ℝ≥0∞) μ)
    (hft : Filter.Tendsto
      (fun n => eLpNorm (fun x => f n x - f₀ x) (2 : ℝ≥0∞) μ)
      l (𝓝 0))
    (hgt : Filter.Tendsto
      (fun n => eLpNorm (fun x => g n x - g₀ x) (2 : ℝ≥0∞) μ)
      l (𝓝 0)) :
    Filter.Tendsto
      (fun n => ∫ x, f n x * g n x ∂μ)
      l (𝓝 (∫ x, f₀ x * g₀ x ∂μ)) := by
  let F  := fun n =>
    eLpNorm (fun x => f n x - f₀ x) (2) μ
  let G  := fun n =>
    eLpNorm (fun x => g n x - g₀ x) (2) μ
  have hFt : Tendsto (fun n => (F n).toReal) l (𝓝 0) := by
    simpa only [F, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hft
  have hGt : Tendsto (fun n => (G n).toReal) l (𝓝 0) := by
    simpa only [G, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hgt
  let f₀Norm  := (eLpNorm f₀ (2) μ).toReal
  let g₀Norm  := (eLpNorm g₀ (2) μ).toReal
  let bound  := fun n =>
    (F n).toReal * ((G n).toReal + g₀Norm) + f₀Norm * (G n).toReal
  have hbound : Tendsto bound l (𝓝 0) := by
    simpa only [zero_mul, mul_zero, zero_add, add_zero] using
      (hFt.mul (hGt.add tendsto_const_nhds)).add
        (tendsto_const_nhds.mul hGt)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ?_ hbound
  filter_upwards [hf, hg] with n hfn hgn
  have hfd : MemLp (fun x => f n x - f₀ x) (2) μ := hfn.sub hf₀
  have hgd : MemLp (fun x => g n x - g₀ x) (2) μ := hgn.sub hg₀
  have hgnorm : (eLpNorm (g n) (2) μ).toReal ≤
      (G n).toReal + g₀Norm := by
    have htri : eLpNorm (g n) (2) μ ≤ G n + eLpNorm g₀ 2 μ := by
      have hle := eLpNorm_add_le (f := fun x => g n x - g₀ x) (g := g₀)
        (μ := μ) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      rw [show g n = (fun x => g n x - g₀ x) + g₀ by
        aesop]
      exact hle
    exact ENNReal.toReal_le_add htri hgd.eLpNorm_ne_top hg₀.eLpNorm_ne_top
  have hprodFn : Integrable (fun x => f n x * g n x) μ := hfn.integrable_mul hgn
  have hprod₀ : Integrable (fun x => f₀ x * g₀ x) μ := hf₀.integrable_mul hg₀
  have hfirst : Integrable (fun x => (f n x - f₀ x) * g n x) μ := hfd.integrable_mul hgn
  have hsecond : Integrable (fun x => f₀ x * (g n x - g₀ x)) μ := hf₀.integrable_mul hgd
  have hint :
      (∫ x, f n x * g n x ∂μ) - ∫ x, f₀ x * g₀ x ∂μ =
        (∫ x, (f n x - f₀ x) * g n x ∂μ) +
          ∫ x, f₀ x * (g n x - g₀ x) ∂μ := by
    rw [← integral_sub hprodFn hprod₀, ← integral_add hfirst hsecond]
    ring
  rw [hint]
  calc
    ‖(∫ x, (f n x - f₀ x) * g n x ∂μ) +
        ∫ x, f₀ x * (g n x - g₀ x) ∂μ‖ ≤
        ‖∫ x, (f n x - f₀ x) * g n x ∂μ‖ +
          ‖∫ x, f₀ x * (g n x - g₀ x) ∂μ‖ := norm_add_le _ _
    _ ≤ (F n).toReal * (eLpNorm _ 2 μ).toReal +
        f₀Norm * (G n).toReal := add_le_add (norm_integral_mul_le_eLpNorm_two hfd hgn)
        (norm_integral_mul_le_eLpNorm_two hf₀ hgd)
    _ ≤ bound n := add_le_add
        (mul_le_mul_of_nonneg_left hgnorm ENNReal.toReal_nonneg) le_rfl

/-- Multiplication by a fixed `L∞` scalar preserves strong `L²`
convergence. -/
theorem tendsto_eLpNorm_mul_sub_mul_of_tendsto_eLpNorm_two
    {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι}
    (a : α → ℝ) (f : ι → α → ℝ) (f₀ : α → ℝ)
    (ha : MemLp a ∞ μ)
    (hft : Filter.Tendsto
      (fun n => eLpNorm (fun x => f n x - f₀ x) (2 : ℝ≥0∞) μ)
      l (𝓝 0)) :
    Filter.Tendsto
      (fun n => eLpNorm
        (fun x => a x * f n x - a x * f₀ x)
        (2 : ℝ≥0∞) μ)
      l (𝓝 0) := by
  let C  := (eLpNorm a ∞ μ).toNNReal
  have hC : C = eLpNorm a ∞ μ := ENNReal.coe_toNNReal ha.eLpNorm_ne_top
  have haBound : ∀ᵐ x ∂μ, ‖a x‖ₑ ≤ C := by
    rw [hC, eLpNorm_exponent_top ha.aestronglyMeasurable]
    exact enorm_ae_le_eLpNormEssSup a μ
  have hmeas : ∀ᶠ n in l,
      AEStronglyMeasurable (fun x => f n x - f₀ x) μ := by
    filter_upwards [hft.eventually_lt_const (by simp : (0) < ∞)] with n hn
    exact aestronglyMeasurable_of_eLpNorm_ne_top hn.ne
  have hle (n : ι)
      (hn : AEStronglyMeasurable (fun x => f n x - f₀ x) μ) :
      eLpNorm (fun x => a x * f n x - a x * f₀ x) (2) μ ≤
        C * eLpNorm (fun x => f n x - f₀ x) (2) μ := by
    refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' ?_ ?_ _
    · have heq : (fun x => a x * f n x - a x * f₀ x) =
          a * (fun x => f n x - f₀ x) := (mul_sub _ _ _).symm
      rw [heq]
      exact ha.aestronglyMeasurable.mul hn
    · filter_upwards [haBound] with x hx
      simp only [← mul_sub, enorm_mul]
      gcongr
  have hCt : Tendsto
      (fun n => C *
        eLpNorm (fun x => f n x - f₀ x) (2) μ)
      l (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (ENNReal.continuous_const_mul
        ENNReal.coe_ne_top).continuousAt.tendsto.comp hft
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    hCt
    (Eventually.of_forall fun _ => bot_le)
    (hmeas.mono fun n hn => hle n hn)

end HypoellipticAleksandrov.Analysis
