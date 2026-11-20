module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import HypoellipticAleksandrov.Analysis.L2Convergence

/-!
# Convergence of products of strongly convergent `L²` functions

This file records convergence of scalar product integrals under strong `L²`
convergence and stability of strong `L²` convergence under a fixed `L∞`
multiplier.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace HypoellipticAleksandrov.Analysis

section
variable {α : Type*}

/-- The product integral is the real `L²` pairing, also for arbitrary representatives. -/
theorem integral_mul_eq_inner_L2 [MeasurableSpace α] {μ : Measure α}
    {F G : Lp ℝ 2 μ} {f g : α → ℝ} (hf : f =ᵐ[μ] F) (hg : g =ᵐ[μ] G) :
    (∫ x, f x * g x ∂μ) = inner ℝ F G := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf, hg] with x hfx hgx
  simp only [hfx, hgx, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Cauchy–Schwarz for real `L²` representatives. -/
theorem norm_integral_mul_le_eLpNorm_two [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * g x ∂μ‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  rw [integral_mul_eq_inner_L2 hf.coeFn_toLp.symm hg.coeFn_toLp.symm, ← Lp.norm_toLp f hf,
    ← Lp.norm_toLp g hg, Real.norm_eq_abs]
  exact abs_real_inner_le_norm _ _

/-- A bounded multiplier and two `L²` representatives control a triple product integral. -/
theorem abs_integral_weighted_mul_le_L2 [MeasurableSpace α] {μ : Measure α}
    {F G : Lp ℝ 2 μ} {q f g : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hq : ∀ᵐ x ∂μ, |q x| ≤ C) (hf : f =ᵐ[μ] F) (hg : g =ᵐ[μ] G) :
    |∫ x, q x * f x * g x ∂μ| ≤ C * ‖F‖ * ‖G‖ := by
  have hf₂ := (Lp.memLp F).ae_eq hf.symm
  have hg₂ := (Lp.memLp G).ae_eq hg.symm
  have hint : Integrable (fun x => ‖f x‖ * ‖g x‖) μ := hf₂.norm.integrable_mul hg₂.norm
  have hprod := norm_integral_mul_le_eLpNorm_two hf₂.norm hg₂.norm
  rw [eLpNorm_norm _ hf₂.aestronglyMeasurable, eLpNorm_norm _ hg₂.aestronglyMeasurable,
    eLpNorm_congr_ae hf, eLpNorm_congr_ae hg, ← Lp.norm_def, ← Lp.norm_def] at hprod
  calc
    _ ≤ ∫ x, ‖q x * f x * g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C * (‖f x‖ * ‖g x‖) ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hint.const_mul C)
      filter_upwards [hq] with x hx
      simpa only [norm_mul, Real.norm_eq_abs, mul_assoc] using
        mul_le_mul_of_nonneg_right hx (mul_nonneg (abs_nonneg (f x)) (abs_nonneg (g x)))
    _ ≤ _ := by
      rw [integral_const_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((Real.le_norm_self _).trans hprod) hC

end

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
  have h := (ENNReal.continuous_const_mul ha.eLpNorm_ne_top).continuousAt.tendsto.comp hft
  simp only [Function.comp_apply, mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => ?_)
  simpa only [Pi.smul_apply, Pi.mul_def, smul_eq_mul, mul_sub, Function.comp_apply] using
    (eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (μ := μ) (φ := a)
      (f := fun x => f n x - f₀ x) 2 (by norm_num))

/-- Strong convergence of a family of raw representatives in `L²`. -/
structure StrongL2Limit {ι α : Type*} [MeasurableSpace α] (l : Filter ι)
    (μ : Measure α) (f : ι → α → ℝ) (f₀ : α → ℝ) : Prop where
  eventually_memLp : ∀ᶠ i in l, MemLp (f i) 2 μ
  memLp : MemLp f₀ 2 μ
  tendsto_norm : Tendsto (fun i => eLpNorm (fun x => f i x - f₀ x) 2 μ) l (𝓝 0)

namespace StrongL2Limit

variable {ι α : Type*} [MeasurableSpace α] {l : Filter ι} {μ ν : Measure α}
  {f g : ι → α → ℝ} {f₀ g₀ c : α → ℝ}

section
variable (hf : StrongL2Limit l μ f f₀)
include hf

theorem mono_measure (hle : ν ≤ μ) : StrongL2Limit l ν f f₀ :=
  ⟨hf.eventually_memLp.mono fun _ h => h.mono_measure hle, hf.memLp.mono_measure hle,
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hf.tendsto_norm
      (Eventually.of_forall fun _ => bot_le)
      (Eventually.of_forall fun _ => eLpNorm_mono_measure _ hle)⟩

theorem restrict (S : Set α) :
    StrongL2Limit l (μ.restrict S) f f₀ := hf.mono_measure Measure.restrict_le_self

theorem weight (hc : MemLp c ∞ μ) :
    StrongL2Limit l μ (fun i x => c x * f i x) (fun x => c x * f₀ x) :=
  ⟨hf.eventually_memLp.mono fun _ h => hc.mul' h, hc.mul' hf.memLp,
    tendsto_eLpNorm_mul_sub_mul_of_tendsto_eLpNorm_two c f f₀ hc hf.tendsto_norm⟩

/-- Strong `L²` convergence is preserved by addition. -/
theorem add (hg : StrongL2Limit l μ g g₀) :
    StrongL2Limit l μ (fun i x => f i x + g i x) (fun x => f₀ x + g₀ x) := by
  refine ⟨hf.eventually_memLp.and hg.eventually_memLp |>.mono (fun _ h => h.1.add h.2),
    hf.memLp.add hg.memLp, ?_⟩
  have h := hf.tendsto_norm.add hg.tendsto_norm
  rw [zero_add] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun i => by
      have heq : (fun x => f i x + g i x - (f₀ x + g₀ x)) =
          (fun x => f i x - f₀ x) + (fun x => g i x - g₀ x) := by
        ext x
        simp only [Pi.add_apply]
        ring
      rw [heq]
      exact eLpNorm_add_le (by norm_num))

end

/-- A fixed `L²` representative gives a constant strongly convergent family. -/
theorem const (hf : MemLp f₀ 2 μ) : StrongL2Limit l μ (fun _ => f₀) f₀ :=
  ⟨Eventually.of_forall fun _ => hf, hf, by
    simp only [sub_self]
    change Tendsto (fun _ : ι => eLpNorm (0 : α → ℝ) 2 μ) l (𝓝 0)
    rw [eLpNorm_zero]
    exact tendsto_const_nhds⟩

/-- Multiplication by a fixed scalar preserves strong `L²` convergence. -/
theorem const_mul (hf : StrongL2Limit l μ f f₀) (a : ℝ) :
    StrongL2Limit l μ (fun i x => a * f i x) (fun x => a * f₀ x) :=
  hf.weight (memLp_top_const a)

theorem sub (hf : StrongL2Limit l μ f f₀) (hg : StrongL2Limit l μ g g₀) :
    StrongL2Limit l μ (fun i x => f i x - g i x) (fun x => f₀ x - g₀ x) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using hf.add (hg.const_mul (-1))

/-- Pullback along a measure-preserving map preserves strong `L²` convergence. -/
theorem comp_measurePreserving {β : Type*} [MeasurableSpace β] {ν : Measure β}
    (hf : StrongL2Limit l μ f f₀) {g : β → α} (hg : MeasurePreserving g ν μ) :
    StrongL2Limit l ν (fun i => f i ∘ g) (f₀ ∘ g) := by
  refine ⟨hf.eventually_memLp.mono fun _ h => h.comp_measurePreserving hg,
    hf.memLp.comp_measurePreserving hg, hf.tendsto_norm.congr' ?_⟩
  exact hf.eventually_memLp.mono fun i hi =>
    (eLpNorm_comp_measurePreserving (hi.sub hf.memLp).aestronglyMeasurable hg).symm

/-- Strong `L²` convergence passes through finite sums. -/
theorem finset_sum {κ : Type*} (s : Finset κ) {f : κ → ι → α → ℝ} {f₀ : κ → α → ℝ}
    (hf : ∀ j ∈ s, StrongL2Limit l μ (f j) (f₀ j)) :
    StrongL2Limit l μ (fun i x => ∑ j ∈ s, f j i x) (fun x => ∑ j ∈ s, f₀ j x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨Eventually.of_forall fun _ => MemLp.zero, MemLp.zero, by simpa using tendsto_const_nhds⟩
  | insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using (hf j (Finset.mem_insert_self _ _)).add
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

theorem pairing (hf : StrongL2Limit l μ f f₀) (hg : StrongL2Limit l μ g g₀) :
    Tendsto (fun i => ∫ x, f i x * g i x ∂μ) l (𝓝 (∫ x, f₀ x * g₀ x ∂μ)) := by
  obtain ⟨F, hF, hFe⟩ := exists_tendsto_Lp_of_eLpNorm hf.memLp hf.eventually_memLp hf.tendsto_norm
  obtain ⟨G, hG, hGe⟩ := exists_tendsto_Lp_of_eLpNorm hg.memLp hg.eventually_memLp hg.tendsto_norm
  rw [integral_mul_eq_inner_L2 hf.memLp.coeFn_toLp.symm hg.memLp.coeFn_toLp.symm]
  exact (hF.inner hG).congr' ((hFe.and hGe).mono fun _ h =>
    (integral_mul_eq_inner_L2 h.1.symm h.2.symm).symm)

/-- A bounded weight times a finite sum of squares converges in integral. -/
theorem weighted_sum_sq {κ : Type*} [Fintype κ] {f : κ → ι → α → ℝ} {f₀ : κ → α → ℝ}
    (hf : ∀ j, StrongL2Limit l μ (f j) (f₀ j)) (hc : MemLp c ∞ μ) :
    Tendsto (fun i => ∫ x, c x * ∑ j, f j i x ^ 2 ∂μ) l
      (𝓝 (∫ x, c x * ∑ j, f₀ j x ^ 2 ∂μ)) := by
  have hIntegral {u : κ → α → ℝ} (hu : ∀ j, MemLp (u j) 2 μ) :
      (∫ x, c x * ∑ j, u j x ^ 2 ∂μ) = ∑ j, ∫ x, (c x * u j x) * u j x ∂μ := by
    simp only [Finset.mul_sum, pow_two, ← mul_assoc]
    exact integral_finsetSum _ fun j _ => (hc.mul' (hu j) : MemLp _ 2 μ).integrable_mul (hu j)
  rw [hIntegral (fun j => (hf j).memLp)]
  have h := tendsto_finsetSum Finset.univ fun j _ => ((hf j).weight hc).pairing (hf j)
  refine h.congr' ((Filter.eventually_all.2 fun j => (hf j).eventually_memLp).mono fun i hi => ?_)
  exact (hIntegral hi).symm

end StrongL2Limit

/-- The weighted sum of the squares of a finite `L²` family is integrable. -/
theorem integrable_weighted_sum_sq {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} {c : α → ℝ} {f : ι → α → ℝ} (hc : MemLp c ∞ μ)
    (hf : ∀ i, MemLp (f i) 2 μ) : Integrable (fun z => c z * ∑ i, f i z ^ 2) μ := by
  have hi (i : ι) : Integrable (fun z => c z * f i z * f i z) μ :=
    (hc.mul' (hf i) : MemLp _ 2 μ).integrable_mul (hf i)
  refine (integrable_finsetSum Finset.univ fun i _ => hi i).congr (ae_of_all _ fun z => ?_)
  simp only [Finset.mul_sum, pow_two, mul_assoc]

end HypoellipticAleksandrov.Analysis
