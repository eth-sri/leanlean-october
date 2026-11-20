module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

namespace HypoellipticAleksandrov.Analysis

open Filter MeasureTheory Topology
open scoped ENNReal

set_option maxHeartbeats 800000

variable {α E F G ι : Type*} [MeasurableSpace α] {μ ν : Measure α} {l : Filter ι}
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

/-- The squared `L²` norm in terms of an arbitrary representative. -/
theorem integral_sq_eq_norm_toLp_sq {f : α → E} (hf : MemLp f 2 μ) :
    (∫ t, ‖f t‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _),
    ← one_div, ← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

section
variable {f : α → ℝ} (hf : MemLp f 2 μ)
include hf

/-- The ordinary square integral of a real-valued `L²` function. -/
theorem integral_real_sq_eq_norm_toLp_sq :
    (∫ t, f t ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using integral_sq_eq_norm_toLp_sq hf

/-- The ordinary square integral equals the square of the real `L²` seminorm. -/
theorem integral_real_sq_eq_eLpNorm_sq :
    (∫ t, f t ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [integral_real_sq_eq_norm_toLp_sq hf, Lp.norm_toLp]

end

/-- Integrating the squared coordinates adds the corresponding `L²` energies. -/
theorem integral_sum_sq_eq_eLpNorm_sq [Fintype ι] {f : ι → α → ℝ}
    (hf : ∀ i, MemLp (f i) 2 μ) :
    (∫ t, ∑ i, f i t ^ 2 ∂μ) = ∑ i, (eLpNorm (f i) 2 μ).toReal ^ 2 := by
  rw [integral_finsetSum _ (fun i _ => (hf i).integrable_sq)]
  exact Finset.sum_congr rfl fun i _ => integral_real_sq_eq_eLpNorm_sq (hf i)

/-- Continuity of a pointwise operation with a norm bound, even when the
operation varies measurably with the point. No Lipschitz bound is needed. -/
theorem continuous_L2_of_pointwise {Φ : Lp E 2 μ → Lp F 2 μ} {φ : α → E → F}
    [IsFiniteMeasure μ] (hΦ : ∀ f, Φ f =ᵐ[μ] fun t => φ t (f t))
    (hc : ∀ t, Continuous (φ t)) (hφ : ∀ t x, ‖φ t x‖ ≤ ‖x‖) : Continuous Φ := by
  rw [continuous_iff_seqContinuous]
  intro fn f hfn
  let G : ℕ → α → F := fun n t => φ t (fn n t)
  have hm (g : Lp E 2 μ) := (memLp_congr_ae (hΦ g)).mp (Lp.memLp (Φ g))
  have hfui : UnifIntegrable (fun n t => fn n t) 2 μ :=
    unifIntegrable_of_tendsto_Lp (by norm_num) (by norm_num)
      (fun n => Lp.memLp (fn n)) (Lp.memLp f) ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' fn f).1 hfn)
  have hui : UnifIntegrable G 2 μ := by
    apply unifIntegrable_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := unifIntegrable_iff.mp hfui ε hε
    exact ⟨δ, hδ, fun n S hS => (eLpNorm_mono (hm (fn n)).aestronglyMeasurable.restrict
      (fun t => hφ t (fn n t))).trans (hbound n S hS)⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp (hfn.comp hns)).exists_seq_tendsto_ae
  have hpoint : ∀ᵐ t ∂μ, Tendsto (fun n => G (ns (ms n)) t) atTop (𝓝 (φ t (f t))) :=
    hae.mono fun t ht => (hc t).continuousAt.tendsto.comp ht
  have hnorm : Tendsto (fun n => eLpNorm (G (ns (ms n)) - fun t => φ t (f t)) 2 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae (p := 2) (by norm_num) (by norm_num)
      (fun n => (hm (fn (ns (ms n)))).aestronglyMeasurable) (hm f) (hui.comp (ns ∘ ms)) hpoint
  refine ⟨ms, (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).2 (hnorm.congr' ?_)⟩
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards [hΦ (fn (ns (ms n))), hΦ f] with t h₁ h₂
  simp only [Pi.sub_apply, h₁, h₂, Function.comp_apply, G]

/-- A convergent family of seminorms lifts to `Lp`, even if membership is only eventual. -/
theorem exists_tendsto_Lp_of_eLpNorm {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : α → E} {fn : ι → α → E} (hf : MemLp f p μ)
    (hfn : ∀ᶠ n in l, MemLp (fn n) p μ)
    (ht : Tendsto (fun n => eLpNorm (fun x => fn n x - f x) p μ) l (𝓝 0)) :
    ∃ F : ι → Lp E p μ, Tendsto F l (𝓝 (hf.toLp f)) ∧ ∀ᶠ n in l, F n =ᵐ[μ] fn n := by
  classical
  let F n := if h : MemLp (fn n) p μ then h.toLp (fn n) else 0
  have hrep : ∀ᶠ n in l, F n =ᵐ[μ] fn n := hfn.mono fun n hn => by
    simpa only [F, dif_pos hn] using hn.coeFn_toLp
  refine ⟨F, Lp.tendsto_Lp_of_tendsto_eLpNorm _ hf ?_, hrep⟩
  exact ht.congr' (hrep.mono fun n hn => eLpNorm_congr_ae (hn.symm.sub EventuallyEq.rfl))

/-- Lift convergent representatives to classes, using zero at indices where
there is no `MemLp` proof. -/
theorem exists_tendsto_L2_of_sqNorm {f : α → E} {fn : ι → α → E}
    (hf : MemLp f 2 μ) (hfn : ∀ᶠ n in l, MemLp (fn n) 2 μ)
    (hlim : Tendsto (fun n => ∫ t, ‖fn n t - f t‖ ^ 2 ∂μ) l (𝓝 0)) :
    ∃ F : ι → Lp E 2 μ, Tendsto F l (𝓝 (hf.toLp f)) ∧ ∀ᶠ n in l, F n =ᵐ[μ] fn n := by
  refine exists_tendsto_Lp_of_eLpNorm hf hfn ?_
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim.sqrt
  rw [Real.sqrt_zero, ENNReal.ofReal_zero] at h
  refine h.congr' (hfn.mono fun n hn => ?_)
  have hd := hn.sub hf
  change ENNReal.ofReal (√(∫ t, ‖(fn n - f) t‖ ^ 2 ∂μ)) = eLpNorm (fn n - f) 2 μ
  rw [integral_sq_eq_norm_toLp_sq hd, Real.sqrt_sq (norm_nonneg _), Lp.norm_toLp,
    ENNReal.ofReal_toReal hd.eLpNorm_ne_top]

/-- Strong `L²` convergence gives local `L¹` convergence of any continuous
bilinear product. -/
theorem tendsto_integral_norm_bilin_sub_of_tendsto
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (hμ : μ ≤ ν)
    {f : Lp E 2 ν} {g : Lp F 2 ν} {fn : ι → Lp E 2 ν} {gn : ι → Lp F 2 ν}
    (hf : Tendsto fn l (𝓝 f)) (hg : Tendsto gn l (𝓝 g)) :
    Tendsto (fun n => ∫ t, ‖B (fn n t) (gn n t) - B (f t) (g t)‖ ∂μ) l (𝓝 0) := by
  let C : Lp E 2 ν →L[ℝ] Lp F 2 ν →L[ℝ] Lp G 1 ν := B.holderL ν 2 2 1
  have hp : Tendsto (fun n => (fn n, gn n)) l (𝓝 (f, g)) := hf.prodMk_nhds hg
  have hC := (C.continuous₂.tendsto (f, g)).comp hp
  change Tendsto (fun n => C (fn n) (gn n)) l (𝓝 (C f g)) at hC
  have h := tendsto_iff_norm_sub_tendsto_zero.mp hC
  refine squeeze_zero' (.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) ?_ h
  filter_upwards with n
  have hrep : (C (fn n) (gn n) - C f g : Lp G 1 ν) =ᵐ[ν]
      fun t => B (fn n t) (gn n t) - B (f t) (g t) := by
    filter_upwards [Lp.coeFn_sub (C (fn n) (gn n)) (C f g),
      B.coeFn_holder (r := 1) (fn n) (gn n), B.coeFn_holder (r := 1) f g] with t ht hn hfg
    simpa only [Pi.sub_apply, C, ContinuousLinearMap.holderL_apply_apply, hn, hfg] using ht
  rw [L1.norm_eq_integral_norm]
  refine (integral_mono_measure hμ (.of_forall fun _ => norm_nonneg _)
    ((memLp_one_iff_integrable.mp (Lp.memLp (C (fn n) (gn n) - C f g))).norm.congr (hrep.fun_comp norm))).trans_eq ?_
  exact (integral_congr_ae (hrep.fun_comp norm)).symm

/-- Version of bilinear convergence for arbitrary representatives. -/
theorem tendsto_integral_norm_bilin_sub_of_sqNorm
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {f : α → E} {g : α → F} {fn : ι → α → E} {gn : ι → α → F}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfn : ∀ᶠ n in l, MemLp (fn n) 2 μ) (hgn : ∀ᶠ n in l, MemLp (gn n) 2 μ)
    (hF : Tendsto (fun n => ∫ t, ‖fn n t - f t‖ ^ 2 ∂μ) l (𝓝 0))
    (hG : Tendsto (fun n => ∫ t, ‖gn n t - g t‖ ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun n => ∫ t, ‖B (fn n t) (gn n t) - B (f t) (g t)‖ ∂μ) l (𝓝 0) := by
  obtain ⟨F, hF, hFe⟩ := exists_tendsto_L2_of_sqNorm hf hfn hF
  obtain ⟨G, hG, hGe⟩ := exists_tendsto_L2_of_sqNorm hg hgn hG
  refine (tendsto_integral_norm_bilin_sub_of_tendsto B le_rfl hF hG).congr' ?_
  filter_upwards [hFe, hGe] with n hn hm
  apply integral_congr_ae
  filter_upwards [hn, hm, hf.coeFn_toLp, hg.coeFn_toLp] with t h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

/-- `L¹` convergence of real representatives implies convergence against
bounded measurable test functions. -/
theorem tendsto_integral_mul_of_tendsto_integral_abs
    {F : ι → α → ℝ} {f φ : α → ℝ}
    (hF : ∀ᶠ n in l, Integrable (F n) μ) (hf : Integrable f μ)
    (hφ : AEStronglyMeasurable φ μ) (hbound : ∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C)
    (hlim : Tendsto (fun n => ∫ t, |F n t - f t| ∂μ) l (𝓝 0)) :
    Tendsto (fun n => ∫ t, F n t * φ t ∂μ) l (𝓝 (∫ t, f t * φ t ∂μ)) := by
  obtain ⟨C, hC⟩ := hbound
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun _ => norm_nonneg _) ?_
    (show Tendsto (fun n => C * ∫ t, |F n t - f t| ∂μ) l (𝓝 0) by
      simpa only [mul_zero] using tendsto_const_nhds.mul hlim)
  filter_upwards [hF] with n hn
  have hbd := (show ∀ᵐ t ∂μ, ‖φ t‖ ≤ C from .of_forall hC)
  rw [← integral_sub (hn.mul_bdd hφ hbd) (hf.mul_bdd hφ hbd), ← integral_const_mul]
  simp_rw [← sub_mul]
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _) ((hn.sub hf).norm.const_mul C) ?_)
  exact .of_forall fun t => by
    change ‖(F n t - f t) * φ t‖ ≤ C * |F n t - f t|
    rw [norm_mul, mul_comm C, Real.norm_eq_abs (F n t - f t)]
    exact mul_le_mul_of_nonneg_left (hC t) (abs_nonneg _)

end HypoellipticAleksandrov.Analysis
