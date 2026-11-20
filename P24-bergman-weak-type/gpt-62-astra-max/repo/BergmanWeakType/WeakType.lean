/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Measure
public import BergmanWeakType.Weighted.CompactIntegral
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.UnitInterval

/-! # Comparison and test functions for weak type constants -/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter
open scoped ENNReal Topology unitInterval

namespace BergmanWeakType

variable {μ : Measure ℂ} {T S : (ℂ → ℂ) → ℂ → ℝ≥0∞} {C : ℝ≥0∞}

/-- Pointwise domination transfers a weak type estimate. -/
theorem isWeakTypeBound_mono (h : ∀ f z, T f z ≤ S f z)
    (hS : IsWeakTypeBound μ S C) : IsWeakTypeBound μ T C := by
  intro f hf t ht
  apply le_trans (mul_le_mul_right (measure_mono ?_) _) (hS f hf t ht)
  grind

/-- Test the optimal constant at thresholds tending up to `L`. The input may
vary with the threshold, but its mass stays fixed. -/
theorem weak_test [IsFiniteMeasure μ] {B : Set ℂ} {L : ℝ} {m : ℝ≥0∞} (hL : 0 < L)
    (test : ∀ t ∈ Ioo 0 L, ∃ f, Integrable f μ ∧ (∫⁻ z, ‖f z‖ₑ ∂μ) = m ∧
      B ≤ᵐ[μ] {z | ENNReal.ofReal t < T f z}) : ENNReal.ofReal L * μ B / m ≤ weakTypeConstant μ T := by
  apply le_sInf; intro C hC; apply ENNReal.div_le_of_le_mul
  apply le_of_tendsto (x := 𝓝[<] L) (((ENNReal.continuous_mul_const (measure_ne_top _ _)).comp ENNReal.continuous_ofReal).continuousWithinAt)
  filter_upwards [Ioo_mem_nhdsLT hL] with t ht
  obtain ⟨f,hf,rfl,sub⟩ := test t ht
  exact (mul_le_mul_right (measure_mono_ae sub) _).trans (hC f hf t ht.1)

private def blend (t : I) (p : ClosedDisk × ℂ) := (1-(t:ℝ)) • p.1.val + (t:ℝ) • p.2

@[fun_prop] private theorem measurable_blend (t : I) : Measurable (blend t) := by unfold blend; fun_prop

/-- Moving a source by a positive fraction towards an independent uniform disk
point produces an absolutely continuous law, still supported inside the disk. -/
private theorem blend_ac (ν₀ : Measure ClosedDisk) {t : I} (ht : 0 < t) {α : ℝ} (hα : -1 < α) :
    (ν₀.prod diskArea).map (blend t) ≪ weightedArea α := by
  have h0 : (0:ℝ) < t := ht
  have hd := sub_nonneg.mpr t.2.2
  have m := measurable_blend t
  have ac : Measure.QuasiMeasurePreserving (blend t) (ν₀.prod diskArea) area :=
    QuasiMeasurePreserving.prod_of_right m (.of_forall fun a ↦ ((measurePreserving_add_left area ((1-(t:ℝ)) • a.val)).quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_smul area h0.ne')).mono_left (Measure.absolutelyContinuous_restrict ))
  have supp : ∀ᵐ w ∂(ν₀.prod diskArea).map (blend t), w ∈ disk := by
    apply (ae_map_iff m.aemeasurable measurableSet_disk).mpr
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae ae_mem_disk] with p hp
    change blend t p ∈ disk
    simpa only [disk, ClosedDisk, interior_closedBall', blend] using
      (convex_closedBall (0 : ℂ) 1).combo_self_interior_mem_interior p.1.property
        (ball_subset_interior_closedBall hp) hd h0 (by ring)
  apply Measure.AbsolutelyContinuous.trans _ (diskArea_absolutelyContinuous_weightedArea α hα)
  rw [← Measure.restrict_eq_self_of_ae_mem supp]; exact ac.absolutelyContinuous.restrict disk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Probability sources on the closed disk are admissible limiting tests. Kernel
rows are integrated against a smoothed source by testing its Radon–Nikodym density;
compactness gives simultaneous convergence on compact sets of output points. -/
theorem test_source {α : ℝ} (hα : -1 < α) (g : ℂ → ℂ → E)
    (cg : ContinuousOn g.uncurry (disk ×ˢ ClosedDisk)) (mg : ∀ z, StronglyMeasurable (g z)) {T : (ℂ → ℂ) → ℂ → ℝ≥0∞}
    (major : ∀ (f : ℂ → ℝ) z, ‖∫ w, f w • g z w ∂weightedArea α‖ₑ ≤ T (fun w ↦ (f w:ℂ)) z)
    (ν₀ : Measure ClosedDisk) [IsProbabilityMeasure ν₀]
    {B : Set ℂ} (hB : MeasurableSet B) (sub : B ⊆ disk) {L : ℝ} (hL : 0 < L)
    (lev : ∀ z ∈ B, L ≤ ‖∫ w, g z w.val ∂ν₀‖) : ENNReal.ofReal L * weightedArea α B ≤ weakTypeConstant (weightedArea α) T := by
  let μ := weightedArea α
  let := weightedArea_isProbabilityMeasure α hα
  rw [hB.measure_eq_iSup_isCompact (weightedArea α)]
  simp [ENNReal.mul_iSup]; intro K hKB hK
  let P := ν₀.prod diskArea
  let F (t : I) (z : ℂ) := ∫ p, g z (blend t p) ∂P
  have sp : ∀ᵐ p ∂P, p ∈ univ ×ˢ ClosedDisk := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae ae_mem_disk] with p h using ⟨trivial,ball_subset_closedBall h⟩
  have cf : ContinuousOn F.uncurry (univ ×ˢ disk) := by
    apply Weighted.continuousOn_average (isCompact_univ.prod (isCompact_closedBall _ _)) sp
    apply cg.comp (f := fun p : (I × ℂ) × ClosedDisk × ℂ ↦ (p.1.2, blend p.1.1 p.2)) (by dsimp [blend]; fun_prop)
    intro p hp
    exact ⟨hp.1.2, convex_closedBall 0 1 p.2.1.property hp.2.2 (sub_nonneg.mpr p.1.1.2.2) p.1.1.2.1 (by ring)⟩
  have f0 (z : ℂ) : F 0 z = ∫ w, g z w.val ∂ν₀ := by
    simp [F, blend]; simpa using integral_fun_fst  (ν := diskArea) (fun w : ClosedDisk ↦ g z w.val)
  rw [← div_one (ENNReal.ofReal L * μ K)]; apply weak_test hL
  intro ℓ hℓ
  have ev : ∀ᶠ t in 𝓝 0, ∀ z ∈ K, ℓ < ‖F t z‖ := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    apply (cf.continuousAt ((isOpen_univ.prod isOpen_ball).mem_nhds (by tauto))).norm.eventually_const_lt
    change ℓ < ‖F 0 z‖
    rw [f0]; grind
  let := nhdsGT_neBot_of_exists_gt (a := (0:I)) ⟨1,zero_lt_one⟩
  obtain ⟨t, ht, H⟩ := ev.exists_gt
  let ν := P.map (blend t)
  have ac : ν ≪ μ := blend_ac ν₀ ht hα
  let d w := (ν.rnDeriv μ w).toReal
  have di := (integrable_rnDeriv_smul_iff ac (f := fun _ ↦ (1:ℝ))).mpr (integrable_const _)
  simp  at di
  let f w := (d w : ℂ)
  have hf : Integrable f μ := di.ofReal
  have mass : ∫⁻ w, ‖f w‖ₑ ∂μ = 1 := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hf]; simp [f, d, Measure.integral_toReal_rnDeriv ac]
  refine ⟨f,hf,mass,.of_forall fun z hz ↦ ?_⟩
  have hl := H z hz
  have val : F t z = ∫ w, d w • g z w ∂μ := by
    rw [integral_rnDeriv_smul ac, integral_map (by fun_prop) (mg z).aestronglyMeasurable]
  rw [val] at hl
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hℓ.1.le).mpr hl).trans_le (by simpa using major d z)

end BergmanWeakType
