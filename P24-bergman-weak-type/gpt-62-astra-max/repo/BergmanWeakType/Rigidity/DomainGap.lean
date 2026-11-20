/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.KernelTransform
public import BergmanWeakType.Affine
public import BergmanWeakType.WeakType
public import Mathlib.Topology.Semicontinuity.Basic

/-! # A radial barrier for the rigidity implication

The norm of a disk coordinate has mean strictly less than one, but approaches
one outside compact subsets of the domain. Mixing it into the constant input
reduces the mass relative to the output level unless a kernel row has no
cancellation. In a chart centered at that row, the inverse derivative is
constant, so the chart is affine.
-/
@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter Complex
open scoped NNReal ENNReal Topology ComplexConjugate
namespace BergmanWeakType

variable {Ω : Set ℂ} {K : ℂ → ℂ → ℂ}
local notation "νΩ" => area.restrict Ω
local notation "M" => fun a ↦ ∫⁻ w, ‖K a w‖ₑ ∂νΩ

/-- At the center of a chart an extremal row must be real, hence
constant by the open mapping theorem. -/
private theorem disk_of_center {φ : ℂ → ℂ} (c : Chart disk Ω φ) (sc : IsConnected Ω)
    [IsFiniteMeasure νΩ] (hK : IsBergmanKernel Ω K) (small : M (φ 0) ≤ 1) :
    ∃ a R, 0 < R ∧ Ω = ball a R := by
  let a := φ 0
  have ha : a ∈ Ω := c.bij.mapsTo (by simp)
  have hi := (hK.squareIntegrable a ha).integrable (by norm_num)
  have rep : ∫ w, K a w ∂νΩ = 1 := by simpa using hK.reproduces _ (differentiableOn_const 1) (memLp_const 1) a ha
  have eq : (fun w ↦ (K a w).re) =ᵐ[νΩ] fun w ↦ ‖K a w‖ := by
    apply (integral_eq_iff_of_ae_le hi.re hi.norm (.of_forall fun _ ↦ re_le_norm _)).mp
    rw [integral_re hi,rep]; change 1 = _; apply le_antisymm
    · simpa [rep] using norm_integral_le_integral_norm (μ := νΩ) (K a)
    · apply (ENNReal.ofReal_le_one).mp; rwa [ofReal_integral_norm_eq_lintegral_enorm hi]
  have him : EqOn (fun w ↦ (K w a).im) 0 Ω := by
    apply Measure.eqOn_open_of_ae_eq (μ := area) _ c.dst (continuous_im.comp_continuousOn (hK.holomorphic a ha).continuousOn) continuousOn_const
    filter_upwards [ae_restrict_mem c.dst.measurableSet,eq] with w hw he
    change (K w a).im = 0
    rw [hK.hermitian w hw a ha]; simp [abs_re_eq_norm.mp (by rw [he,abs_of_nonneg (norm_nonneg _)])]
  obtain ⟨d,hd⟩ := ((hK.holomorphic a ha).analyticOnNhd c.dst).eq_const_of_im_eq_const him c.dst sc
  have row (w) (hw : w ∈ disk) : K (φ 0) (φ w) = conj d := (hK.hermitian _ ha _ (c.bij.mapsTo hw)).trans (congrArg _ (hd _ (c.bij.mapsTo hw)))
  have deriv_eq w (hw : w ∈ disk) : deriv φ w = deriv φ 0 := by
    have e := c.center_row hK hw; have e₀ := c.center_row hK (by simp : 0 ∈ disk)
    rw [row _ hw] at e; rw [row _ (by simp)] at e₀
    simpa using congrArg (fun t : ℂ ↦ (conj t)⁻¹) (e.symm.trans e₀)
  have iden : EqOn φ (fun w ↦ φ 0 + deriv φ 0 * w) disk := isOpen_ball.eqOn_of_deriv_eq
    (convex_ball _ _).isPreconnected c.reg.diff (by fun_prop) (fun w hw ↦ by simp [deriv_eq w hw]) (by simp : 0 ∈ disk) (by simp)
  exact ⟨_, _, norm_pos_iff.mpr (c.reg 0 (by simp)), c.bij.image_eq.symm.trans ((image_congr iden).trans (image_affine_disk (c.reg 0 (by simp))))⟩

/-- The lower envelope of the row masses on a compact subdisk is attained,
by Fatou's lemma in the holomorphic variable. -/
private theorem compact_min {φ : ℂ → ℂ} (c : Chart disk Ω φ) (hK : IsBergmanKernel Ω K)
    {R : ℝ} (hR : 0 ≤ R) (h1 : R < 1) : ∃ u ∈ closedBall (0 : ℂ) R,
    IsMinOn (fun v ↦ M (φ v)) (closedBall 0 R) u := by
  let S := closedBall (0 : ℂ) R
  have sub : S ⊆ disk := closedBall_subset_ball h1
  apply LowerSemicontinuousOn.exists_isMinOn (nonempty_closedBall.mpr hR) (isCompact_closedBall _ _)
  apply lowerSemicontinuous_restrict_iff.mp
  intro u; apply lowerSemicontinuousAt_iff_le_liminf.mpr
  apply le_trans _ (lintegral_liminf_le' fun v : S ↦ (hK.squareIntegrable _ (c.bij.mapsTo (sub v.2))).aestronglyMeasurable.aemeasurable.enorm)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem c.dst.measurableSet] with w hw
  have ct := (((hK.holomorphic w hw).comp c.reg.diff c.bij.mapsTo).continuousOn.mono sub).domRestrict
  exact (ct.continuousAt.tendsto.enorm.liminf_eq).symm.le

private theorem row_test (hK : IsBergmanKernel Ω K) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (m : MemLp g 2 νΩ) {a : ℂ} (ha : a ∈ Ω) : ‖g a‖ₑ ≤ ∫⁻ w, ‖K a w‖ₑ * ‖g w‖ₑ ∂νΩ := by
  simpa [hK.reproduces g hg m a ha] using enorm_integral_le_lintegral_enorm (μ := νΩ) (fun w ↦ K a w*g w)

theorem nondisk_gt_one (op : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (sc : IsSimplyConnected Ω) (hK : IsBergmanKernel Ω K) (hn : ¬∃ a R, 0 < R ∧ Ω = ball a R) :
    1 < weakTypeConstant νΩ (domainPositiveProjection Ω K) := by
  obtain ⟨φ,c⟩ := exists_chart op sc hb
  let g := Function.invFunOn φ disk
  have cg := c.symm
  have : IsFiniteMeasure νΩ := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have aeΩ := ae_restrict_mem (μ := area) op.measurableSet
  have vol : νΩ univ ≠ 0 := by simpa using (op.measure_pos area sc.nonempty).ne'
  have hg : ∀ᵐ w ∂νΩ, ‖g w‖ < 1 := aeΩ.mono fun w hw ↦ (mem_disk_iff _).mp (cg.bij.mapsTo hw)
  have lp : MemLp g 2 νΩ := .of_bound (cg.reg.diff.continuousOn.aestronglyMeasurable op.measurableSet) 1 (hg.mono fun _ h ↦ h.le)
  have hi := lp.integrable (by norm_num)
  let m := ∫⁻ w, ‖g w‖ₑ ∂νΩ
  have mlt : m < νΩ univ := by
    simpa [m] using lintegral_strict_mono (Measure.measure_univ_ne_zero.mp vol)
      (aemeasurable_const (b := (1:ℝ≥0∞))) hi.hasFiniteIntegral.ne (hg.mono fun w h ↦ by simpa [← ofReal_norm] using h)
  have divlt {a b : ℝ≥0∞} : a / νΩ univ < b ↔ a < b * νΩ univ := ENNReal.div_lt_iff (.inl vol) (.inl (measure_ne_top _ _))
  obtain ⟨R,hR,hR1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (divlt.mpr (by simpa using mlt) : m / νΩ univ < 1)
  have hR' : R < 1 := by exact_mod_cast hR1
  obtain ⟨u,hu,minimal⟩ := compact_min c hK R.coe_nonneg (NNReal.coe_lt_one.mpr hR')
  have ud := closedBall_subset_ball (NNReal.coe_lt_one.mpr hR') hu
  have strict : 1 < M (φ u) := by
    by_contra! le; apply hn
    exact disk_of_center (c.recentered ud) sc.isPathConnected.isConnected hK (by simpa using le)
  obtain ⟨D,hD,hD'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp strict
  let δ := D-1
  have d : (0:ℝ≥0) < δ := tsub_pos_iff_lt.mpr (by exact_mod_cast hD)
  let L := 1+δ*R
  let f w : ℂ := ((↑(1+δ*‖g w‖₊) : ℝ) : ℂ)
  have hf : Integrable f νΩ := ((integrable_const (1:ℝ)).add (hi.norm.const_mul (δ:ℝ))).ofReal
  have fn w : ‖f w‖ₑ = 1+(δ:ℝ≥0∞)*‖g w‖ₑ  := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]; push_cast; rfl
  have expand (k : ℂ → ℝ≥0∞) (hk : AEMeasurable k νΩ) : (∫⁻ w, k w*‖f w‖ₑ ∂νΩ) =
      (∫⁻ w, k w ∂νΩ) + δ * ∫⁻ w, k w*‖g w‖ₑ ∂νΩ := by
    simp only [fn, mul_add, mul_one, mul_left_comm _ (δ:ℝ≥0∞), lintegral_add_left' hk, lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  have mass : (∫⁻ w, ‖f w‖ₑ ∂νΩ) < (L:ℝ≥0∞) * νΩ univ := by
    rw [show (∫⁻ w, ‖f w‖ₑ ∂νΩ) = νΩ univ + δ * m by simpa [m] using expand 1 aemeasurable_const]
    simp only [L,ENNReal.coe_add,ENNReal.coe_one,ENNReal.coe_mul,add_mul,one_mul,mul_assoc]
    apply ENNReal.add_lt_add_left (measure_ne_top _ _) (ENNReal.mul_lt_mul_right (by positivity : (δ:ℝ≥0∞) ≠ 0) ENNReal.coe_ne_top (divlt.mp hR))
  apply (show 1 < (L:ℝ≥0∞) * νΩ univ / (∫⁻ w, ‖f w‖ₑ ∂νΩ) by rwa [ENNReal.lt_div_iff_mul_lt (.inr ENNReal.one_ne_top) (.inr one_ne_zero),one_mul]).trans_le
  rw [ENNReal.coe_nnreal_eq L]; apply weak_test (by dsimp [L]; positivity : 0 < (L:ℝ)); intro t ht
  refine ⟨f,hf,rfl,aeΩ.mono fun z hz _ ↦ ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.1.le).mpr ht.2).trans_le ?_⟩
  simp only [ENNReal.ofReal_coe_nnreal,domainPositiveProjection,ofReal_norm, expand _ (hK.squareIntegrable z hz).aestronglyMeasurable.aemeasurable.enorm]
  rcases le_or_gt ‖g z‖₊ R with h|h
  · have m' := isMinOn_iff.mp minimal (g z) (by simpa using NNReal.coe_le_coe.mpr h)
    rw [c.bij.invOn_invFunOn.2 hz] at m'
    apply le_trans _ (le_add_right (hD'.le.trans m'))
    exact_mod_cast (show L ≤ D by dsimp [L]; grw [hR'.le]; simpa [δ, add_comm] using (tsub_add_cancel_of_le (by exact_mod_cast hD.le : 1 ≤ D)).le)
  · have one : 1 ≤ M z := by simpa using row_test hK (differentiableOn_const (1:ℂ)) (memLp_const _) hz
    simp only [L,ENNReal.coe_add,ENNReal.coe_one,ENNReal.coe_mul]; exact add_le_add one (mul_le_mul_right ((ENNReal.coe_le_coe.mpr h.le).trans (row_test hK cg.reg.diff lp hz)) _)

end BergmanWeakType
