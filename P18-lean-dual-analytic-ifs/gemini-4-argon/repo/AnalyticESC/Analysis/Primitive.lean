module

public import AnalyticESC.Basic

@[expose] public section

/-!
# Integration on a convex complex neighbourhood

Straight-segment integration constructs the primitives used in the ODE-first proof of
Lemma 5.1. Differentiating the integral gives the integrand.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory
open scoped Interval

/-- The integral of `f` on the straight segment from `p` to `z`. -/
noncomputable def segmentPrimitive (f : ℂ → ℂ) (p z : ℂ) : ℂ :=
  ∫ t : ℝ in 0..1, (z - p) * f (p + (t : ℂ) * (z - p))

@[simp] theorem segmentPrimitive_self (f : ℂ → ℂ) (p : ℂ) : segmentPrimitive f p p = 0 := by
  simp [segmentPrimitive]

theorem segment_point_mem {U : Set ℂ} (hU : Convex ℝ U) {p z : ℂ}
    (hp : p ∈ U) (hz : z ∈ U) {t : ℝ} (ht : t ∈ Icc 0 1) :
    p + (t : ℂ) * (z - p) ∈ U := by
  simpa only [Complex.real_smul] using hU.add_smul_sub_mem hp hz ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A holomorphic function on an open convex set has the straight-segment primitive. -/
theorem hasDerivAt_segmentPrimitive {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {p z : ℂ} (hp : p ∈ U) (hz : z ∈ U) :
    HasDerivAt (segmentPrimitive f p) (f z) z := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hUo.mem_nhds hz)
  let P (w : ℂ) (t : ℝ) := p + (t : ℂ) * (w - p)
  let F (w : ℂ) (t : ℝ) := (w - p) * f (P w t)
  let G (w : ℂ) (t : ℝ) := f (P w t) + (w - p) * (deriv f (P w t) * t)
  have hP : ∀ w ∈ closedBall z r, ∀ t ∈ Icc (0 : ℝ) 1, P w t ∈ U :=
    fun w hw t ht => segment_point_mem hUc hp (hball hw) ht
  have hfP : ContinuousOn (fun w : ℂ × ℝ => f (P w.1 w.2)) (closedBall z r ×ˢ Icc 0 1) :=
    hf.continuousOn.comp (by fun_prop) fun w hw => hP w.1 hw.1 w.2 hw.2
  have hfc : ContinuousOn (Function.uncurry F) (closedBall z r ×ˢ Icc 0 1) :=
    ContinuousOn.mul (by fun_prop) hfP
  have hgc : ContinuousOn (Function.uncurry G) (closedBall z r ×ˢ Icc 0 1) :=
    hfP.add (ContinuousOn.mul (by fun_prop)
      (((hf.deriv hUo).continuousOn.comp (by fun_prop) fun w hw => hP w.1 hw.1 w.2 hw.2).mul
        (by fun_prop)))
  obtain ⟨B, hB⟩ := ((isCompact_closedBall z r).prod isCompact_Icc).exists_bound_of_continuousOn hgc
  have hFcont : ∀ w ∈ closedBall z r, ContinuousOn (F w) (Icc 0 1) :=
    fun w hw => hfc.comp (f := fun t : ℝ => (w, t)) (by fun_prop) (fun t ht => ⟨hw, ht⟩)
  have hGcont : ContinuousOn (G z) (Icc 0 1) :=
    hgc.comp (f := fun t : ℝ => (z, t)) (by fun_prop) (fun t ht => ⟨mem_closedBall_self hr.le, ht⟩)
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ closedBall z r,
      HasDerivAt (fun w => F w t) (G w t) w := fun t ht w hw =>
    (((hasDerivAt_id w).sub_const p).mul
      (((hf.differentiableAt (hUo.mem_nhds (hP w hw t ht))).hasDerivAt).comp w
        ((((hasDerivAt_id w).sub_const p).const_mul (t : ℂ)).const_add p))).congr_deriv
      (by dsimp [F, G, P]; ring)
  have hInt := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (F := F) (F' := G) (bound := fun _ => B) (closedBall_mem_nhds z hr)
    (by
      filter_upwards [closedBall_mem_nhds z hr] with w hw
      simpa only [uIoc_of_le zero_le_one] using
        ((hFcont w hw).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc)
    (ContinuousOn.intervalIntegrable (by
      simpa only [uIcc_of_le zero_le_one] using hFcont z (mem_closedBall_self hr.le)))
    (by simpa using (hGcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (Eventually.of_forall fun t ht w hw => hB (w, t) ⟨hw, by simpa using Ioc_subset_Icc_self ht⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht w hw => hder t (by simpa using Ioc_subset_Icc_self ht) w hw)
  refine hInt.2.congr_deriv ?_
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => (t : ℂ) * f (P z t)) (G z t) t := fun t ht => by
    have hfd := (hf.differentiableAt
      (hUo.mem_nhds (hP z (mem_closedBall_self hr.le) t (by simpa using ht)))).hasDerivAt
    convert ((hasDerivAt_id (t : ℂ)).mul
      (hfd.comp (t : ℂ) (((hasDerivAt_id (t : ℂ)).mul_const (z - p)).const_add p))).comp_ofReal using 1 <;>
      dsimp [G, P]; ring
  simpa [P] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hInt.1

/-- A primitive is real along real segments when the integrand is real there. -/
theorem im_segmentPrimitive_eq_zero {U : Set ℂ} (hUc : Convex ℝ U) {f : ℂ → ℂ}
    (hf : ContinuousOn f U) (hreal : ∀ x : ℝ, (x : ℂ) ∈ U → (f x).im = 0)
    {p x : ℝ} (hp : (p : ℂ) ∈ U) (hx : (x : ℂ) ∈ U) :
    (segmentPrimitive f p x).im = 0 := by
  have hcont : ContinuousOn (fun t : ℝ => ((x : ℂ) - p) * f (p + (t : ℂ) * (x - p))) (uIcc 0 1) :=
    continuousOn_const.mul (hf.comp (by fun_prop) fun _ ht =>
      segment_point_mem hUc hp hx (by simpa using ht))
  change Complex.imCLM (∫ t : ℝ in 0..1, ((x : ℂ) - p) * f (p + (t : ℂ) * (x - p))) = 0
  rw [← Complex.imCLM.intervalIntegral_comp_comm hcont.intervalIntegrable,
    intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_,
    intervalIntegral.integral_zero]
  have hm := segment_point_mem hUc hp hx (t := t) (by simpa using ht)
  have he : (p : ℂ) + t * ((x : ℂ) - p) = ((p + t * (x - p) : ℝ) : ℂ) := by push_cast; rfl
  change (((x : ℂ) - p) * f (p + (t : ℂ) * (x - p))).im = 0
  rw [he] at hm
  rw [he, Complex.mul_im, hreal _ hm]
  simp

end AnalyticESC
