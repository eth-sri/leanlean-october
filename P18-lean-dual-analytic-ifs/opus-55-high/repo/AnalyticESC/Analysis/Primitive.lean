module

public import AnalyticESC.Basic

public section

set_option hygiene false
local notation "𝖁" => P w t
local notation "𝖀" => w - p
local notation "𝕿" => closedBall z r ×ˢ Icc 0 1
local notation "𝖋" => z - p

local notation "𝖊" => x - p

/-!
# Integration on a convex complex neighbourhood

Straight-segment integration constructs the primitives used in the ODE-first proof of
Lemma 5.1. Differentiating the integral gives the integrand; continuity extends to the
closed neighbourhood when the integrand is continuous there.
-/

namespace AnalyticESC

variable {U : Set ℂ} {f : ℂ → ℂ} {p z : ℂ}

open Set Metric Filter MeasureTheory


/-- The integral of `f` on the straight segment from `p` to `z`. -/
noncomputable def segmentPrimitive (f : ℂ → ℂ) (p z : ℂ) : ℂ :=
  ∫ t : ℝ in 0..1, 𝖋 * f (p + t * 𝖋)

theorem segmentPrimitive_self f p : segmentPrimitive f p p = 0 := by
  simp [segmentPrimitive]

variable (hUc : Convex ℝ U)
include hUc

theorem segment_point_mem (hp : p ∈ U) (hz : z ∈ U) {t : ℝ} (ht : t ∈ Icc 0 1) :
    p + t * 𝖋 ∈ U := by
  simpa only [Complex.real_smul] using hUc.add_smul_sub_mem hp hz ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A holomorphic function on an open convex set has the straight-segment primitive. -/
theorem hasDerivAt_segmentPrimitive (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hp : p ∈ U) (hz : z ∈ U) :
    HasDerivAt (segmentPrimitive f p) (f z) z := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hUo.mem_nhds hz)
  let P w t := p + t * 𝖀
  let F w (t : ℝ) := 𝖀 * f 𝖁
  let G w (t : ℝ) := f 𝖁 + 𝖀 * (deriv f 𝖁 * t)
  have hP : ∀ w ∈ closedBall z r, ∀ t ∈ Icc (0 : ℝ) 1, P w t ∈ U :=
    fun w hw t ht => segment_point_mem hUc hp (hball hw) ht
  have hfc : ContinuousOn (Function.uncurry F) 𝕿 := by
    apply ContinuousOn.mul (by fun_prop)
    exact hf.continuousOn.comp (by fun_prop) (fun w hw => hP w.1 hw.1 w.2 hw.2)
  have hgc : ContinuousOn (Function.uncurry G) 𝕿 := by
    apply ContinuousOn.add
    · exact hf.continuousOn.comp (by fun_prop) (fun w hw => hP w.1 hw.1 w.2 hw.2)
    · apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.mul
      · exact (hf.deriv hUo).continuousOn.comp (by fun_prop)
          (fun w hw => hP w.1 hw.1 w.2 hw.2)
      · fun_prop
  obtain ⟨B, hB⟩ := ((isCompact_closedBall z r).prod isCompact_Icc).exists_bound_of_continuousOn hgc
  have hFcont : ∀ w ∈ closedBall z r, ContinuousOn (F w) (Icc 0 1) :=
    fun w hw => hfc.comp (f := fun t => (w, t)) (by fun_prop) (fun t ht => ⟨hw, ht⟩)
  have hGcont : ContinuousOn (G z) (Icc 0 1) :=
    hgc.comp (f := fun t => (z, t)) (by fun_prop) (fun t ht => ⟨mem_closedBall_self hr.le, ht⟩)
  have hder : ∀ t ∈ Icc 0 1, ∀ w ∈ closedBall z r,
      HasDerivAt (fun w => F w t) (G w t) w := by
    intro t ht w hw
    convert! ((hasDerivAt_id w).sub_const p).mul (((hf.differentiableAt (hUo.mem_nhds (hP w hw t ht))).hasDerivAt).comp w ((((hasDerivAt_id w).sub_const p).const_mul (t : ℂ)).const_add p)) using 1
    dsimp [F, G, P]
    ring
  have hInt := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := 0) (b := 1) (F' := G) (closedBall_mem_nhds z hr)
    (by
      filter_upwards [closedBall_mem_nhds z hr] with w hw
      simpa only [uIoc_of_le zero_le_one] using
        ((hFcont w hw).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc)
    (ContinuousOn.intervalIntegrable (by
      simpa only [uIcc_of_le zero_le_one] using hFcont z (mem_closedBall_self hr.le)))
    (by simpa using (hGcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (Eventually.of_forall fun t ht w hw => hB (w, t) ⟨hw, by grind⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht w hw => hder t (by grind) w hw)
  have hFTC : (∫ t : ℝ in 0..1, G z t) = f z := by
    have hd : ∀ t ∈ uIcc 0 1,
        HasDerivAt (fun t : ℝ => t * f (P z t)) (G z t) t := by
      intro t ht
      convert ((hasDerivAt_id (t : ℂ)).mul (((hf.differentiableAt (hUo.mem_nhds (hP z (mem_closedBall_self hr.le) t (by simp_all)))).hasDerivAt).comp (t : ℂ) (((hasDerivAt_id (t : ℂ)).mul_const 𝖋).const_add p))).comp_ofReal using 1 <;>
        dsimp [G, P]; ring
    simpa [P] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hInt.1
  convert! hInt.2 using 1
  exact hFTC.symm

/-- The integrand in straight-segment integration is continuous. -/
theorem continuousOn_segment_integrand
    (hf : ContinuousOn f U) (hp : p ∈ U) (hz : z ∈ U) :
    ContinuousOn (fun t : ℝ => 𝖋 * f (p + t * 𝖋)) (uIcc 0 1) := by
  apply ContinuousOn.mul continuousOn_const
  apply hf.comp (by fun_prop)
  intro t ht
  exact segment_point_mem hUc hp hz (by simp_all)

/-- A primitive is real along real segments when the integrand is real there. -/
theorem im_segmentPrimitive_eq_zero
    (hf : ContinuousOn f U) (hreal : ∀ x : ℝ, (x : ℂ) ∈ U → (f x).im = 0)
    {p x : ℝ} (hp : (p : ℂ) ∈ U) (hx : (x : ℂ) ∈ U) :
    (segmentPrimitive f p x).im = 0 := by
  have hint : IntervalIntegrable (fun t => 𝖊 *
      f (p + t * 𝖊)) volume 0 1 :=
    (continuousOn_segment_integrand hUc hf hp hx).intervalIntegrable
  change Complex.imCLM (∫ t : ℝ in 0..1, 𝖊 * f (p + t * 𝖊)) = 0
  rw [← Complex.imCLM.intervalIntegral_comp_comm hint]
  calc _ = ∫ _ : ℝ in 0..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hm := segment_point_mem hUc hp hx (t := t) (by simp_all)
        have he : p + t * 𝖊 = ((p + t * 𝖊 : ℝ) : ℂ) := by simp_all
        change (𝖊 * f (p + t * 𝖊)).im = 0
        rw [he] at hm ⊢
        rw [Complex.mul_im, hreal _ hm]
        simp
    _ = 0 := by simp

end AnalyticESC
