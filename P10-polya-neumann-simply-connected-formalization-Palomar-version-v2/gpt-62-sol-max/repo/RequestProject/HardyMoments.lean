module

public import RequestProject.CirclePullback
public import RequestProject.CircleFourier
public import RequestProject.LocalConformalBoundaryGeometry
public import RequestProject.ExteriorConnected
public import RequestProject.WindingJump
public import Mathlib.MeasureTheory.Integral.Prod

/-! Physical polynomial moments can be transferred directly to circle moments
using a contour in the holomorphic collar. In particular no boundary values of
Cauchy integrals, or regularity of the load beyond L¹, are needed. -/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Metric MeasureTheory Filter Complex
open scoped Real Topology ComplexConjugate

local notation "L" => (2 * Real.pi)
local notation "J" => Icc (0 : ℝ) L
local notation "μ" => volume.restrict (Ioc (0 : ℝ) L)

private lemma cauchy_far {γ f : ℝ → ℂ} (hγ : Continuous γ)
    (hf : Integrable f μ)
    (hm : ∀ n : ℕ, (∫ t, f t * (γ t - γ 0)^n ∂μ) = 0)
    {B : ℝ} (hB : ∀ t ∈ J, ‖γ t - γ 0‖ ≤ B) {w : ℂ} (hw : B < ‖w - γ 0‖) :
    ∫ t, f t / (w - γ t) ∂μ = 0 := by
  let z (t : ℝ) := γ t - γ 0
  let a := w - γ 0
  let q := B / ‖a‖
  have hB0 := (norm_nonneg _).trans (hB 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have ha : 0 < ‖a‖ := hB0.trans_lt hw
  have ha0 := norm_pos_iff.mp ha
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one ha).mpr hw
  have hz : Continuous z := hγ.sub continuous_const
  have hrat (t : ℝ) (ht : t ∈ Ioc 0 L) : ‖z t / a‖ ≤ q := by
    rw [norm_div]
    exact div_le_div_of_nonneg_right (hB t (Ioc_subset_Icc_self ht)) ha.le
  have hs : HasSum (fun n : ℕ => ∫ t, (f t / a) * (z t / a)^n ∂μ)
      (∫ t, f t / (w - γ t) ∂μ) := by
    refine hasSum_integral_of_dominated_convergence (fun n t => (‖f t‖ / ‖a‖) * q^n)
      (fun n => ((hf.aestronglyMeasurable.aemeasurable.div_const a).aestronglyMeasurable).mul
        ((hz.div_const a).pow n).aestronglyMeasurable) (fun n => ?_) ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul, norm_div, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hrat t ht) n) (by positivity)
    · exact Eventually.of_forall fun t => (summable_geometric_of_lt_one hq0 hq1).mul_left _
    · simpa only [tsum_mul_left] using (hf.norm.div_const ‖a‖).mul_const (∑' n : ℕ, q^n)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have h := (hasSum_geometric_of_norm_lt_one ((hrat t ht).trans_lt hq1)).mul_left (f t / a)
      convert h using 1
      rw [← div_eq_mul_inv, div_div]
      have hden : a * (1 - z t / a) = a - z t := by field_simp [ha0]
      rw [hden]
      congr 1
      dsimp [a, z]
      ring
  have hz (n : ℕ) : (∫ t, (f t / a) * (z t / a)^n ∂μ) = 0 := by
    have h (t : ℝ) : (f t / a) * (z t / a)^n = (a⁻¹ * a⁻¹ ^ n) * (f t * z t^n) := by
      simp only [div_eq_mul_inv, mul_pow]
      ring
    simp_rw [h, integral_const_mul]
    change (a⁻¹ * a⁻¹ ^ n) * (∫ t, f t * (γ t - γ 0)^n ∂μ) = 0
    rw [hm, mul_zero]
  simpa only [hz, tsum_zero] using hs.tsum_eq.symm

private lemma cauchy_differentiableAt {γ f : ℝ → ℂ} (hγ : Continuous γ)
    (hf : Integrable f μ) {w : ℂ} (hw : ∀ t ∈ J, γ t ≠ w) :
    DifferentiableAt ℂ (fun v => ∫ t, f t / (v - γ t) ∂μ) w := by
  obtain ⟨d, hd, hsep⟩ := exists_pos_le_norm_sub hγ hw
  have hnorm (t : ℝ) (ht : t ∈ Ioc 0 L) (v : ℂ) (hv : v ∈ ball w (d / 2)) :
      d / 2 ≤ ‖v - γ t‖ := by
    have h := dist_triangle (γ t) v w
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev (γ t) v] at h
    rw [mem_ball, dist_eq_norm] at hv
    linarith [hsep t (Ioc_subset_Icc_self ht)]
  have hmeas (v : ℂ) : AEStronglyMeasurable (fun t => f t / (v - γ t)) μ :=
    (hf.aestronglyMeasurable.aemeasurable.div (measurable_const.sub hγ.measurable).aemeasurable).aestronglyMeasurable
  have hwI : w ∈ ball w (d / 2) := mem_ball_self (half_pos hd)
  have hi : Integrable (fun t => f t / (w - γ t)) μ := by
    apply (hf.norm.div_const (d / 2)).mono' (hmeas w)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (half_pos hd) (hnorm t ht w hwI)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun v t => -f t / (v - γ t)^2) (ball_mem_nhds w (half_pos hd))
    (Eventually.of_forall hmeas) hi
    (hf.aestronglyMeasurable.aemeasurable.neg.div
      ((measurable_const.sub hγ.measurable).pow_const 2).aemeasurable).aestronglyMeasurable
    ?_ (hf.norm.div_const ((d / 2)^2)) ?_).2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro v hv
    rw [norm_div, norm_neg, norm_pow]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (pow_le_pow_left₀ (half_pos hd).le (hnorm t ht v hv) 2)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro v hv
    simpa [Pi.div_def] using (hasDerivAt_const v (f t)).div ((hasDerivAt_id v).sub_const (γ t))
      (norm_pos_iff.mp ((half_pos hd).trans_le (hnorm t ht v hv)))

private lemma cauchy_exterior {Ω : Set ℂ} {γ f : ℝ → ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : Continuous γ) (him : γ '' J = frontier Ω)
    (hf : Integrable f μ) (hm : ∀ n : ℕ, (∫ t, f t * (γ t - γ 0)^n ∂μ) = 0) :
    ∀ w ∉ closure Ω, ∫ t, f t / (w - γ t) ∂μ = 0 := by
  have hfc := him ▸ isPreconnected_Icc.image _ hγ.continuousOn
  have hconn := isConnected_compl_closure_of_frontier hb hL hfc
  have hdiff : DifferentiableOn ℂ (fun w => ∫ t, f t / (w - γ t) ∂μ) (closure Ω)ᶜ := by
    intro w hw
    refine (cauchy_differentiableAt hγ hf (w := w) fun t ht he => hw ?_).differentiableWithinAt
    rw [← he]
    apply frontier_subset_closure
    rw [← him]
    exact mem_image_of_mem γ ht
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := J)
    (hγ.sub (continuous_const (y := γ 0))).continuousOn
  obtain ⟨R, hR⟩ := hb.closure.subset_ball (γ 0)
  let d := max (max B R) 0 + 1
  let w := γ 0 + (d : ℂ)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hn : ‖w - γ 0‖ = d := by simp [w, hd]
  have hfar : B < ‖w - γ 0‖ := by rw [hn]; dsimp [d]; grind
  have hw : w ∈ (closure Ω)ᶜ := by
    intro h
    have := hR h
    rw [mem_ball, dist_eq_norm, hn] at this
    dsimp [d] at this
    grind
  apply (hdiff.analyticOnNhd isClosed_closure.isOpen_compl).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hconn.isPreconnected hw
  filter_upwards [(isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hfar]
    with v hv
  exact cauchy_far hγ hf hm hB hv

private lemma circle_moment_of_exterior {F : ℂ → ℂ} {f : ℝ → ℂ} {r : ℝ} (hr : 1 < r)
    (hF : DifferentiableOn ℂ F (closedBall 0 r)) (hi : InjOn F (closedBall 0 r))
    (hn : ∀ x ∈ closedBall (0 : ℂ) 1, deriv F x ≠ 0) (hf : Integrable f μ)
    (hzero : ∀ z ∈ sphere (0 : ℂ) r, (∫ t, f t / (F z - F (circleMap 0 1 t)) ∂μ) = 0)
    (n : ℕ) : (∫ t, f t * ((circleMap 0 1 t)^n / deriv F (circleMap 0 1 t)) ∂μ) = 0 := by
  let z := circleMap 0 r
  let x := circleMap 0 1
  have hr0 : 0 ≤ r := by linarith
  have hz (s : ℝ) : z s ∈ sphere 0 r := circleMap_mem_sphere _ hr0 _
  have hx (t : ℝ) : x t ∈ closedBall 0 1 := circleMap_mem_closedBall _ zero_le_one _
  let K (s t : ℝ) := (z s * I) * ((z s)^n / (F (z s) - F (x t)))
  have hner (s t : ℝ) : F (z s) - F (x t) ≠ 0 := by
    refine sub_ne_zero.mpr fun h => ?_
    have he := hi (sphere_subset_closedBall (hz s)) (closedBall_subset_closedBall hr.le (hx t)) h
    have hs := hz s
    rw [he] at hs
    exact (not_le_of_gt hr) ((mem_sphere.mp hs).ge.trans (mem_closedBall.mp (hx t)))
  have hc₁ :=
    hF.continuousOn.comp_continuous (continuous_circleMap _ _) (fun s => sphere_subset_closedBall (hz s))
  have hc₂ :=
    hF.continuousOn.comp_continuous (continuous_circleMap _ _) (fun t => closedBall_subset_closedBall hr.le (hx t))
  have hKc : Continuous (Function.uncurry K) := by
    exact ((((continuous_circleMap 0 r).comp continuous_fst).mul continuous_const).mul
      ((((continuous_circleMap 0 r).comp continuous_fst).pow n).div
        ((hc₁.comp continuous_fst).sub (hc₂.comp continuous_snd)) (fun p => hner p.1 p.2)))
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := J ×ˢ J) hKc.continuousOn
  have hg := hf.comp_snd μ
  have hKi : Integrable (Function.uncurry fun s t => K s t * f t) ((μ).prod μ) := by
    apply (hg.norm.const_mul M).mono' (hKc.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    change ‖K p.1 p.2 * f p.2‖ ≤ M * ‖f p.2‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM p ⟨Ioc_subset_Icc_self hp.1, Ioc_subset_Icc_self hp.2⟩)
      (norm_nonneg _)
  have hout (s : ℝ) : (∫ t, K s t * f t ∂μ) = 0 := by
    have he (t : ℝ) : K s t * f t = (z s * I * z s^n) * (f t / (F (z s) - F (x t))) := by
      simp only [K]
      ring
    simp_rw [he, integral_const_mul]
    change (z s * I * z s^n) * (∫ t, f t / (F (z s) - F (circleMap 0 1 t)) ∂μ) = 0
    rw [hzero _ (hz s), mul_zero]
  have hin (t : ℝ) : (∫ s, K s t * f t ∂μ) = (2 * π * I) *
      (f t * (x t^n / deriv F (x t))) := by
    have hs := circle_pullback_pole (closedBall_subset_ball hr (hx t)) hF hi (hn _ (hx t)) (g := fun z => z^n) (differentiableOn_id.pow n)
    simp only [circleIntegral, deriv_circleMap, smul_eq_mul,
      intervalIntegral.integral_of_le Real.two_pi_pos.le, x] at hs
    rw [integral_mul_const]
    change (∫ s, (circleMap 0 r s * I) * ((circleMap 0 r s)^n /
      (F (circleMap 0 r s) - F (circleMap 0 1 t))) ∂μ) * f t = _
    rw [hs]
    ring
  have h := integral_integral_swap hKi
  simp only [hout, hin, integral_zero, integral_const_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by simp [Real.pi_ne_zero])

/-- The complex moments of an integrable physical density imply that its
positive circle coefficients vanish. The collar supplies an exterior Cauchy contour. -/
theorem localConformal_physicalMoments_nonpositive {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
    (H : ℝ → ℂ) (hH : IntervalIntegrable H volume 0 L)
    (hmom : ∀ m : ℕ, (∫ t in (0 : ℝ)..L,
      (conj (deriv (physicalCircleTrace F) t) * H t) *
        (conj (physicalCircleTrace F t) - conj (physicalCircleTrace F 0))^m) = 0) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  have hc := coords.holomorphic_collar
  let U := ball (0 : ℂ) coords.radius ∩ coords.model.source
  have hU : IsOpen U := isOpen_ball.inter coords.model.open_source
  have hsub : closedBall (0 : ℂ) 1 ⊆ U := fun _ hx =>
    ⟨closedBall_subset_ball coords.one_lt_radius hx, coords.source hx⟩
  obtain ⟨ε, hε, hεU⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hU hsub
  rw [thickening_closedBall hε zero_le_one] at hεU
  let r := 1 + ε / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hrU : closedBall (0 : ℂ) r ⊆ U :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans hεU
  have hF := hc.mono (fun z hz => (hrU hz).1)
  have hiU : InjOn F U := coords.model_eq ▸ coords.model.injOn.mono inter_subset_right
  have hi := hiU.mono hrU
  have hn : ∀ x ∈ closedBall (0 : ℂ) 1, deriv F x ≠ 0 := fun _ => coords.deriv_ne_zero_closed
  let γ := physicalCircleTrace F
  let f (t : ℝ) := deriv γ t * conj (H t)
  have hγ := coords.trace_contDiff
  have hHc : IntervalIntegrable (fun t => conj (H t)) volume 0 L :=
    ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hH.1,
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hH.2⟩
  have hf : Integrable f μ := (hHc.continuousOn_mul hγ.continuous_deriv_one.continuousOn).1
  have hm (m : ℕ) : (∫ t, f t * (γ t - γ 0)^m ∂μ) = 0 := by
    have he := congrArg (fun q : ℂ => conj q) (hmom m)
    change conj (∫ t in (0 : ℝ)..L,
      (conj (deriv γ t) * H t) * (conj (γ t) - conj (γ 0))^m) = conj (0 : ℂ) at he
    rw [← intervalIntegral.intervalIntegral_conj,
      intervalIntegral.integral_of_le Real.two_pi_pos.le] at he
    simpa only [map_zero, map_mul, map_pow, map_sub, conj_conj, f] using he
  have hext := cauchy_exterior coords.bounded coords.lipschitz hγ.continuous
    (localConformal_circleTrace_image_frontier coords.one_lt_radius F coords.smooth
      coords.injOn_closed coords.lipschitz.1.1) hf hm
  have hcau : ∀ z ∈ sphere (0 : ℂ) r, (∫ t, f t / (F z - γ t) ∂μ) = 0 := by
    intro z hz
    apply hext (F z)
    rw [← localConformal_closedDisk_image_eq_closure coords.one_lt_radius F coords.smooth]
    rintro ⟨y, hy, hyz⟩
    have he := hi (closedBall_subset_closedBall hr.le hy) (sphere_subset_closedBall hz) hyz
    rw [he, mem_closedBall, mem_sphere.mp hz] at hy
    linarith
  have hcirc (m : ℕ) : (∫ t, conj (H t) * (circleMap 0 1 t)^(m+1) ∂μ) = 0 := by
    have h := circle_moment_of_exterior hr hF hi hn hf hcau m
    have he (t : ℝ) : f t * ((circleMap 0 1 t)^m / deriv F (circleMap 0 1 t)) =
        I * (conj (H t) * (circleMap 0 1 t)^(m+1)) := by
      dsimp only [f]
      rw [coords.trace_deriv, pow_succ]
      field_simp [hn _ (circleMap_mem_closedBall _ zero_le_one _)]
    simp only [he, integral_const_mul] at h
    exact (mul_eq_zero.mp h).resolve_left I_ne_zero
  intro n hnpos
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = ((m + 1 : ℕ) : ℤ) := ⟨n.toNat - 1, by omega⟩
  have h : fourierCoeffOn Real.two_pi_pos (fun t => conj (H t)) (-((m + 1 : ℕ) : ℤ)) = 0 := by
    rw [fourierCoeffOn_eq_integral]
    have he (t : ℝ) : fourier (T := L) ((m + 1 : ℕ) : ℤ) (t : AddCircle L) • conj (H t) =
        conj (H t) * (circleMap 0 1 t)^(m+1) := by
      rw [smul_eq_mul, mul_comm, fourier_coe_two_pi, circleMap_zero_pow]
      simp [circleMap_zero]
    have hi : (∫ t, fourier (T := L) ((m + 1 : ℕ) : ℤ) (t : AddCircle L) • conj (H t) ∂μ) = 0 := by
      simpa only [he] using hcirc m
    simpa only [fourier_coe_apply, sub_zero, neg_neg,
      intervalIntegral.integral_of_le Real.two_pi_pos.le, smul_zero] using
      congrArg (fun q : ℂ => (1 / L : ℝ) • q) hi
  rw [fourierCoeffOn_conj, neg_neg] at h
  exact (map_eq_zero_iff _ (starRingEnd ℂ).injective).mp h

end PolyaNeumann
