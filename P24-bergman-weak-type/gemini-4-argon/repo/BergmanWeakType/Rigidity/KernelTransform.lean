/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.RiemannMapping
public import BergmanWeakType.KernelIntegrability
public import BergmanWeakType.Weighted.PolarIntegral
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Metric Function Complex Real
open scoped ComplexConjugate Topology ENNReal Real

namespace BergmanWeakType

/-- An injective function on an open complex neighborhood cannot be locally constant. -/
theorem not_eventually_constant_of_injOn {U : Set ℂ} {f : ℂ → ℂ} {x : ℂ}
    (hU : IsOpen U) (hf : InjOn f U) (hx : x ∈ U) :
    ¬ ∀ᶠ z in 𝓝 x, f z = f x := fun h ↦
  not_isOpen_singleton x <| isOpen_singleton_of_finite_mem_nhds x
    (by filter_upwards [h, hU.eventually_mem hx] with z hz hzU using hf hzU hx hz)
    (finite_singleton x)

/-- A set-theoretic inverse of a holomorphic bijection between open complex sets is holomorphic. -/
theorem differentiableOn_inverse {U V : Set ℂ} {f g : ℂ → ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
    (hinv : InvOn g f U V) (hgmap : MapsTo g V U) : DifferentiableOn ℂ g V := by
  have hcont (y : ℂ) (hy : y ∈ V) : ContinuousAt g y := by
    have hx := hgmap hy
    have hopen : 𝓝 (f (g y)) ≤ Filter.map f (𝓝 (g y)) :=
      (hf.analyticAt (hU.mem_nhds hx)).eventually_constant_or_nhds_le_map_nhds.resolve_left
        (not_eventually_constant_of_injOn hU hinv.1.injOn hx)
    rw [hinv.2 hy] at hopen
    exact (Filter.map_mono hopen).trans <| Filter.map_map.trans_le <|
      tendsto_id.congr' <| (hU.eventually_mem hx).mono fun z hz ↦ (hinv.1 hz).symm
  intro y hy
  apply DifferentiableAt.differentiableWithinAt
  apply AnalyticAt.differentiableAt
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ (hcont y hy)
  have hx := hgmap hy
  have hcrit : ∀ᶠ z in 𝓝[≠] g y, deriv f z ≠ 0 := by
    rcases (hf.analyticOnNhd hU).deriv (g y) hx |>.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_ball.mem_iff.mp (hzero.and (hU.eventually_mem hx))
      refine (not_eventually_constant_of_injOn hU hinv.1.injOn hx ?_).elim
      filter_upwards [ball_mem_nhds (g y) hr] with z hz
      exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (g y) r).isPreconnected
        (hf.mono fun w hw ↦ (hrU hw).2) (fun w hw ↦ (hrU hw).1) hz (mem_ball_self hr)
    · exact hne
  rw [eventually_nhdsWithin_iff] at hcrit
  filter_upwards [((hcont y hy).tendsto.eventually hcrit).filter_mono nhdsWithin_le_nhds,
    (hV.eventually_mem hy).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzV hzneq
  have hneq : g z ≠ g y := fun heq ↦ hzneq ((hinv.2 hzV).symm.trans ((congrArg f heq).trans (hinv.2 hy)))
  exact ((hf.differentiableAt (hU.mem_nhds (hgmap hzV))).hasDerivAt.of_local_left_inverse
    (hcont z hzV) (hz hneq) ((hV.eventually_mem hzV).mono fun w hw ↦ hinv.2 hw)).differentiableAt

/-- A holomorphic bijection between open complex sets has no critical points. -/
theorem deriv_ne_zero_of_bijOn {U V : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
    (hbij : BijOn f U V) {x : ℂ} (hx : x ∈ U) : deriv f x ≠ 0 := by
  let g := invFunOn f U
  have hinv : InvOn g f U V := hbij.invOn_invFunOn
  have hg := differentiableOn_inverse hU hV hf hinv (hinv.1.mapsTo hbij.surjOn)
  have hid : HasDerivAt (fun z : ℂ ↦ z) (deriv g (f x) * deriv f x) x :=
    ((hg.differentiableAt (hV.mem_nhds (hbij.mapsTo hx))).hasDerivAt.comp x
      (hf.differentiableAt (hU.mem_nhds hx)).hasDerivAt).congr_of_eventuallyEq
      ((hU.eventually_mem hx).mono fun z hz ↦ (hinv.1 hz).symm)
  exact right_ne_zero_of_mul_eq_one (hid.unique (hasDerivAt_id x))

/-- A complex derivative scales real area by its squared norm. -/
theorem det_complex_derivative (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

theorem area_lintegral_image_eq {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U)
    (g : ℂ → ℝ≥0∞) :
    ∫⁻ z in φ '' U, g z ∂area =
      ∫⁻ w in U, ENNReal.ofReal (‖deriv φ w‖ ^ 2) * g (φ w) ∂area := by
  simp only [area, Measure.restrict_smul, lintegral_smul_measure]
  congr 1
  simpa only [det_complex_derivative, abs_sq] using
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU.measurableSet
      (fun w hw ↦ ((hφ.differentiableAt (hU.mem_nhds hw)).hasDerivAt.hasFDerivAt
        |>.restrictScalars ℝ).hasFDerivWithinAt) hinj g

theorem area_integral_image_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (g : ℂ → E) :
    ∫ z in φ '' U, g z ∂area = ∫ w in U, (‖deriv φ w‖ ^ 2 : ℝ) • g (φ w) ∂area := by
  simp only [area, Measure.restrict_smul, integral_smul_measure]
  congr 1
  simpa only [det_complex_derivative, abs_sq] using
    integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet
      (fun w hw ↦ ((hφ.differentiableAt (hU.mem_nhds hw)).hasDerivAt.hasFDerivAt
        |>.restrictScalars ℝ).hasFDerivWithinAt) hinj g

/-- The Bergman kernel of a domain, expressed in any biholomorphic disk coordinates. -/
theorem IsBergmanKernel.disk_coordinate_formula {Ω : Set ℂ} {K : ℂ → ℂ → ℂ}
    {φ ψ : ℂ → ℂ} (hK : IsBergmanKernel Ω K) (hΩ : IsOpen Ω)
    (hφ : DifferentiableOn ℂ φ disk) (hψ : DifferentiableOn ℂ ψ Ω)
    (hbij : BijOn φ disk Ω) (hinv : InvOn ψ φ disk Ω)
    {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    K (φ z) (φ w) = kernel z w / (deriv φ z * star (deriv φ w)) := by
  have hcol {U : Set ℂ} {L : ℂ → ℂ → ℂ} (hL : IsBergmanKernel U L) (hU : MeasurableSet U)
      {u : ℂ} (hu : u ∈ U) : MemLp (fun v ↦ L v u) 2 (area.restrict U) :=
    (memLp_congr_ae ((ae_restrict_mem hU).mono fun v hv ↦ (hL.hermitian v hv u hu).symm)).mp
      (hL.squareIntegrable u hu).star
  have hp_memLp {U V : Set ℂ} {g f : ℂ → ℂ} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
      (hb : BijOn g U V) (hf : ContinuousOn f V) (hfi : MemLp f 2 (area.restrict V)) :
      MemLp (fun v ↦ deriv g v * f (g v)) 2 (area.restrict U) := by
    have hc : ContinuousOn (fun v ↦ deriv g v * f (g v)) U :=
      (hg.analyticOnNhd hU).deriv.continuousOn.mul (hf.comp hg.continuousOn hb.mapsTo)
    apply (memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable hU.measurableSet)).mpr
    have himage : IntegrableOn (fun v ↦ ‖f v‖ ^ 2) (g '' U) area := by
      rw [hb.image_eq]; exact hfi.integrable_norm_pow (by decide)
    simp only [IntegrableOn, area, Measure.restrict_smul] at himage ⊢
    rw [integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top] at himage ⊢
    simpa only [IntegrableOn, det_complex_derivative, abs_sq, norm_mul, mul_pow, smul_eq_mul] using
      (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU.measurableSet
        (fun v hv ↦ ((hg.differentiableAt (hU.mem_nhds hv)).hasDerivAt.hasFDerivAt
          |>.restrictScalars ℝ).hasFDerivWithinAt) hb.injOn (fun v ↦ ‖f v‖ ^ 2)).mp himage
  have hinv_mul {u : ℂ} (hu : u ∈ disk) : deriv ψ (φ u) * deriv φ u = 1 :=
    (((hψ.differentiableAt (hΩ.mem_nhds (hbij.mapsTo hu))).hasDerivAt.comp u
      (hφ.differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt).congr_of_eventuallyEq
      ((isOpen_ball.eventually_mem hu).mono fun _ hv ↦ (hinv.1 hv).symm)).unique (hasDerivAt_id u)
  let P (u v : ℂ) : ℂ := deriv φ u * K (φ u) (φ v) * star (deriv φ v)
  have hψbij : BijOn ψ Ω disk := hbij.symm hinv.symm
  have hφderiv := (hφ.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hψderiv := (hψ.analyticOnNhd hΩ).deriv.differentiableOn
  have hpull : IsBergmanKernel disk P := by
    refine ⟨fun u hu ↦ (hφderiv.mul ((hK.holomorphic (φ u) (hbij.mapsTo hu)).comp hφ hbij.mapsTo)).mul_const _,
      fun u hu v hv ↦ by
        simp only [P, star_mul, star_star, hK.hermitian (φ v) (hbij.mapsTo hv) (φ u) (hbij.mapsTo hu)]
        ring,
      fun u hu ↦ ?_, fun f hf hfi u hu ↦ ?_⟩
    · refine (memLp_congr_ae ?_).mp ((hp_memLp isOpen_ball hφ hbij
        (hK.holomorphic (φ u) (hbij.mapsTo hu)).continuousOn
        (hcol hK hΩ.measurableSet (hbij.mapsTo hu))).star.const_mul (deriv φ u))
      filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with v hv
      simp only [Pi.star_apply, star_mul, P]
      rw [← hK.hermitian (φ u) (hbij.mapsTo hu) (φ v) (hbij.mapsTo hv)]; ring
    · let F : ℂ → ℂ := fun v ↦ deriv ψ v * f (ψ v)
      have hrep := hK.reproduces F (hψderiv.mul (hf.comp hψ hψbij.mapsTo))
        (hp_memLp hΩ hψ hψbij hf.continuousOn hfi) (φ u) (hbij.mapsTo hu)
      have hchange := area_integral_image_eq (U := disk) isOpen_ball hφ hbij.injOn (fun v ↦ K (φ u) v * F v)
      rw [hbij.image_eq] at hchange
      have heq : (∫ v, K (φ u) v * F v ∂area.restrict Ω) =
          ∫ v, K (φ u) (φ v) * star (deriv φ v) * f v ∂area.restrict disk := by
        rw [hchange]
        refine integral_congr_ae ((ae_restrict_mem isOpen_ball.measurableSet).mono fun v hv ↦ ?_)
        dsimp only [F]
        rw [hinv.1 hv, Complex.real_smul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
        simp only [starRingEnd_apply]
        calc
          _ = (deriv ψ (φ v) * deriv φ v) * (K (φ u) (φ v) * star (deriv φ v) * f v) := by ring
          _ = _ := by rw [hinv_mul hv, one_mul]
      calc
        (∫ v, P u v * f v ∂area.restrict disk) =
            deriv φ u * ∫ v, K (φ u) (φ v) * star (deriv φ v) * f v ∂area.restrict disk := by
          rw [← integral_const_mul]
          exact integral_congr_ae (Eventually.of_forall fun _ ↦ by simp only [P]; ring)
        _ = deriv φ u * F (φ u) := by rw [← heq, hrep]
        _ = f u := by
          dsimp only [F]
          rw [hinv.1 hu]
          calc _ = (deriv ψ (φ u) * deriv φ u) * f u := by ring
               _ = _ := by rw [hinv_mul hu, one_mul]
  have hL : IsBergmanKernel disk kernel := by
    refine ⟨fun u hu ↦ (((differentiableOn_const 1).sub
        (differentiableOn_id.mul_const (star u))).inv
        (fun v hv ↦ kernel_denominator_ne_zero hv hu)).pow 2,
      fun u _ v _ ↦ by simp [kernel, star_mul],
      fun u hu ↦ by
        change MemLp (kernel u) 2 diskArea
        exact MemLp.of_bound (aestronglyMeasurable_kernel hu) ((1 - ‖u‖)⁻¹ ^ 2)
          (ae_mem_disk.mono fun _ hv ↦ norm_kernel_le hu hv),
      fun f hf hfi u hu ↦ ?_⟩
    change MemLp f 2 diskArea at hfi
    have hfi' : Integrable f diskArea := hfi.integrable (by norm_num)
    have hu1 : ‖u‖ < 1 := (mem_disk_iff u).mp hu
    have hmap : MapsTo (fun r : ℝ ↦ (r : ℂ) ^ 2 * u) (Icc 0 1) disk := fun r hr ↦ by
      rw [mem_disk_iff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
      exact (mul_le_of_le_one_left (norm_nonneg u) (by nlinarith [hr.1, hr.2])).trans_lt hu1
    have hderiv (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun s : ℝ ↦ (s : ℂ) ^ 2 * f ((s : ℂ) ^ 2 * u))
          ((2 * r) • (f ((r : ℂ) ^ 2 * u) + (r : ℂ) ^ 2 * u * deriv f ((r : ℂ) ^ 2 * u))) r := by
      have hpow := (hasDerivAt_id (r : ℂ)).pow 2
      have hcomp := (hf.differentiableAt (isOpen_ball.mem_nhds (hmap hr))).hasDerivAt.comp
        (r : ℂ) (hpow.mul_const u)
      convert (hpow.mul hcomp).comp_ofReal using 1
      · rfl
      · simp only [Pi.pow_apply, Function.comp_apply, id_eq, Nat.reduceSub, pow_one,
          Nat.cast_ofNat, mul_one, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
        ring
    have hcont : ContinuousOn (fun r : ℝ ↦ (2 * r) •
        (f ((r : ℂ) ^ 2 * u) + (r : ℂ) ^ 2 * u * deriv f ((r : ℂ) ^ 2 * u))) (Icc 0 1) := by
      have ha : ContinuousOn (fun r : ℝ ↦ (r : ℂ) ^ 2 * u) (Icc 0 1) := by fun_prop
      exact ((by fun_prop : ContinuousOn (fun r : ℝ ↦ 2 * r) (Icc 0 1)).smul
        ((hf.continuousOn.comp ha hmap).add
          (ha.mul ((hf.analyticOnNhd isOpen_ball).deriv.continuousOn.comp ha hmap)))).congr
        fun _ _ ↦ rfl
    have havg (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
        circleAverage (fun v ↦ kernel u v * f v) 0 r =
          f ((r : ℂ) ^ 2 * u) + (r : ℂ) ^ 2 * u * deriv f ((r : ℂ) ^ 2 * u) := by
      let a : ℂ := (r : ℂ) ^ 2 * u
      have ha : a ∈ ball 0 r := by
        simp only [a, mem_ball, dist_zero_right, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hr.1]
        nlinarith [sq_pos_of_pos hr.1, norm_nonneg u, hr.1, hr.2]
      have hfr : DiffContOnCl ℂ f (ball 0 r) :=
        (hf.mono (closure_ball_subset_closedBall.trans fun v hv ↦ lt_of_le_of_lt hv hr.2)).diffContOnCl
      have hne (v : ℂ) (hv : v ∈ sphere (0 : ℂ) r) : v - a ≠ 0 := fun hva ↦
        (ne_of_lt ha) (mem_sphere.mp (sub_eq_zero.mp hva ▸ hv))
      have hfc := hfr.continuousOn_ball.mono sphere_subset_closedBall
      have hci₁ : CircleIntegrable (fun v ↦ (v - a)⁻¹ * f v) 0 r :=
        (((continuousOn_id.sub continuousOn_const).inv₀ hne).mul hfc).circleIntegrable hr.1.le
      have hci₂a : CircleIntegrable (fun v ↦ a * ((v - a) ^ (-2 : ℤ) * f v)) 0 r :=
        (continuousOn_const.mul (((continuousOn_id.sub continuousOn_const).zpow₀ (-2)
          fun v hv ↦ Or.inl (hne v hv)).mul hfc)).circleIntegrable hr.1.le
      have hcauchy2 : (∮ v in C(0, r), (v - a) ^ (-2 : ℤ) * f v) = (2 * π * I) * deriv f a := by
        have has := Complex.hasDerivAt_circleIntegral_sub_inv_smul (w := a) (hfc.circleIntegrable hr.1.le)
          (by rw [abs_of_pos hr.1]; exact fun hs ↦ (ne_of_lt ha) (mem_sphere.mp hs))
        have heq : (fun a ↦ ∮ v in C(0, r), (v - a)⁻¹ • f v) =ᶠ[𝓝 a] (fun a ↦ (2 * π * I) * f a) :=
          (isOpen_ball.eventually_mem ha).mono fun b hb ↦ by
            simpa only [smul_eq_mul] using hfr.circleIntegral_sub_inv_smul hb
        simpa only [smul_eq_mul] using (has.congr_of_eventuallyEq heq.symm).unique
          ((hfr.differentiableAt isOpen_ball ha).hasDerivAt.const_mul (2 * π * I))
      have hintegrand (v : ℂ) (hv : v ∈ sphere (0 : ℂ) r) :
          (v - 0)⁻¹ • (kernel u v * f v) =
            (v - a)⁻¹ * f v + a * ((v - a) ^ (-2 : ℤ) * f v) := by
        have hwNorm : ‖v‖ = r := by simpa only [mem_sphere, dist_zero_right] using hv
        have hw0 : v ≠ 0 := by rintro rfl; simp at hwNorm; linarith [hr.1]
        have hwstar : v * conj v = (r : ℂ) ^ 2 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hwNorm]; norm_cast
        have hdenEq : 1 - u * conj v = (v - a) / v :=
          (eq_div_iff hw0).mpr (by dsimp [a]; linear_combination -u * hwstar)
        simp only [sub_zero, smul_eq_mul, kernel, zpow_neg, zpow_ofNat, ← starRingEnd_apply]
        rw [hdenEq]; field_simp [hw0, hne v hv]; ring
      rw [circleAverage_eq_circleIntegral hr.1.ne',
        circleIntegral.integral_congr hr.1.le hintegrand,
        circleIntegral.integral_add hci₁ hci₂a, circleIntegral.integral_const_mul,
        show (∮ v in C(0, r), (v - a)⁻¹ * f v) = (2 * π * I) * f a by
          simpa only [smul_eq_mul] using hfr.circleIntegral_sub_inv_smul ha,
        hcauchy2]
      simp only [smul_eq_mul]; field_simp; rfl
    change (∫ v, kernel u v * f v ∂diskArea) = f u
    rw [integral_diskArea_eq_circleAverage (integrable_kernel_mul hfi' hu),
      setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ congrArg ((2 * r) • ·) (havg r hr),
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr ↦ hderiv r (by simpa only [uIcc_of_le zero_le_one] using hr))
      (hcont.intervalIntegrable_of_Icc zero_le_one)
    simpa only [Complex.ofReal_one, Complex.ofReal_zero, one_pow, zero_pow (by omega : 2 ≠ 0),
      one_mul, zero_mul, sub_zero] using ht
  have h₁ := hL.reproduces (fun u ↦ P u w) (hpull.holomorphic w hw)
    (hcol hpull isOpen_ball.measurableSet hw) z hz
  have h₂ := hpull.reproduces (fun u ↦ kernel u z) (hL.holomorphic z hz)
    (hcol hL isOpen_ball.measurableSet hz) w hw
  have htrans : P z w = kernel z w := by
    calc
      P z w = ∫ u, kernel z u * P u w ∂area.restrict disk := h₁.symm
      _ = conj (∫ u, P w u * kernel u z ∂area.restrict disk) := by
        rw [← integral_conj]
        refine integral_congr_ae ((ae_restrict_mem isOpen_ball.measurableSet).mono fun u hu ↦ ?_)
        dsimp only
        rw [map_mul, starRingEnd_apply, starRingEnd_apply,
          ← hpull.hermitian u hu w hw, ← hL.hermitian z hz u hu, mul_comm]
      _ = conj (kernel w z) := congrArg (starRingEnd ℂ) h₂
      _ = kernel z w := (hL.hermitian z hz w hw).symm
  have hz' := deriv_ne_zero_of_bijOn isOpen_ball hΩ hφ hbij hz
  have hw' := deriv_ne_zero_of_bijOn isOpen_ball hΩ hφ hbij hw
  apply (eq_div_iff (mul_ne_zero hz' (star_ne_zero.mpr hw'))).mpr
  calc _ = P z w := by simp only [P]; ring
       _ = kernel z w := htrans

end BergmanWeakType
