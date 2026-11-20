/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.RiemannMapping
public import BergmanWeakType.WeakType
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.MeanValue
public import BergmanWeakType.Rigidity.KernelTransform
public import BergmanWeakType.KernelIntegrability
public import BergmanWeakType.Weighted.CompactIntegral
public import Mathlib.Analysis.Normed.Module.Connected
public import BergmanWeakType.Measure
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.MeasureTheory.Measure.OpenPos

public section

open Set MeasureTheory Metric Filter
open scoped ComplexConjugate ComplexOrder ENNReal

namespace BergmanWeakType

/-- Boundedness rules out a pole on the unit circle; an interior parameter gives a disk shift. -/
private theorem image_is_disk_of_derivative_form {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ disk) (hφ0 : deriv φ 0 ≠ 0)
    (hbounded : Bornology.IsBounded (φ '' disk)) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    (hderiv : ∀ w ∈ disk, deriv φ w * (1 - w * conj ζ) ^ 2 = deriv φ 0) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ φ '' disk = ball c R := by
  let a := φ 0
  let b := deriv φ 0
  let G := fun w ↦ a + b * (w / (1 - w * conj ζ))
  have hn {w : ℂ} (hw : w ∈ disk) : 1 - w * conj ζ ≠ 0 := kernel_denominator_ne_zero hw hζ
  have hG (w : ℂ) (hw : w ∈ disk) : HasDerivAt G (deriv φ w) w := by
    have d := hasDerivAt_id w
    have h := hderiv w hw
    convert ((d.div ((d.mul_const (conj ζ)).const_sub 1) (hn hw)).const_mul b).const_add a using 1
    · rfl
    grind
  have he : φ '' disk = G '' disk := image_congr (isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℂ) 1).isPreconnected hφ
    (fun w hw ↦ (hG w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hG w hw).deriv.symm) (x := 0) (by simp) (by simp [G, a]))
  have hζ' : ‖ζ‖ < 1 := by
    refine lt_of_le_of_ne hζ fun h ↦ ?_
    obtain ⟨M, _, hM⟩ := (he ▸ hbounded).exists_pos_norm_le
    have hbnd (w : ℂ) (hw : w ∈ disk) : ‖b * w‖ ≤ (M + ‖a‖) * ‖1 - w * conj ζ‖ := by
      apply (div_le_iff₀ (norm_pos_iff.mpr (hn hw))).mp
      rw [← norm_div, mul_div_assoc, ← show G w - a = _ from add_sub_cancel_left _ _]
      exact (norm_sub_le _ _).trans (add_le_add_left (hM _ ⟨w, hw, rfl⟩) _)
    have hm : ζ * conj ζ = 1 := by simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
    have hf := le_on_closure hbnd (by fun_prop) (by fun_prop) (show ζ ∈ closure disk by simp [disk, closure_ball, h])
    simp [h, hm, b, hφ0] at hf
  have hmem : ζ ∈ disk := (mem_disk_iff _).mpr hζ'
  let k := b / (1 - ζ * conj ζ)
  have hk : k ≠ 0 := div_ne_zero hφ0 (hn hmem)
  let c := a + k * ζ
  have hf : EqOn G ((fun w ↦ c + k * w) ∘ diskShift (-ζ)) disk := by
    intro w hw
    simp only [Function.comp_apply, G, c, k, diskShift, map_neg, mul_neg, ← sub_eq_add_neg]
    have h₁ : 1 - ζ * conj ζ ≠ 0 := hn hmem
    grind [hn hw]
  refine ⟨c, ‖k‖, norm_pos_iff.mpr hk, ?_⟩
  rw [he, image_congr hf, image_comp, (diskShift_bijOn (by simpa using hmem : -ζ ∈ disk)).image_eq, image_affine_disk hk]

/-- A compact interior core gives a uniform cancellation gap in every row of a non-disk kernel. -/
theorem weakTypeConstant_gt_one_of_nondisk {Ω : Set ℂ} {K : ℂ → ℂ → ℂ}
    (hΩ : IsOpen Ω) (hconn : IsSimplyConnected Ω) (hbdd : Bornology.IsBounded Ω)
    (hK : IsBergmanKernel Ω K) (hnd : ¬∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = ball c R) :
    1 < weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) := by
  let : IsFiniteMeasure (area.restrict Ω) := isFiniteMeasure_restrict.mpr hbdd.measure_lt_top.ne
  obtain ⟨φ, ψ, hφ, hψ, hbij, hinv, hne⟩ := exists_biholomorphic_unitBall hΩ hconn hbdd
  have h0 : (0 : ℂ) ∈ disk := by simp
  have hx := hbij.mapsTo h0
  obtain ⟨r, hr, hEO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hx)
  let E := closedBall (φ 0) r
  have hE : MeasurableSet E := measurableSet_closedBall
  have hB := ball_subset_closedBall.trans hEO
  let μ := area.restrict E
  let P := fun u ↦ deriv φ (ψ u)
  let Q := fun ζ u ↦ P u * (1 - ψ u * conj ζ) ^ 2
  let g := fun ζ u ↦ (Q ζ u)⁻¹
  let I := fun ζ ↦ ∫ u, g ζ u ∂μ
  let N := fun ζ ↦ ∫ u, ‖g ζ u‖ ∂μ
  have hm := (hbij.symm hinv.symm).mapsTo
  have hP : DifferentiableOn ℂ P Ω := (hφ.analyticOnNhd isOpen_ball).deriv.differentiableOn.comp hψ hm
  have hnorm {ζ : ℂ} (hζ : ζ ∈ closedBall 0 1) : ‖ζ‖ ≤ 1 := by simpa using hζ
  have hQ {ζ u} (hζ : ζ ∈ closedBall 0 1) (hu : u ∈ Ω) : Q ζ u ≠ 0 :=
    mul_ne_zero (hne _ (hm hu)) (pow_ne_zero _ (kernel_denominator_ne_zero (hm hu) (hnorm hζ)))
  have hprod : ContinuousOn (Function.uncurry g) (closedBall 0 1 ×ˢ E) := by
    have hs : MapsTo Prod.snd (closedBall (0 : ℂ) 1 ×ˢ E) Ω := fun _ hp ↦ hEO hp.2
    have hP' := hP.continuousOn.comp continuous_snd.continuousOn hs
    have hψ' := hψ.continuousOn.comp continuous_snd.continuousOn hs
    unfold Function.uncurry g
    exact ContinuousOn.inv₀ (hP'.mul ((continuousOn_const.sub (hψ'.mul (continuous_star.comp continuous_fst).continuousOn)).pow 2)) fun p hp ↦ hQ hp.1 (hEO hp.2)
  have hT := isCompact_closedBall (φ 0) r
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hT.measure_lt_top.ne
  have hμ := ae_restrict_mem (μ := area) hE
  have hlt {ζ} (hζ : ζ ∈ closedBall 0 1) : ‖I ζ‖ < N ζ := by
    refine lt_of_le_of_ne (norm_integral_le_integral_norm _) fun heq ↦ hnd ?_
    let c := Complex.exp (-(I ζ).arg * Complex.I)
    have hc : c ≠ 0 := Complex.exp_ne_zero _
    let G := fun u ↦ g ζ u * c
    have hG : DifferentiableOn ℂ G Ω := by
      unfold G g Q
      fun_prop (disch := exact fun _ hu ↦ hQ hζ hu)
    have hGint : Integrable G μ := (integrable_compact_slice hT hμ hprod hζ).mul_const _
    have he : (fun u ↦ (G u).re) =ᵐ[μ] fun u ↦ ‖G u‖ :=
      (integral_eq_iff_of_ae_le hGint.re hGint.norm (.of_forall fun _ ↦ Complex.re_le_norm _)).mp (by
        simp only [G, norm_mul]
        rw [integral_re hGint, integral_mul_const, integral_mul_const]
        change (I ζ * c).re = N ζ * ‖c‖
        nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I (I ζ)]
        simp [c, neg_mul, Complex.exp_neg, heq])
    have hreal := Measure.eqOn_open_of_ae_eq (μ := area)
      (ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall (he.mono fun u hu ↦ (Complex.re_eq_norm.mp hu).2.symm))
      isOpen_ball (Complex.continuous_im.comp_continuousOn (hG.continuousOn.mono hB)) continuousOn_const
    have ha := hG.analyticOnNhd hΩ
    obtain ⟨d, hd⟩ := (ha.mono hB).eq_const_of_im_eq_const hreal isOpen_ball (isConnected_ball hr)
    have hconst := ha.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      hconn.isPathConnected.isConnected.isPreconnected hx ((isOpen_ball.eventually_mem (mem_ball_self hr)).mono hd)
    rw [← hbij.image_eq]
    apply image_is_disk_of_derivative_form hφ (hne 0 h0) (hbij.image_eq.symm ▸ hbdd) (hnorm hζ)
    intro w hw
    have h := (hconst (hbij.mapsTo hw)).trans (hconst hx).symm
    exact inv_injective (mul_right_cancel₀ hc (by simpa [G, g, Q, P, hinv.1 hw, hinv.1 h0] using h))
  have hpos {ζ} (hζ : ζ ∈ closedBall 0 1) := (norm_nonneg _).trans_lt (hlt hζ)
  obtain ⟨ζ, hζ, hmax⟩ := (isCompact_closedBall 0 1).exists_isMaxOn ⟨0, by simp⟩
    ((continuousOn_integral_of_compact_support hT hμ hprod).norm.div
      (continuousOn_integral_of_compact_support hT hμ (F := fun ζ u ↦ ‖g ζ u‖) hprod.norm) fun _ hx ↦ (hpos hx).ne')
  let q := ‖I ζ‖ / N ζ
  have hq : 0 ≤ q := div_nonneg (norm_nonneg _) (hpos hζ).le
  have hqone : q < 1 := (div_lt_one (hpos hζ)).mpr (hlt hζ)
  have hgap a (ha : a ∈ Ω) : ‖∫ w in E, K a w ∂area‖ ≤ q * ∫ w in E, ‖K a w‖ ∂area := by
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn ha
    have he {u : ℂ} (hu : u ∈ E) : K (φ z) u = conj (g z u) / deriv φ z := by
      have h := hK.disk_formula hΩ hφ hψ hbij hinv hz (hm (hEO hu))
      simpa [g, Q, P, kernel, div_eq_mul_inv, inv_pow, mul_comm, mul_left_comm, mul_assoc, hinv.2 (hEO hu), ← starRingEnd_apply] using h
    change ‖∫ u in E, K (φ z) u ∂area‖ ≤ _
    rw [setIntegral_congr_fun (g := fun u ↦ conj (g z u) / deriv φ z) hE (fun _ ↦ he),
      setIntegral_congr_fun (g := fun u ↦ ‖g z u‖ / ‖deriv φ z‖) hE
        (fun _ hu ↦ by simp_all),
      integral_div, integral_div, integral_conj, norm_div, Complex.norm_conj, ← mul_div_assoc]
    have hz' : z ∈ closedBall 0 1 := ball_subset_closedBall hz
    exact div_le_div_of_nonneg_right ((div_le_iff₀ (hpos hz')).mp (hmax hz')) (norm_nonneg _)

  -- Lower the input on the core. The gap preserves level one while decreasing the input mass.
  classical
  let ν := area.restrict Ω
  let f : ℂ → ℂ := E.piecewise (fun _ ↦ ↑q) 1
  have hf : Integrable f ν := Integrable.piecewise hE (integrable_const _) (integrable_const _)
  have splitIntegral (g : ℂ → ℝ≥0∞) : (∫⁻ w, g w * ‖f w‖ₑ ∂ν) =
      ENNReal.ofReal q * (∫⁻ w in E, g w ∂ν) + ∫⁻ w in Eᶜ, g w ∂ν := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_piecewise hE]
    congr with w
    by_cases hw : w ∈ E <;> simp [f, hw, ← ofReal_norm, abs_of_nonneg hq, mul_comm]

  suffices h : (∫⁻ z, ‖f z‖ₑ ∂ν) < ν univ ∧ ∀ᵐ z ∂ν, 1 ≤ domainPositiveProjection Ω K f z by
    refine lt_of_lt_of_le (b := ν univ / ∫⁻ z, ‖f z‖ₑ ∂ν) ?_ (le_sInf fun C hC ↦ ?_)
    · exact (ENNReal.lt_div_iff_mul_lt (Or.inr ENNReal.one_ne_top) (Or.inr one_ne_zero)).mpr (by simpa using h.1)
    · apply ENNReal.div_le_of_le_mul
      simpa [ν] using hC.test_le hf (E := univ) (l := 1) (by simpa using h.2)
  constructor
  · have h := splitIntegral 1
    simp only [Pi.one_apply, one_mul, setLIntegral_const] at h
    rw [h, ← measure_add_measure_compl hE]
    apply ENNReal.add_lt_add_right (measure_ne_top ν Eᶜ)
    have hp : ν E ≠ 0 := by
      rw [show ν E = area E from Measure.restrict_eq_self _ hEO]
      exact (measure_closedBall_pos area (φ 0) hr).ne'
    simpa [mul_comm] using ENNReal.mul_lt_mul_right hp (measure_ne_top ν E) (ENNReal.ofReal_lt_one.mpr hqone)
  · filter_upwards [ae_restrict_mem hΩ.measurableSet] with a ha
    have hk : Integrable (K a) ν := (hK.squareIntegrable a ha).integrable (by norm_num)
    have hg := hgap a ha
    rw [← Measure.restrict_restrict_of_subset (μ := area) hEO] at hg
    have ht := ENNReal.ofReal_le_ofReal hg
    rw [ofReal_norm, ENNReal.ofReal_mul hq, ofReal_integral_norm_eq_lintegral_enorm hk.integrableOn] at ht
    have h := (enorm_add_le (∫ w in E, K a w ∂ν) (∫ w in Eᶜ, K a w ∂ν)).trans
      (add_le_add ht (enorm_integral_le_lintegral_enorm (μ := ν.restrict Eᶜ) (K a)))
    have hconstant : (∫ w, K a w ∂ν) = 1 := by
      simpa using hK.reproduces (fun _ ↦ 1) (differentiableOn_const _) (memLp_const _) a ha
    rw [integral_add_compl hE hk, hconstant, enorm_one] at h
    rw [domainPositiveProjection, splitIntegral]
    simpa only [ofReal_norm] using h

end BergmanWeakType
