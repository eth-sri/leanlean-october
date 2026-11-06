/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.AnalyticInverse
public import BergmanWeakType.Rigidity.ChangeOfVariables
public import BergmanWeakType.Rigidity.DiskReproducing
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ComplexConjugate Topology

namespace BergmanWeakType

/-- Both sections of a Hermitian Bergman kernel are square integrable. -/
theorem IsBergmanKernel.column_memLp {Ω : Set ℂ} {K : ℂ → ℂ → ℂ}
    (hK : IsBergmanKernel Ω K) (hΩ : MeasurableSet Ω) {z : ℂ} (hz : z ∈ Ω) :
    MemLp (fun w ↦ K w z) 2 (area.restrict Ω) := by
  have heq : (star (fun w ↦ K z w)) =ᵐ[area.restrict Ω] (fun w ↦ K w z) := by
    filter_upwards [ae_restrict_mem hΩ] with w hw
    exact (hK.hermitian w hw z hz).symm
  exact (memLp_congr_ae heq).mp (hK.squareIntegrable z hz).star

/-- The holomorphic pullback, including one complex derivative, preserves square integrability. -/
theorem memLp_pullback_deriv {U V : Set ℂ} {φ f : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hbij : BijOn φ U V)
    (hf : ContinuousOn f V) (hfi : MemLp f 2 (area.restrict V)) :
    MemLp (fun w ↦ deriv φ w * f (φ w)) 2 (area.restrict U) := by
  have hc : ContinuousOn (fun w ↦ deriv φ w * f (φ w)) U :=
    (hφ.analyticOnNhd hU).deriv.continuousOn.mul
      (hf.comp hφ.continuousOn hbij.mapsTo)
  apply (memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable hU.measurableSet)).mpr
  have hi := hfi.integrable_norm_pow (by omega : 2 ≠ 0)
  have himage : IntegrableOn (fun w ↦ ‖f w‖ ^ 2) (φ '' U) area := by
    rwa [hbij.image_eq]
  have hp := (area_integrableOn_image_iff_norm_deriv_sq hU hφ hbij.injOn
    (fun w ↦ ‖f w‖ ^ 2)).mp himage
  simpa only [IntegrableOn, norm_mul, mul_pow, smul_eq_mul] using hp

/-- The usual pullback of a Bergman kernel under a holomorphic coordinate map. -/
def pullbackKernel (φ : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (z w : ℂ) : ℂ :=
  deriv φ z * K (φ z) (φ w) * star (deriv φ w)

theorem deriv_inverse_mul {U V : Set ℂ} {φ ψ : ℂ → ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : DifferentiableOn ℂ φ U)
    (hψ : DifferentiableOn ℂ ψ V) (hinv : InvOn ψ φ U V) (hmap : MapsTo φ U V)
    {z : ℂ} (hz : z ∈ U) : deriv ψ (φ z) * deriv φ z = 1 := by
  have hc := (hψ.differentiableAt (hV.mem_nhds (hmap hz))).hasDerivAt.comp z
    (hφ.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hid : HasDerivAt (fun z : ℂ ↦ z) (deriv ψ (φ z) * deriv φ z) z :=
    hc.congr_of_eventuallyEq ((hU.eventually_mem hz).mono fun w hw ↦ (hinv.1 hw).symm)
  exact hid.unique (hasDerivAt_id z)

/-- Bergman kernels transform by one derivative in each variable under a biholomorphic map. -/
theorem IsBergmanKernel.pullback {U V : Set ℂ} {K : ℂ → ℂ → ℂ} {φ ψ : ℂ → ℂ}
    (hK : IsBergmanKernel V K) (hU : IsOpen U) (hV : IsOpen V)
    (hφ : DifferentiableOn ℂ φ U) (hψ : DifferentiableOn ℂ ψ V)
    (hbij : BijOn φ U V) (hinv : InvOn ψ φ U V) :
    IsBergmanKernel U (pullbackKernel φ K) := by
  have hψbij : BijOn ψ V U := hbij.symm hinv.symm
  have hφderiv := (hφ.analyticOnNhd hU).deriv.differentiableOn
  have hψderiv := (hψ.analyticOnNhd hV).deriv.differentiableOn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    exact (hφderiv.mul ((hK.holomorphic (φ w) (hbij.mapsTo hw)).comp hφ hbij.mapsTo)).mul_const
      (star (deriv φ w))
  · intro z hz w hw
    simp only [pullbackKernel, star_mul, star_star, hK.hermitian (φ w) (hbij.mapsTo hw)
      (φ z) (hbij.mapsTo hz)]
    ring
  · intro z hz
    have hcol := memLp_pullback_deriv hU hφ hbij
      (hK.holomorphic (φ z) (hbij.mapsTo hz)).continuousOn
      (hK.column_memLp hV.measurableSet (hbij.mapsTo hz))
    have hm := hcol.star.const_mul (deriv φ z)
    apply (memLp_congr_ae ?_).mp hm
    filter_upwards [ae_restrict_mem hU.measurableSet] with w hw
    simp only [Pi.star_apply, star_mul, pullbackKernel]
    rw [← hK.hermitian (φ z) (hbij.mapsTo hz) (φ w) (hbij.mapsTo hw)]
    ring
  · intro f hf hfi z hz
    let F : ℂ → ℂ := fun v ↦ deriv ψ v * f (ψ v)
    have hFd : DifferentiableOn ℂ F V :=
      hψderiv.mul (hf.comp hψ hψbij.mapsTo)
    have hFi : MemLp F 2 (area.restrict V) :=
      memLp_pullback_deriv hV hψ hψbij hf.continuousOn hfi
    have hrep := hK.reproduces F hFd hFi (φ z) (hbij.mapsTo hz)
    have hchange := area_integral_image_eq hU hφ hbij.injOn
      (fun v ↦ K (φ z) v * F v)
    rw [hbij.image_eq] at hchange
    have heq : (∫ v, K (φ z) v * F v ∂area.restrict V) =
        ∫ w, K (φ z) (φ w) * star (deriv φ w) * f w ∂area.restrict U := by
      rw [hchange]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with w hw
      have hd := deriv_inverse_mul hU hV hφ hψ hinv hbij.mapsTo hw
      dsimp only [F]
      rw [hinv.1 hw, Complex.real_smul, ← Complex.normSq_eq_norm_sq,
        ← Complex.mul_conj]
      simp only [starRingEnd_apply]
      calc
        _ = (deriv ψ (φ w) * deriv φ w) *
            (K (φ z) (φ w) * star (deriv φ w) * f w) := by ring
        _ = _ := by rw [hd, one_mul]
    calc
      (∫ w, pullbackKernel φ K z w * f w ∂area.restrict U) =
          deriv φ z * ∫ w, K (φ z) (φ w) * star (deriv φ w) * f w ∂area.restrict U := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun w ↦ by simp only [pullbackKernel]; ring
      _ = deriv φ z * F (φ z) := by rw [← heq, hrep]
      _ = f z := by
        dsimp only [F]
        rw [hinv.1 hz]
        have hd := deriv_inverse_mul hU hV hφ hψ hinv hbij.mapsTo hz
        calc
          _ = (deriv ψ (φ z) * deriv φ z) * f z := by ring
          _ = _ := by rw [hd, one_mul]

/-- The Bergman kernel of a domain, expressed in any biholomorphic disk coordinates. -/
theorem IsBergmanKernel.disk_coordinate_formula {Ω : Set ℂ} {K : ℂ → ℂ → ℂ}
    {φ ψ : ℂ → ℂ} (hK : IsBergmanKernel Ω K) (hΩ : IsOpen Ω)
    (hφ : DifferentiableOn ℂ φ disk) (hψ : DifferentiableOn ℂ ψ Ω)
    (hbij : BijOn φ disk Ω) (hinv : InvOn ψ φ disk Ω)
    {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    K (φ z) (φ w) = kernel z w / (deriv φ z * star (deriv φ w)) := by
  let hP := hK.pullback Metric.isOpen_ball hΩ hφ hψ hbij hinv
  have htrans := by
    have h₁ := isBergmanKernel_disk.reproduces (fun u ↦ pullbackKernel φ K u w)
      (hP.holomorphic w hw) (hP.column_memLp Metric.isOpen_ball.measurableSet hw) z hz
    have h₂ := hP.reproduces (fun u ↦ kernel u z) (isBergmanKernel_disk.holomorphic z hz)
      (isBergmanKernel_disk.column_memLp Metric.isOpen_ball.measurableSet hz) w hw
    calc
      pullbackKernel φ K z w = ∫ u, kernel z u * pullbackKernel φ K u w ∂diskArea := h₁.symm
      _ = conj (∫ u, pullbackKernel φ K w u * kernel u z ∂diskArea) := by
        rw [← integral_conj]
        apply integral_congr_ae
        filter_upwards [ae_mem_disk] with u hu
        rw [map_mul, starRingEnd_apply, starRingEnd_apply,
          ← hP.hermitian u hu w hw, ← isBergmanKernel_disk.hermitian z hz u hu, mul_comm]
      _ = conj (kernel w z) := congrArg (starRingEnd ℂ) h₂
      _ = kernel z w := (isBergmanKernel_disk.hermitian z hz w hw).symm
  have hz' := deriv_ne_zero_of_bijOn Metric.isOpen_ball hΩ hφ hbij hz
  have hw' := deriv_ne_zero_of_bijOn Metric.isOpen_ball hΩ hφ hbij hw
  apply (eq_div_iff (mul_ne_zero hz' (star_ne_zero.mpr hw'))).mpr
  calc
    _ = pullbackKernel φ K z w := by simp only [pullbackKernel]; ring
    _ = kernel z w := htrans

end BergmanWeakType
