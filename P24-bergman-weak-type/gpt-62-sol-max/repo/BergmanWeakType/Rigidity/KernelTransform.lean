/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.ChangeOfVariables
public import BergmanWeakType.Rigidity.DiskReproducing
public import Mathlib.MeasureTheory.Function.L2Space

public section

open Set MeasureTheory Filter
open scoped ComplexConjugate

namespace BergmanWeakType

/-- Pulling back a kernel column with one complex derivative preserves holomorphy and L². -/
private theorem pullback_column {U V : Set ℂ} {φ : ℂ → ℂ} {K : ℂ → ℂ → ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : DifferentiableOn ℂ φ U) (hbij : BijOn φ U V)
    (hK : IsBergmanKernel V K) {z : ℂ} (hz : z ∈ V) :
    DifferentiableOn ℂ (fun w ↦ deriv φ w * K (φ w) z) U ∧
      MemLp (fun w ↦ deriv φ w * K (φ w) z) 2 (area.restrict U) := by
  have hi : MemLp (fun w ↦ K w z) 2 (area.restrict V) := by
    refine MemLp.ae_eq ?_ (hK.squareIntegrable z hz).star
    filter_upwards [ae_restrict_mem hV.measurableSet] with w hw
    exact (hK.hermitian w hw z hz).symm
  have hd := (hφ.analyticOnNhd hU).deriv.differentiableOn.mul ((hK.holomorphic z hz).comp hφ hbij.mapsTo)
  refine ⟨hd, (memLp_two_iff_integrable_sq_norm (hd.continuousOn.aestronglyMeasurable hU.measurableSet)).mpr ?_⟩
  simpa [IntegrableOn, norm_mul, mul_pow] using
    (area_integrableOn_image_iff_norm_deriv_sq hU hφ hbij.injOn (fun w ↦ ‖K w z‖ ^ 2)).mp
      (hbij.image_eq.symm ▸ hi.integrable_norm_pow (by decide : 2 ≠ 0))

/-- Test reproduction in each chart against the column from the other one. -/
theorem IsBergmanKernel.disk_formula {Ω : Set ℂ} {K : ℂ → ℂ → ℂ}
    {φ ψ : ℂ → ℂ} (hK : IsBergmanKernel Ω K) (hΩ : IsOpen Ω)
    (hφ : DifferentiableOn ℂ φ disk) (hψ : DifferentiableOn ℂ ψ Ω)
    (hbij : BijOn φ disk Ω) (hinv : InvOn ψ φ disk Ω)
    {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    K (φ z) (φ w) = kernel z w / (deriv φ z * conj (deriv φ w)) := by
  let f := fun u ↦ deriv φ u * K (φ u) (φ z)
  let F := fun v ↦ deriv ψ v * kernel (ψ v) w
  have hb := hbij.symm hinv.symm
  have hz' := hbij.mapsTo hz
  obtain ⟨hfd, hfi⟩ := pullback_column Metric.isOpen_ball hΩ hφ hbij hK hz'
  obtain ⟨hFd, hFi⟩ := pullback_column hΩ Metric.isOpen_ball hψ hb isBergmanKernel_disk hw
  have h₂ := hK.reproduces F hFd hFi (φ z) hz'
  have hd {x} (hx : x ∈ disk) : deriv ψ (φ x) * deriv φ x = 1 := by
    have hc := (hψ.differentiableAt (hΩ.mem_nhds (hbij.mapsTo hx))).hasDerivAt.comp x
      (hφ.differentiableAt (Metric.isOpen_ball.mem_nhds hx)).hasDerivAt
    exact (hc.congr_of_eventuallyEq ((Metric.isOpen_ball.eventually_mem hx).mono
      fun u hu ↦ (hinv.1 hu).symm)).unique (hasDerivAt_id x)
  have heq : (∫ v, K (φ z) v * F v ∂area.restrict Ω) = conj (∫ u in disk, kernel w u * f u ∂area) := by
    rw [← hbij.image_eq, area_integral_image_eq (U := disk) Metric.isOpen_ball hφ hbij.injOn, ← integral_conj]
    change (∫ u, _ ∂diskArea) = _
    apply integral_congr_ae
    filter_upwards [ae_mem_disk] with u hu
    simp only [Complex.real_smul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, F, f,
      hinv.1 hu, map_mul, starRingEnd_apply, ← isBergmanKernel_disk.hermitian u hu w hw,
      ← hK.hermitian (φ z) hz' (φ u) (hbij.mapsTo hu)]
    have h := hd hu
    clear * - h
    grind
  rw [heq, isBergmanKernel_disk.reproduces f hfd hfi w hw] at h₂
  simp only [F, f, hinv.1 hz, map_mul, starRingEnd_apply, ← hK.hermitian (φ z) hz' (φ w) (hbij.mapsTo hw)] at h₂
  have h := hd hz
  have hw' := right_ne_zero_of_mul_eq_one (hd hw)
  simp only [starRingEnd_apply]
  rw [eq_div_iff (mul_ne_zero (right_ne_zero_of_mul_eq_one h) (star_ne_zero.mpr hw'))]
  clear * - h₂ h
  grind

end BergmanWeakType
