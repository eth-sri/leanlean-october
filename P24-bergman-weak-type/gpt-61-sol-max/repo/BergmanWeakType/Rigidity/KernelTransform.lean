/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Rigidity.AnalyticInverse
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import BergmanWeakType.Rigidity.DiskReproducing
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

variable {Ω U V : Set ℂ} {K : ℂ → ℂ → ℂ} {z : ℂ} {φ ψ : ℂ → ℂ}




open Set MeasureTheory
open scoped ComplexConjugate

namespace BergmanWeakType

/-- A complex derivative scales real area by its squared norm. -/
theorem det_complex_derivative (c ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]


/-- The normalized-area version of holomorphic change of variables for complex integrals. -/
def area_integral_image_eq {E : Type*} [RCLike E] (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U)
    (g : ℂ → E) := by
  simpa [det_complex_derivative, abs_sq] using
    integral_image_eq_integral_abs_det_fderiv_smul area hU.measurableSet
      (fun w hw ↦
        ((hφ.differentiableAt (hU.mem_nhds hw)).hasDerivAt.hasFDerivAt |>.restrictScalars ℝ).hasFDerivWithinAt)
      hinj g


/-- A finite-area Bergman kernel reproduces one. -/
def IsBergmanKernel.integral_section_eq_one [IsFiniteMeasure (area.restrict Ω)]
    (hK : IsBergmanKernel Ω K) (hz : z ∈ Ω) := by
  simpa using hK.reproduces _ (differentiableOn_const 1) (memLp_const 1) z hz

/-- Both sections of a Hermitian Bergman kernel are square integrable. -/
def IsBergmanKernel.column_memLp
    (hK : IsBergmanKernel Ω K) (hΩ : MeasurableSet Ω)  (hz : z ∈ Ω) :=
  MemLp.ae_eq ((ae_restrict_mem hΩ).mono fun w hw ↦ (hK.hermitian w hw z hz).symm)
    (hK.squareIntegrable z hz).star

/-- The holomorphic pullback, including one complex derivative, preserves square integrability. -/
def memLp_pullback_deriv  {f : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hbij : BijOn φ U V)
    (hf : ContinuousOn f V) (hfi : MemLp f 2 (area.restrict V)) := by
  have hc  :=
    (hφ.analyticOnNhd hU).deriv.continuousOn.mul
      (hf.comp hφ.continuousOn hbij.mapsTo)
  apply (memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable hU.measurableSet)).mpr
  have hi := hfi.integrable_norm_pow (two_ne_zero : 2 ≠ 0)
  have hp := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul area hU.measurableSet
    (fun w hw ↦ ((hφ.differentiableAt (hU.mem_nhds hw)).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ).hasFDerivWithinAt) hbij.injOn (fun w ↦ ‖f w‖ ^ 2)).mp (by simpa only [hbij.image_eq] using! hi)
  simpa [det_complex_derivative, abs_sq, IntegrableOn, mul_pow] using hp

/-- The Jacobian-weighted kernel formula follows directly from pullback uniqueness. -/
theorem IsBergmanKernel.disk_jacobian_formula (hK : IsBergmanKernel Ω K) (hΩ : IsOpen Ω)
    (hφ : DifferentiableOn ℂ φ disk) (hψ : DifferentiableOn ℂ ψ Ω) (hbij : BijOn φ disk Ω) (hinv : InvOn ψ φ disk Ω)
    {w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) : ‖deriv φ w‖ ^ 2 • K (φ z) (φ w) = deriv φ w * kernel z w / deriv φ z :=
  by
  have hψbij := hbij.symm hinv.symm
  have hrep :=
    isBergmanKernel_disk.reproduces _
      ((hφ.analyticOnNhd Metric.isOpen_ball).deriv.differentiableOn.mul
        ((hK.holomorphic (φ w) (hbij.mapsTo hw)).comp hφ hbij.mapsTo))
      (memLp_pullback_deriv Metric.isOpen_ball hφ hbij (hK.holomorphic (φ w) (hbij.mapsTo hw)).continuousOn
      (hK.column_memLp hΩ.measurableSet (hbij.mapsTo hw))) z hz
  let F := fun v ↦ deriv ψ v * kernel (ψ v) z
  have hFi :=
    memLp_pullback_deriv hΩ hψ hψbij (isBergmanKernel_disk.holomorphic z hz).continuousOn
      (isBergmanKernel_disk.column_memLp Metric.isOpen_ball.measurableSet hz)
  have hrep' :=
    hK.reproduces F
      ((hψ.analyticOnNhd hΩ).deriv.differentiableOn.mul ((isBergmanKernel_disk.holomorphic z hz).comp hψ hψbij.mapsTo))
      hFi (φ w) (hbij.mapsTo hw)
  have hchange := area_integral_image_eq (U := disk) Metric.isOpen_ball hφ hbij.injOn (fun v ↦ K (φ w) v * F v)
  rw [hbij.image_eq] at hchange
  have ht : deriv φ z * K (φ z) (φ w) = conj (deriv ψ (φ w)) * kernel z w := by
    calc
      _ = ∫ u in disk, kernel z u * (deriv φ u * K (φ u) (φ w)) ∂area := hrep.symm
      _ = conj (∫ v in Ω, K (φ w) v * F v ∂area) :=
        by
        rw [hchange, ← integral_conj]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with u hu
        have hd := congrArg (starRingEnd ℂ) (deriv_inverse_mul Metric.isOpen_ball hΩ hφ hψ hinv hbij.mapsTo hu)
        dsimp only [F]
        rw [hinv.1 hu, Complex.real_smul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
        simp only [map_mul, map_one, starRingEnd_apply, star_star,
          ← hK.hermitian _ (hbij.mapsTo hu) _ (hbij.mapsTo hw),
          ← isBergmanKernel_disk.hermitian z hz u hu] at hd ⊢
        linear_combination -deriv φ u * kernel z u * K _ _ * hd
      _ = conj (F (φ w)) := (congrArg (starRingEnd ℂ) hrep')
      _ = _ := by
        simp only [F, hinv.1 hw, map_mul]
        congr 1
        exact (isBergmanKernel_disk.hermitian z hz w hw).symm
  have hz' := right_ne_zero_of_mul_eq_one (deriv_inverse_mul Metric.isOpen_ball hΩ hφ hψ hinv hbij.mapsTo hz)
  have hd := congrArg (starRingEnd ℂ) (deriv_inverse_mul Metric.isOpen_ball hΩ hφ hψ hinv hbij.mapsTo hw)
  simp at hd
  rw [Complex.real_smul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  apply (eq_div_iff hz').mpr
  linear_combination deriv φ w * conj _ * ht + deriv φ w * kernel z w * hd

end BergmanWeakType
