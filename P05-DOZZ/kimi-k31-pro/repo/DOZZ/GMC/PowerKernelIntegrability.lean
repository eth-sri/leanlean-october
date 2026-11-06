/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Local integrability of the planar power kernel below its dimension threshold. -/


open MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace DOZZ.Proofs

/-- The planar Riesz kernel `‖z‖⁻ᵅ` is locally integrable when its exponent is strictly below
the real dimension two. -/
theorem complex_norm_neg_rpow_locallyIntegrable (α : ℝ) (hαpos : 0 < α) (hα : α < 2) :
    LocallyIntegrable (fun z : ℂ => ‖z‖ ^ (-α)) volume := by
  refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℝ)
    (μ := volume) (C := 1) (α := α) ?_ ?_ ?_ ?_
  · rw [Complex.finrank_real_complex]
    norm_num
  · exact hα.trans_eq (by norm_num [Complex.finrank_real_complex])
  · filter_upwards [] with z
    calc
      ‖‖z‖ ^ (-α)‖ = ‖z‖ ^ (-α) :=
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)
      _ ≤ 1 * ‖z‖ ^ (-α) := by simp
  · have hα0 : 0 ≤ α := hαpos.le
    have hpow : Measurable (fun z : ℂ => ‖z‖ ^ α) :=
      (Real.continuous_rpow_const hα0).comp continuous_norm |>.measurable
    have hfun : (fun z : ℂ => ‖z‖ ^ (-α)) =
        fun z => (‖z‖ ^ α)⁻¹ := by
      funext z
      rw [Real.rpow_neg (norm_nonneg z)]
    rw [hfun]
    exact (measurable_inv.comp hpow).aestronglyMeasurable

/-- The local singularity has a uniform finite integral when its center ranges over a compact
set and the integration domain is compact. The bound comes from translating both compact sets
into one fixed ball around the origin. -/
theorem complex_norm_sub_neg_rpow_lintegral_uniform_compacts
    (K L : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (α : ℝ) (hαpos : 0 < α) (hα : α < 2) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ u ∈ K,
      ∫⁻ z in L, ENNReal.ofReal (‖z - u‖ ^ (-α)) ∂volume ≤ C := by
  obtain ⟨R₁, hR₁, hLnorm⟩ := hL.isBounded.exists_pos_norm_lt
  obtain ⟨R₂, hR₂, hKnorm⟩ := hK.isBounded.exists_pos_norm_lt
  let R : ℝ := R₁ + R₂
  let B : Set ℂ := Metric.closedBall 0 R
  let f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (-α))
  have hbase := complex_norm_neg_rpow_locallyIntegrable α hαpos hα
  have hballReal : IntegrableOn (fun z : ℂ => ‖z‖ ^ (-α)) B volume :=
    hbase.integrableOn_isCompact (isCompact_closedBall 0 R)
  have hballNonneg : 0 ≤ᵐ[volume.restrict B] (fun z : ℂ => ‖z‖ ^ (-α)) :=
    ae_of_all _ (fun z => Real.rpow_nonneg (norm_nonneg _) _)
  let C : ℝ≥0∞ := ∫⁻ z in B, f z ∂volume
  have hC : C ≠ ∞ := by
    dsimp [C, f]
    rw [← ofReal_integral_eq_lintegral_ofReal hballReal hballNonneg]
    exact ENNReal.ofReal_ne_top
  refine ⟨C, hC, ?_⟩
  intro u hu
  let e : ℂ → ℂ := fun z => z + u
  have he : MeasurePreserving e volume volume :=
    MeasureTheory.measurePreserving_add_right volume u
  have hchange :
      ∫⁻ z in L, ENNReal.ofReal (‖z - u‖ ^ (-α)) ∂volume =
        ∫⁻ z in e ⁻¹' L, f z ∂volume := by
    calc
      _ = ∫⁻ z in L, ENNReal.ofReal (‖z - u‖ ^ (-α)) ∂volume.map e := by
            rw [he.map_eq]
      _ = ∫⁻ z in e ⁻¹' L,
            ENNReal.ofReal (‖(z + u) - u‖ ^ (-α)) ∂volume := by
              rw [setLIntegral_map hL.measurableSet (by fun_prop) he.measurable]
      _ = ∫⁻ z in e ⁻¹' L, f z ∂volume := by
            rw [setLIntegral_congr_fun (hL.measurableSet.preimage he.measurable)]
            intro z hz
            simp [f]
  have hsubset (z : ℂ) (hz : z ∈ e ⁻¹' L) : z ∈ B := by
    have hzu : z + u ∈ L := hz
    have hnorm : ‖z‖ = ‖(z + u) - u‖ := by rw [add_sub_cancel_right]
    have h1 := hLnorm (z + u) hzu
    have h2 := hKnorm u hu
    have hbound : ‖z‖ ≤ R₁ + R₂ := by
      rw [hnorm]
      apply le_of_lt
      calc
        ‖(z + u) - u‖ ≤ ‖z + u‖ + ‖u‖ := norm_sub_le _ _
        _ < R₁ + R₂ := add_lt_add h1 h2
    simpa [B, R, Metric.mem_closedBall, dist_zero_right] using hbound
  calc
    ∫⁻ z in L, ENNReal.ofReal (‖z - u‖ ^ (-α)) ∂volume =
        ∫⁻ z in e ⁻¹' L, f z ∂volume := hchange
    _ ≤ ∫⁻ z in B, f z ∂volume := lintegral_mono_set hsubset
    _ = C := rfl

/-- The planar pair kernel is integrable over a compact root set when its singularity exponent
is below the dimension. The uniform translated-kernel estimate reduces the product integral to
one finite local integral times the volume of the root set. -/
theorem complex_norm_pair_neg_rpow_lintegral_isCompact
    (K : Set ℂ) (hK : IsCompact K) (α : ℝ) (hαpos : 0 < α) (hα : α < 2) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ p in K ×ˢ K,
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-α)) ∂(volume.prod volume) ≤ C := by
  obtain ⟨C, hC, huniform⟩ :=
    complex_norm_sub_neg_rpow_lintegral_uniform_compacts K K hK hK α hαpos hα
  let f : ℂ × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((‖p.1 - p.2‖ ^ α)⁻¹)
  have hnorm : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖) := by fun_prop
  have hpow : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖ ^ α) :=
    (Real.continuous_rpow_const hαpos.le).measurable.comp hnorm
  have hf : Measurable f := by
    dsimp [f]
    exact ENNReal.measurable_ofReal.comp (measurable_inv.comp hpow)
  have hpair :
      ∫⁻ p in K ×ˢ K, f p ∂(volume.prod volume) =
        ∫⁻ x in K, ∫⁻ y in K, f (x, y) ∂volume ∂volume :=
    setLIntegral_prod f hf.aemeasurable
  have hinner (x : ℂ) (hx : x ∈ K) :
      ∫⁻ y in K, f (x, y) ∂volume ≤ C := by
    have hfun : (fun y : ℂ => f (x, y)) =
        fun y => ENNReal.ofReal (‖y - x‖ ^ (-α)) := by
      funext y
      dsimp [f]
      rw [Real.rpow_neg (norm_nonneg (y - x)), norm_sub_rev]
    rw [hfun]
    exact huniform x hx
  have houter :
      ∫⁻ x in K, ∫⁻ y in K, f (x, y) ∂volume ∂volume ≤ C * volume K := by
    calc
      ∫⁻ x in K, ∫⁻ y in K, f (x, y) ∂volume ∂volume
          ≤ ∫⁻ x in K, C ∂volume :=
            setLIntegral_mono measurable_const (fun x hx => hinner x hx)
      _ = C * volume K := by simp [lintegral_const]
  have hkernel : (fun p : ℂ × ℂ => ENNReal.ofReal (‖p.1 - p.2‖ ^ (-α))) = f := by
    funext p
    dsimp [f]
    rw [Real.rpow_neg (norm_nonneg (p.1 - p.2))]
  refine ⟨C * volume K, ENNReal.mul_ne_top hC hK.measure_ne_top, ?_⟩
  rwa [hkernel, hpair]
end DOZZ.Proofs
