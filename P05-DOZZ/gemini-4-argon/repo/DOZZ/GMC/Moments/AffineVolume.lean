/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Lebesgue change of variables for local affine charts in the complex plane. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- Real dilation on the complex plane scales area by the inverse square. -/
theorem complexVolume_map_smul {c} (hc : c ≠ 0) :
    Measure.map (fun z : ℂ => c • z) (volume : Measure ℂ) =
      ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume := by
  simpa [Complex.finrank_real_complex] using
    (Measure.map_addHaar_smul (μ := (volume : Measure ℂ)) hc)


/-- A positive complex dilation maps a centered closed disk to the disk with its scaled radius. -/
theorem complex_affine_image_closedBall {a} {c R} (hc : 0 < c) :
    (fun z : ℂ => a + c • z) '' Metric.closedBall (0 : ℂ) R =
      Metric.closedBall a (c * R) := by
  have hdist x : dist (a + c • x) a = c * dist x 0 := by
    calc
      dist (a + c • x) a = ‖(a + c • x) - a‖ := dist_eq_norm _ _
      _ = ‖c • x‖ := by congr 1; abel
      _ = ‖c‖ * ‖x‖ := norm_smul _ _
      _ = c * dist x 0 := by
        rw [Real.norm_eq_abs, abs_of_pos hc, dist_eq_norm, sub_zero]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, hdist]
    nlinarith [mul_le_mul_of_nonneg_left (show dist x 0 ≤ R by simpa [Metric.mem_closedBall] using hx) (le_of_lt hc)]
  · intro hy
    let x := (c⁻¹ : ℝ) • (y - a)
    have hdistInv : dist x 0 = c⁻¹ * dist y a := by
      dsimp [x]
      calc
        dist ((c⁻¹ : ℝ) • (y - a)) 0 = ‖(c⁻¹ : ℝ) • (y - a)‖ := by
          rw [dist_eq_norm, sub_zero]
        _ = c⁻¹ * ‖y - a‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
        _ = c⁻¹ * dist y a := by rw [dist_eq_norm]
    have hx : x ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, hdistInv]
      calc
        c⁻¹ * dist y a ≤ c⁻¹ * (c * R) :=
          mul_le_mul_of_nonneg_left (by simpa [Metric.mem_closedBall] using hy) (le_of_lt (inv_pos.mpr hc))
        _ = R := by field_simp [hc.ne']
    refine ⟨x, hx, ?_⟩
    dsimp [x]
    calc
      a + c • ((c⁻¹ : ℝ) • (y - a)) = a + (y - a) := by
        rw [smul_smul]
        simp [hc.ne']
      _ = y := by abel


/-- Integral form of the affine change of variables on a restricted planar domain. The inverse
Jacobian appears because the affine map is pushed forward. -/
theorem complex_integral_affine_restrict
    {a : ℂ} {c : ℝ} (hc : c ≠ 0) (K : Set ℂ)
    (himage : MeasurableSet ((fun z : ℂ => a + c • z) '' K))
    (g : ℂ → ℝ) (hg : Measurable g) :
    (∫ y, g y ∂volume.restrict ((fun z : ℂ => a + c • z) '' K)) =
      (|(c ^ 2)⁻¹|)⁻¹ *
        ∫ x, g (a + c • x) ∂volume.restrict K := by
  have complexVolume_map_affine_restrict : Measure.map (fun z : ℂ => a + c • z) (volume.restrict K) = ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume.restrict ((fun z : ℂ => a + c • z) '' K) := by
    have complexVolume_map_affine {a} : Measure.map (fun z : ℂ => a + c • z) (volume : Measure ℂ) = ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume := by
      calc
        Measure.map (fun z : ℂ => a + c • z) volume =
            (Measure.map (fun z : ℂ => c • z) volume).map (fun z => a + z) := by
              rw [(show (fun z => a + c • z) = (fun z => a + z) ∘ (fun z : ℂ => c • z) by funext z; rfl), ← Measure.map_map (measurable_const_add a) (measurable_const_smul c)]
        _ = (ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume).map (fun z => a + z) := by
              rw [complexVolume_map_smul hc]
        _ = ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume := by
              rw [Measure.map_smul _ (measurable_const_add a).aemeasurable,
                Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := volume) a]
    let f : ℂ → ℂ := fun z => a + c • z
    calc
      Measure.map f (volume.restrict K) = (Measure.map f volume).restrict (f '' K) := by
        rw [Measure.restrict_map (show Measurable f by fun_prop) himage, Set.preimage_image_eq _ (show Function.Injective f by intro x y hxy; exact (smul_right_injective ℂ hc) (add_left_cancel hxy))]
      _ = (ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume).restrict (f '' K) := by
        rw [complexVolume_map_affine]
      _ = ENNReal.ofReal (|(c ^ 2)⁻¹|) • volume.restrict (f '' K) := by
        rw [Measure.restrict_smul]
  let J := (c ^ 2)⁻¹
  have hc2 := sq_pos_of_ne_zero hc
  have hgm : AEStronglyMeasurable g (Measure.map (fun z : ℂ => a + c • z)
      (volume.restrict K)) := hg.aestronglyMeasurable
  have hint := integral_map (show Measurable (fun z : ℂ => a + c • z) by fun_prop).aemeasurable hgm
  rw [(complexVolume_map_affine_restrict), integral_smul_measure] at hint
  have hcoef : (ENNReal.ofReal (|(c ^ 2)⁻¹|)).toReal = J := by
    calc
      (ENNReal.ofReal (|(c ^ 2)⁻¹|)).toReal = |(c ^ 2)⁻¹| :=
        ENNReal.toReal_ofReal (abs_nonneg _)
      _ = (c ^ 2)⁻¹ := abs_of_pos (inv_pos.mpr hc2)
      _ = J := rfl
  have hsource : J * (∫ y, g y ∂volume.restrict ((fun z : ℂ => a + c • z) '' K)) =
      ∫ x, g (a + c • x) ∂volume.restrict K := by
    rw [hcoef, smul_eq_mul] at hint
    exact hint
  calc
    (∫ y, g y ∂volume.restrict ((fun z : ℂ => a + c • z) '' K)) =
        J⁻¹ * (J * ∫ y, g y ∂volume.restrict ((fun z : ℂ => a + c • z) '' K)) := by
          field_simp [(show J ≠ 0 by dsimp [J]; exact inv_ne_zero (pow_ne_zero 2 hc))]
    _ = J⁻¹ * ∫ x, g (a + c • x) ∂volume.restrict K := by rw [hsource]
    _ = (|(c ^ 2)⁻¹|)⁻¹ *
        ∫ x, g (a + c • x) ∂volume.restrict K := by rw [(show J = |(c ^ 2)⁻¹| by dsimp [J]; exact (abs_of_pos (inv_pos.mpr hc2)).symm)]

end DOZZ.Proofs
