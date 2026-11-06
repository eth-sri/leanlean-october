module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTailRectangle
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinatesRadial

/-! # Tonelli evaluation of the angular tail weight -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Measure Set

/- The radial reference strip has positive mass for every density degree. -/
theorem bellmanAngularTail_strip_mass (β : ℝ) (F : Measure ℝ)
    [IsFiniteMeasureOnCompacts F] :
    (bellmanRadialWeight β).prod F
      {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
        1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2} =
      bellmanRadialWeight β {s | 1 ≤ s.val ∧ s.val ≤ 2} *
        (∫⁻ y in {y : ℝ | 2 < |y|}, ENNReal.ofReal (|y| ^ (β - 4)) ∂F) := by
  have hm : MeasurableSet {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
      1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2} := by measurability
  rw [Measure.prod_apply_symm hm]
  have hf : (fun y => bellmanRadialWeight β
      ((fun s => (s, y)) ⁻¹' {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
        1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2})) =
      {y : ℝ | 2 < |y|}.indicator (fun y =>
        ENNReal.ofReal (|y| ^ (β - 4)) *
          bellmanRadialWeight β {s | 1 ≤ s.val ∧ s.val ≤ 2}) := by
    funext y
    by_cases hy : 2 < |y|
    · rw [indicator_of_mem (show y ∈ {y : ℝ | 2 < |y|} from hy)]
      have he : ((fun s => (s, y)) ⁻¹'
          {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
            1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2}) =
          {s : BellmanPositiveTime | 1 ≤ |y| * s.val ∧ |y| * s.val ≤ 2} := by
        ext s
        simp only [mem_preimage, mem_ofPred_eq, hy, true_and, abs_mul,
          abs_of_pos s.property, mul_comm s.val |y|]
      rw [he]
      let y := |y|
      have hy : 0 < y := by
        linarith
      have hm : MeasurableSet {s : BellmanPositiveTime | 1 ≤ s.val ∧ s.val ≤ 2} := by
        measurability
      have _h_inl_7 : Measure.map (bellmanRadialScale y hy) (bellmanRadialWeight β) = ENNReal.ofReal (y ^ (β - 4)) • bellmanRadialWeight β := by
        rw [bellmanRadialWeight, bellman_map_withDensity _ _ _ (by fun_prop),
          map_bellmanPositiveTimeVolume_radialScale, withDensity_smul_measure]
        have he : (fun s : BellmanPositiveTime =>
            ENNReal.ofReal (((bellmanRadialScale y hy).symm s).val ^ (3 - β))) =
            ENNReal.ofReal (y ^ (β - 3)) •
              (fun s : BellmanPositiveTime => ENNReal.ofReal (s.val ^ (3 - β))) := by
          funext s
          change ENNReal.ofReal ((y⁻¹ * s.val) ^ (3 - β)) = _
          rw [Real.mul_rpow (inv_nonneg.mpr hy.le) s.property.le,
            ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hy.le) _)]
          have hp : (y⁻¹) ^ (3 - β) = y ^ (β - 3) := by
            rw [← Real.rpow_neg_eq_inv_rpow]
            congr 1
            ring
          rw [hp]
          rfl
        rw [he, withDensity_smul _ (by fun_prop), smul_smul,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr hy.le)]
        have hp : y⁻¹ * y ^ (β - 3) = y ^ (β - 4) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hy]
          congr 1
          ring
        rw [hp]
      have he := congrArg (fun μ : Measure BellmanPositiveTime =>
          μ {s | 1 ≤ s.val ∧ s.val ≤ 2}) _h_inl_7
      rw [Measure.map_apply (bellmanRadialScale y hy).measurable hm,
        Measure.smul_apply, smul_eq_mul] at he
      exact he
    · rw [indicator_of_notMem (show y ∉ {y : ℝ | 2 < |y|} from hy)]
      have he : ((fun s => (s, y)) ⁻¹'
          {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
            1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2}) = ∅ := by
        ext s
        simp only [mem_preimage, mem_ofPred_eq, hy, false_and, mem_empty_iff_false]
      rw [he, measure_empty]
  rw [hf, lintegral_indicator (by measurability), lintegral_mul_const _ (by fun_prop)]
  exact mul_comm _ _

/- Local finiteness of the original measure implies finite weighted angular tail mass. -/
end HypoellipticAleksandrov.KineticAleksandrov
