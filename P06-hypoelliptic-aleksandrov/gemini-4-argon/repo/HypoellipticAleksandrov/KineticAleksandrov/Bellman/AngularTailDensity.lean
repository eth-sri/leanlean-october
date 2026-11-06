module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTailMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensities
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTailRectangle
import Mathlib.MeasureTheory.Measure.OpenPos
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegration
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTailRadial

/-! # The literal angular density tail estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set
open Measure

/- The finite weighted angular mass is the source tail integrability for its actual density. -/
theorem bellmanAngularDensity_tail (β : ℝ) (μ : Measure BellmanPuncturedPlane)
    [IsFiniteMeasureOnCompacts μ] (F ) [IsFiniteMeasureOnCompacts F]
    (hrep : μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F)
    (f : ℝ → ℝ) (hF : F = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf : LocallyIntegrable f volume) (hn : ∀ᵐ x ∂volume, 0 ≤ f x) :
    IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume := by
  let S : Set ℝ := {y | 2 < |y|}
  have hS : MeasurableSet S := by measurability
  have hm : Measurable (fun y : ℝ => |y| ^ (β - 4)) := by fun_prop
  have hi : IntegrableOn (fun y : ℝ => |y| ^ (β - 4)) S F := by
    apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (ae_of_all _ fun y => Real.rpow_nonneg (abs_nonneg y) _)).mp
    have _h_xinl_0 : (∫⁻ y in {y : ℝ | 2 < |y|}, ENNReal.ofReal (|y| ^ (β - 4)) ∂F) < ⊤ := by
      have hm : (bellmanRadialWeight β).prod F {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧ 1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2} < ⊤ := by
        have hm := bellmanAngularTailRectangle_isCompact.measurableSet
        have he : (bellmanRadialWeight β).prod F
            (bellmanAngularPoint ⁻¹' bellmanAngularTailRectangle) =
            μ.restrict {q | 0 < q.val.1} bellmanAngularTailRectangle := by
          rw [hrep, bellmanAngularRep, Measure.map_apply continuous_bellmanAngularPoint.measurable hm]
        calc
          _ ≤ (bellmanRadialWeight β).prod F
              (bellmanAngularPoint ⁻¹' bellmanAngularTailRectangle) :=
            measure_mono bellmanAngularTail_strip_subset
          _ = _ := he
          _ ≤ μ bellmanAngularTailRectangle := Measure.restrict_le_self _
          _ < ⊤ := bellmanAngularTailRectangle_isCompact.measure_lt_top
      rw [bellmanAngularTail_strip_mass] at hm
      have _h_inl_8 : bellmanRadialWeight β {s : BellmanPositiveTime | 1 ≤ s.val ∧ s.val ≤ 2} ≠ 0 := by
          have ho : IsOpen {s : BellmanPositiveTime | 1 < s.val ∧ s.val < 2} := by
            exact (isOpen_lt continuous_const continuous_subtype_val).inter
              (isOpen_lt continuous_subtype_val continuous_const)
          have hn : ({s : BellmanPositiveTime | 1 < s.val ∧ s.val < 2} : Set _).Nonempty := by
            refine ⟨⟨3 / 2, by norm_num⟩, ?_⟩
            norm_num
          have hm := ho.measure_pos (bellmanRadialWeight β) hn
          apply ne_of_gt
          exact hm.trans_le (measure_mono (fun s hs => ⟨hs.1.le, hs.2.le⟩))

        /- Integrating the two-sided velocity strips gives the literal angular tail factor. -/
      exact ENNReal.lt_top_of_mul_ne_top_right hm.ne _h_inl_8
    exact _h_xinl_0.ne
  have hfm := hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [hF, IntegrableOn, restrict_withDensity hS] at hi
  have ht := (integrable_withDensity_iff_integrable_smul₀' hfm.restrict
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)).mp hi
  apply ht.congr
  filter_upwards [ae_restrict_of_ae hn] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

end HypoellipticAleksandrov.KineticAleksandrov
