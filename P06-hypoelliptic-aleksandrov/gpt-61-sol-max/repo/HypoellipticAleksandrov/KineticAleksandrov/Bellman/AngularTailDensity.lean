module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTailMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensities
import Mathlib.Tactic

/-! # The literal angular density tail estimate -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The finite weighted angular mass is the source tail integrability for its actual density. -/
theorem bellmanAngularDensity_tail (β : ℝ) (μ : Measure BellmanPuncturedPlane)
    [IsFiniteMeasureOnCompacts μ] (F : Measure ℝ) [IsFiniteMeasureOnCompacts F]
    (hrep : μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F)
    (f : ℝ → ℝ) (hF : F = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf : LocallyIntegrable f ) (hn : ∀ᵐ x, 0 ≤ f x) :
    IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|}  := by
  let sharedTerm_0cb79d2c52 := ((fun y : ℝ => |y| ^ (β - 4)))



  have hi : IntegrableOn sharedTerm_0cb79d2c52 ({y | 2 < |y|}) F := by
    apply (lintegral_ofReal_ne_top_iff_integrable (show Measurable sharedTerm_0cb79d2c52 by fun_prop).aestronglyMeasurable
      (ae_of_all _ fun y => Real.rpow_nonneg (abs_nonneg y) _)).mp
    exact (bellmanAngularTail_lintegral_finite β μ F hrep).ne

  rw [hF, IntegrableOn, restrict_withDensity (by measurability)] at hi
  have ht := (integrable_withDensity_iff_integrable_smul₀' hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)).mp hi
  apply ht.congr
  filter_upwards [ae_restrict_of_ae hn] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

end HypoellipticAleksandrov.KineticAleksandrov
