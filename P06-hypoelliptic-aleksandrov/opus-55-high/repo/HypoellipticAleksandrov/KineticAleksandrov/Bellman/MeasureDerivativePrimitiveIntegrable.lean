module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitive
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Local Lebesgue integrability of primitives of locally finite weighted measures -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

variable (μ : Measure ℝ)

/-- The primitive is bounded by the integral of |g| on any collar containing zero and x. -/
theorem bellmanMeasurePrimitive_norm_bound  [IsFiniteMeasureOnCompacts μ]
    (g : ℝ → ℝ) (hg : Continuous g) (a b x : ℝ) (hx : x ∈ Icc a b) :
    ‖bellmanMeasurePrimitive μ g 0 x‖ ≤
      ∫ z in Icc (min 0 a) (max 0 b), ‖g z‖ ∂μ := by
  have hs : uIoc (0) x ⊆ Icc (min 0 a) (max 0 b) := by
    grind
  have hi : IntegrableOn (fun z => ‖g z‖) (Icc (min 0 a) (max 0 b)) μ :=
    hg.norm.continuousOn.integrableOn_Icc
  exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    (setIntegral_mono_set hi (ae_of_all _ fun z => norm_nonneg _)
      (ae_of_all _ fun z hz => hs hz))

/-- A weighted measure primitive is Lebesgue integrable on every compact real interval. -/
theorem bellmanMeasurePrimitive_integrableOn_Icc 
    [IsFiniteMeasureOnCompacts μ] (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ) :
    IntegrableOn (bellmanMeasurePrimitive μ g 0) (Icc a b) volume := by
  have hm := bellmanMeasurePrimitive_stronglyMeasurable μ g hg.measurable 0
  let C := ∫ z in Icc (min 0 a) (max 0 b), ‖g z‖ ∂μ
  apply (integrable_const C).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact bellmanMeasurePrimitive_norm_bound μ g hg a b x hx

/-- The actual weighted measure primitive is locally Lebesgue integrable. -/
theorem bellmanMeasurePrimitive_locallyIntegrable 
    [IsFiniteMeasureOnCompacts μ] (g : ℝ → ℝ) (hg : Continuous g) :
    LocallyIntegrable (bellmanMeasurePrimitive μ g 0) volume := by
  intro x
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact bellmanMeasurePrimitive_integrableOn_Icc μ g hg _ _

end HypoellipticAleksandrov.KineticAleksandrov
