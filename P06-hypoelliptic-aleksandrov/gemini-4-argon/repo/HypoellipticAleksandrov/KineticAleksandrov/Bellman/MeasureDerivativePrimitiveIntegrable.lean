module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitive
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Local Lebesgue integrability of primitives of locally finite weighted measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/- The primitive is bounded by the integral of |g| on any collar containing zero and x. -/
theorem bellmanMeasurePrimitive_locallyIntegrable (μ : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] (g : ℝ → ℝ) (hg : Continuous g) :
    LocallyIntegrable (bellmanMeasurePrimitive μ g 0) volume := by
  intro x
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  let a := (x - 1)
  let b := (x + 1)
  have hm := bellmanMeasurePrimitive_stronglyMeasurable μ g hg.measurable 0
  let C := ∫ z in Icc (min 0 a) (max 0 b), ‖g z‖ ∂μ
  apply (integrable_const C).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hs : uIoc (0 : ℝ) x ⊆ Icc (min 0 a) (max 0 b) := by
    intro z hz
    rcases le_total (0 : ℝ) x with h | h
    · rw [uIoc_of_le h] at hz
      exact ⟨(min_le_left 0 a).trans hz.1.le,
        hz.2.trans (hx.2.trans (le_max_right 0 b))⟩
    · rw [uIoc_of_ge h] at hz
      exact ⟨(min_le_right 0 a).trans (hx.1.trans hz.1.le),
        hz.2.trans (le_max_left 0 b)⟩
  have hi : IntegrableOn (fun z => ‖g z‖) (Icc (min 0 a) (max 0 b)) μ :=
    hg.norm.continuousOn.integrableOn_Icc
  exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    (setIntegral_mono_set hi (ae_of_all _ fun z => norm_nonneg (g z))
      (ae_of_all _ fun z hz => hs hz))

end HypoellipticAleksandrov.KineticAleksandrov
