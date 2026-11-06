module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMass
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Bounded-source integration and dominated limits for finite strip Green measures

These lemmas concern the actual unique Green measure. They do not assert smoothness for
Borel sources. Source approximation and its weak equation are separate steps.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped Topology

/-- Every finite-horizon physical Green measure is finite by its proved time bound. -/
instance stripGreenOfKernel_isFiniteMeasure (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) :
    IsFiniteMeasure (stripGreenOfKernel H K T e) :=
  ⟨lt_of_le_of_lt (stripGreenOfKernel_finite_time_mass H K T e) ENNReal.ofReal_lt_top⟩

variable (H : Interval) (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)

/-- A bounded Borel source is integrable against every finite strip Green measure. -/
theorem stripGreen_integrable_boundedBorel
    (e : StripPole H (T : WithTop ℝ)) (g : BoundedBorel Point) :
    Integrable g (stripGreenOfKernel H K T e) := by
  obtain ⟨C, -, hg⟩ := g.exists_bound
  apply (integrable_const C).mono' g.measurable.aestronglyMeasurable
  exact Eventually.of_forall fun p => hg p

variable (g : BoundedBorel Point) (e : StripPole H (T : WithTop ℝ))

/-- The bounded-source potential is the integral against the actual physical Green measure. -/
def stripPotentialOfKernel
     : ℝ :=
  ∫ p, g p ∂stripGreenOfKernel H K T e

/-- A uniform source bound yields the exact finite-time potential estimate. -/
theorem stripPotentialOfKernel_abs_le

    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C) :
    |stripPotentialOfKernel H K T g e| ≤ C * (T - e.1.time) := by
  have hb := norm_integral_le_of_norm_le_const (f := (g : Point → ℝ))
    (μ := stripGreenOfKernel H K T e) (C := C)
    (Eventually.of_forall fun p => hg p)


  exact (show |stripPotentialOfKernel H K T g e| ≤
      C * (stripGreenOfKernel H K T e).real univ by
      exact hb).trans (mul_le_mul_of_nonneg_left (by

      simpa only [Measure.real, ENNReal.toReal_ofReal ((sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)).le)] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (stripGreenOfKernel_finite_time_mass H K T e)) hC)

/-- Uniformly bounded pointwise-convergent Borel sources pass to their Green potentials. -/
theorem stripPotentialOfKernel_tendsto
    (e : StripPole H (T : WithTop ℝ)) (g : ℕ → BoundedBorel Point)
    (f : BoundedBorel Point) (C : ℝ) (hg : ∀ n p, |g n p| ≤ C)
    (hlim : ∀ᵐ p ∂stripGreenOfKernel H K T e,
      Tendsto (fun n => g n p) atTop (𝓝 (f p))) :
    Tendsto (fun n => stripPotentialOfKernel H K T (g n) e) atTop
      (𝓝 (stripPotentialOfKernel H K T f e)) := tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (g n).measurable.aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall fun p => hg n p) hlim

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
