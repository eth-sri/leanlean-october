module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenCharacterization
import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.KineticAleksandrov.SectionTwo Filter
open scoped ENNReal Topology

/-- Finite time bounds the actual killed Green measure, without a normalization factor. -/
theorem stripGreenOfKernel_finite_time_mass (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripGreenOfKernel H K T e univ ≤ ENNReal.ofReal (T - e.1.time) := by
  rw [stripGreenOfKernel, Measure.map_apply (measurable_elapsedPhysicalPoint _ _)
    MeasurableSet.univ, preimage_univ]
  simpa using! (greenMeasure_mass_le K e.1.time (T - e.1.time) (sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)) (Measure.dirac (stripPoleState H T e)) _ (greenMeasure_spec K e.1.time _ (stripHorizon_pos H T e) _))

/-- The finite-time mass bound for the unique autonomous killed family. -/
theorem stripGreen_finite_time_mass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) :
    stripGreen hH hLE hlam hLam A H T e univ ≤ ENNReal.ofReal (T - e.1.time) :=
  stripGreenOfKernel_finite_time_mass H _ T e


/-- Every finite-horizon physical Green measure is finite by its proved time bound. -/
instance stripGreenOfKernel_isFiniteMeasure (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) :
    IsFiniteMeasure (stripGreenOfKernel H K T e) :=
  ⟨lt_of_le_of_lt (stripGreenOfKernel_finite_time_mass H K T e) ENNReal.ofReal_lt_top⟩

/-- A bounded Borel source is integrable against every finite strip Green measure. -/
theorem stripGreen_integrable_boundedBorel (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (g : BoundedBorel Point) :
    Integrable g (stripGreenOfKernel H K T e) := by
  obtain ⟨C, -, hg⟩ := g.exists_bound
  apply (integrable_const C).mono' g.measurable.aestronglyMeasurable
  exact Eventually.of_forall fun p => by simpa using hg p

/-- The bounded-source potential is the integral against the actual physical Green measure. -/
def stripPotentialOfKernel (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (e : StripPole H (T : WithTop ℝ)) : ℝ :=
  ∫ p, g p ∂stripGreenOfKernel H K T e

/-- A uniform source bound yields the exact finite-time potential estimate. -/
theorem stripPotentialOfKernel_abs_le (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (e : StripPole H (T : WithTop ℝ))
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C) :
    |stripPotentialOfKernel H K T g e| ≤ C * (T - e.1.time) := by
  have hm : (stripGreenOfKernel H K T e).real univ ≤ T - e.1.time := by
    simpa only [Measure.real, ENNReal.toReal_ofReal ((sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)).le)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (stripGreenOfKernel_finite_time_mass H K T e)
  have hb' : |stripPotentialOfKernel H K T g e| ≤
      C * (stripGreenOfKernel H K T e).real univ := by
    simpa [stripPotentialOfKernel] using (norm_integral_le_of_norm_le_const (f := (g : Point → ℝ)) (μ := stripGreenOfKernel H K T e) (Eventually.of_forall fun p => by simpa using hg p))
  exact hb'.trans (mul_le_mul_of_nonneg_left hm hC)

/-- Uniformly bounded pointwise-convergent Borel sources pass to their Green potentials. -/
theorem stripPotentialOfKernel_tendsto (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (g : ℕ → BoundedBorel Point)
    (f : BoundedBorel Point) (C : ℝ) (hg : ∀ n p, |g n p| ≤ C)
    (hlim : ∀ᵐ p ∂stripGreenOfKernel H K T e,
      Tendsto (fun n => g n p) atTop (𝓝 (f p))) :
    Tendsto (fun n => stripPotentialOfKernel H K T (g n) e) atTop
      (𝓝 (stripPotentialOfKernel H K T f e)) := by
  exact tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (g n).measurable.aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall fun p => by
      simpa using hg n p) hlim

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

