module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtension
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonLimit
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation

/-! # Bounded homogeneous potentials stopped at an observation time -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter Parabolic
open SectionTwo TheoremA Evolution
open scoped Classical
open scoped Topology

/- Keep a homogeneous potential up to the observation time and set it to zero afterwards. -/
def enlargedStoppedPotential (b : ℝ) (u : Point → ℝ) (p : Point) : ℝ :=
  if p.time ≤ b then u p else 0

/- A continuous past potential has a measurable stopped extension. -/
theorem enlargedStoppedPotential_integrable (b : ℝ) (u : Point → ℝ)
    (hc : ContinuousOn u {p | p.time ≤ b}) (M ) (hM : 0 ≤ M)
    (hb : ∀ p, p.time ≤ b → |u p| ≤ M) (mu : Measure Point) [IsFiniteMeasure mu] :
    Integrable (enlargedStoppedPotential b u) mu := by
  have _h_inl_13 : Measurable (enlargedStoppedPotential b u) := by
      exact (
    hc.measurable_piecewise continuousOn_const
        (isClosed_le continuous_time continuous_const).measurableSet
    )
  apply Integrable.mono' (integrable_const M)
    _h_inl_13.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs]
  unfold enlargedStoppedPotential
  split
  · exact hb p ‹p.time ≤ b›
  · simpa only [abs_zero] using hM

/- The stopped exit action is bounded by the original homogeneous potential value.
Its C112 premises are discharged by the supplied full-space classical potential. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
