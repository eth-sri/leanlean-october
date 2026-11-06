module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakGreenSigned
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsQuadratic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeak

/-! # Actual physical bounded-source potentials, weak forcing, and zero boundary limits

All source integrals use the unique killed Green measure. The only external hypotheses
of the canonical construction are the evolution inputs. No regularity of a Borel
source potential is asserted.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology

/- Exchange physical position and velocity in a bounded Borel source. -/
def nativeStripSource (g : BoundedBorel Point) : BoundedBorel Point :=
  ⟨g ∘ sectionTwoPoint, g.measurable.comp (continuous_sectionTwoPoint 1).measurable, by
    obtain ⟨C, hC, hg⟩ := g.exists_bound
    exact ⟨C, hC, fun p => hg _⟩⟩

/- The physical source potential is the actual Duhamel potential in native coordinates. -/
def stripSourcePotential (H )
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : ℝ) (g : BoundedBorel Point) (p : Point) : ℝ :=
  duhamelPotential K T (nativeStripSource g) (sectionTwoPoint p)

/- Every valid physical pole has the actual signed bounded-source Green representation. -/
theorem stripSourcePotential_eq_green (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (e : StripPole H (T : WithTop ℝ)) :
    stripSourcePotential H K T g e.1 = stripPotentialOfKernel H K T g e := by
  have heT : e.1.time < T := WithTop.coe_lt_coe.mp e.2.1
  have hh := duhamelPotential_eq_green_bounded H K T (nativeStripSource g)
    e.1.time heT (stripPoleState H T e)
    (greenMeasure K e.1.time _ (stripHorizon_pos H T e) _)
    (greenMeasure_spec K _ _ _ _)
  rw [stripPotentialOfKernel, stripGreenOfKernel,
    integral_map (measurable_elapsedPhysicalPoint _ _).aemeasurable
      (show AEStronglyMeasurable (fun p : Point => g p) _ from
        g.measurable.aestronglyMeasurable)]
  exact hh

/- Exchanging physical coordinates converts the actual source potential to native weak forcing. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
