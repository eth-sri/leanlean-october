module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripUnionRestart
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsClosedComponent
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripExit

/-! # Component independence of the genuine internal-exit restart measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- The certified component pole inclusion is measurable in the existing subtype carrier. -/
theorem measurable_componentPoleInclusion (H : FiniteIntervalUnion) (i : Fin H.count)
    (T : WithTop ℝ) : Measurable (componentPoleInclusion H i T) :=
  measurable_subtype_coe.subtype_mk

/- The actual union restart on a component is the image of that component's actual restart. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
