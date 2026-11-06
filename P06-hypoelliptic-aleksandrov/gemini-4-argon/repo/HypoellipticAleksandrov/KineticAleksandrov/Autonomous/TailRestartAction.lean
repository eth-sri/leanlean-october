module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenBorel
import Mathlib.MeasureTheory.Measure.Prod

/-! # Native-state Green restart action -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo ProbabilityTheory
open scoped ENNReal

/- Restore a native state as a valid infinite-horizon pole. -/
def tailRestartPole (H r)
    (a : EvolutionState (intervalDomain H) (fun _ => 0) r) : StripPole H ⊤ :=
  ⟨activeRestartPoint H r a, WithTop.coe_lt_top _, by
    have ha := PDE.mem_translateSet_iff_sub_mem.mp a.2.1
    simpa only [activeRestartPoint, sub_zero, intervalDomain,
      PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, Interval.carrier] using ha⟩

/- The physical restarted pole is Borel in its native state. -/
def tailRestartQuery (H r)
    (q : ElapsedTime ⊤ × EvolutionState (intervalDomain H) (fun _ => 0) r) :
    EvolutionQuery (intervalDomain H) (fun _ => 0) :=
  ⟨(r, r + q.1.1, q.2.1), le_add_of_nonneg_right q.1.2.1.le, q.2.2⟩

/- The jointly varying restart query uses the already fixed Borel master kernel. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
