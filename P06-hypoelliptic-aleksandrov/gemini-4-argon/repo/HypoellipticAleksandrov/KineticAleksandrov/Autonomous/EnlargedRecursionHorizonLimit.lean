module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonConsistency
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripMeasureExt
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripTimeMarginal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Right horizon limits of the actual finite-strip exit measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology

/- The actual occupation measure has no mass on a fixed physical time slice. -/
theorem enlarged_stripGreen_time_slice_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H ) (e : StripPole H ⊤) (b : ℝ) :
    stripGreen hH hLE hlam hLam A H ⊤ e {p | p.time = b} = 0 := by
  have h := stripGreen_timeMarginal hH hLE hlam hLam A H ⊤ e {b}
    (measurableSet_singleton b)
  simp only [Real.volume_singleton, mem_singleton_iff] at h
  exact le_antisymm h zero_le

/- Every compact smooth probe has the correct right limit as its exit horizon decreases. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
