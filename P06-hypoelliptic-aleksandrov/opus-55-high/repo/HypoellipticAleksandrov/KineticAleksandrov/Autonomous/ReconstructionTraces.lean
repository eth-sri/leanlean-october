module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionSource
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakAssembly

/-! # Boundary values and sequential traces of the actual reconstruction candidate

The candidate is phi minus the actual bounded-source Green potential. Boundary
values and limits are proved directly; no interior smoothness is asserted here.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA
open scoped Topology

/-- The actual pointwise difference used in homogeneous reconstruction. -/
def stripReconstructionCandidate (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : ℝ) (phi : Point → ℝ) (g : BoundedBorel Point) (p : Point) : ℝ :=
  phi p - stripSourcePotential H K T g p

/-- The actual candidate equals its prescribed terminal/lateral exit value. -/
theorem stripReconstructionCandidate_eqOn_exit (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (sMinus T : ℝ) (phi : Point → ℝ) (g : BoundedBorel Point) :
    EqOn (stripReconstructionCandidate H K T phi g) phi
      (reconstructionExit H sMinus T) := by
  intro p hp
  have hz : stripSourcePotential H K T g p = 0 := by
    rcases hp with ht | hv
    · exact duhamelPotential_eq_zero_of_terminal_le K T _
        _ (by aesop)
    · apply duhamelPotential_eq_zero_of_not_mem K T (nativeStripSource g)
        (sectionTwoPoint p)
      rw [movingDomain, PDE.mem_translateSet_iff_sub_mem, sub_zero]
      rw [intervalDomain, PDE.mem_oneDimensionalAxisBox_iff]
      change p.velocity 0 ∉ Set.Ioo H.lo H.hi
      grind
  change phi p - stripSourcePotential H K T g p = phi p
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
