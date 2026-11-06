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
open Set
open SectionTwo TheoremA


variable (H : Interval) (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))

/-- The actual pointwise difference used in homogeneous reconstruction. -/
def stripReconstructionCandidate
    (T : ℝ) (phi : Point → ℝ) (g : BoundedBorel Point) (p : Point) : ℝ :=
  phi p - stripSourcePotential H K T g p

/-- The actual candidate equals its prescribed terminal/lateral exit value. -/
theorem stripReconstructionCandidate_eqOn_exit
    (sMinus T : ℝ) (phi : Point → ℝ) (g : BoundedBorel Point) :
    EqOn (stripReconstructionCandidate H K T phi g) phi
      (reconstructionExit H sMinus T) := by
  intro p hp
  have hz : stripSourcePotential H K T g p = 0 := by
    rcases hp with ht | hv
    · exact duhamelPotential_eq_zero_of_terminal_le K T (nativeStripSource g)
        (sectionTwoPoint p) ((id (Eq.ge ht.left)))
    · apply duhamelPotential_eq_zero_of_not_mem K T (nativeStripSource g)
        (sectionTwoPoint p)
      change p.velocity ∉ movingDomain (intervalDomain H) (fun _ => 0) p.time
      rw [movingDomain, PDE.mem_translateSet_iff_sub_mem, sub_zero]
      rw [intervalDomain, PDE.mem_oneDimensionalAxisBox_iff]
      change p.velocity 0 ∉ Set.Ioo H.lo H.hi
      rcases hv.2.2 with hl | hh
      · rw [hl]
        exact fun h => (lt_irrefl H.lo) h.1
      · rw [hh]
        exact fun h => (lt_irrefl H.hi) h.2
  change phi p - stripSourcePotential H K T g p = phi p
  rw [hz, sub_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
