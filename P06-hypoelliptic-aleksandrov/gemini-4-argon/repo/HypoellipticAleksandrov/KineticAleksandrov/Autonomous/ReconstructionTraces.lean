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

/- The actual pointwise difference used in homogeneous reconstruction. -/
def stripReconstructionCandidate (H )
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : ℝ) (phi : Point → ℝ) (g : BoundedBorel Point) (p : Point) : ℝ :=
  phi p - stripSourcePotential H K T g p

/- The actual candidate equals its prescribed terminal/lateral exit value. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
