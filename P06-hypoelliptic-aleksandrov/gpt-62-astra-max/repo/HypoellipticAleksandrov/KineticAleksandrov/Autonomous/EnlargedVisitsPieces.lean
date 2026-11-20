module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsCells
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationMeasure

/-! # Active pieces in the canonical enlarged-strip decomposition

Source: companion paper, Lemma 8.6. These are actual kernel mixtures,
not arbitrary families with a proposed domination property.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open scoped Classical

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (J : Interval) (s T : ℝ) (P : Point) (N : ℕ) (b : ℝ)

include hlam hLam A in
/-- The physical Green kernel before a finite horizon, including initial poles. -/
def enlargedVisitGreenKernel (H : FiniteIntervalUnion) (T : ℝ) :
    Kernel Point Point :=
  visitExtendKernel (enlargedVisitPoleSet H T) (measurableSet_enlargedVisitPoleSet H T)
    (fun p => finiteUnionGreen hlam hLam A H T (enlargedVisitPole H T p))
    ((finiteUnionGreen_measurable hlam hLam A H T).comp
      (measurable_enlargedVisitPole H T))

include hlam hLam A c J s T P in
/-- The occupation measure of active piece number `n+1`. -/
def enlargedActivePiece (n : ℕ) : Measure Point :=
  enlargedVisitGreenKernel hlam hLam A (visitActiveUnion c J) T ∘ₘ
    enlargedVisitEntrance hlam hLam A c J s T P n

include hlam hLam A c J b in
/-- The actual terminal family at time `b`, with the zero-duration initial value included. -/
def enlargedActiveTerminalFamily
    (p : Point) : Measure Point :=
  if p.time = b ∧ p.velocity 0 ∈ (visitActiveUnion c J).carrier then Measure.dirac p
  else (enlargedVisitExitKernel hlam hLam A (visitActiveUnion c J) b p).restrict
    {z | z.time = b}

include hlam hLam A c J s T P N b in
/-- The first `N` active terminal measures, using actual mixtures against visit starts. -/
def enlargedActiveTerminal : Measure Point :=
  ∑ n ∈ Finset.range N,
    (enlargedVisitEntrance hlam hLam A c J s T P n).bind
      (enlargedActiveTerminalFamily hlam hLam A c J b)

include b in
/-- Insert the observation time into physical position-velocity coordinates. -/
def enlargedTerminalPoint (z : Z) : Point :=
  ⟨b, fun _ => z.1, fun _ => z.2⟩

include hlam hLam A P b in
/-- The source full-space terminal measure in the same physical spacetime coordinates. -/
def enlargedFullSpaceTerminal : Measure Point :=
  (kernelXV (fullSpaceEvolution hlam hLam A) (Real.toNNReal (b - P.time))
    (P.position 0, P.velocity 0)).map (enlargedTerminalPoint b)

include hlam hLam A P in
/-- Full-space occupation on the elapsed source window, retaining physical spacetime. -/
def enlargedFullSpaceOccupation (T : ℝ) : Measure Point :=
  ((volume.restrict (Ioc 0 T)) ⊗ₘ
    physicalElapsedKernel (fullSpaceEvolution hlam hLam A)
      (P.position 0, P.velocity 0)).map
        (fun tz => enlargedTerminalPoint (P.time + tz.1) tz.2)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
