module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCountBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellsSlab
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnTime
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCountReturnBridge
import Mathlib.Tactic

/-! # Position-cell concentration from the literal source start and time-count conclusions

The two conditional inputs are exactly the source slab start inequality and
the source time-bin count assigned to AU-14a. Box concentration is derived
from the return-time chain relative to its explicit preliminary P6 input.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- Every canonical observed visit count is finite, with an arbitrary positive horizon. -/
theorem visitsFromZero_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point)
    (hbar : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (hT : 0 < T) (hvel : P.velocity 0 ∈ closure c.entrance) :
    IsFiniteMeasure (visitsFromZero hH hLE hlam hLam A c J T P) :=
  enlargedVisitStarts_isFiniteMeasure hH hLE hlam hLam A c J (1 + T) T P
    (by linarith) hT (by nlinarith) hbar hJ hvel

/- Source position concentration, including the initial atom and the truncated final bin. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
