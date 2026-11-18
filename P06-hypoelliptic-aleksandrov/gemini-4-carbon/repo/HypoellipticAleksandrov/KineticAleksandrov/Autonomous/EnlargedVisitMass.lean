module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassSummation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionOccupation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionTerminalMass
import Mathlib.Tactic

/-! # Canonical enlarged-strip finiteness and uniform total visit count -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- An explicit ellipticity-only constant for the enlarged-strip visit count. -/
def enlargedVisitMassConstant (lam Lam : ℝ) : ℝ :=
  9 / 5 + 16 / 5 * (128 * Lam / lam * Real.sqrt (2 * Lam))

/-- The explicit counting constant is positive under the source ellipticity assumptions. -/
theorem enlargedVisitMassConstant_pos {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) : 0 < enlargedVisitMassConstant lam Lam := by
  have hLp : 0 < Lam := hlam.trans_le hLam
  unfold enlargedVisitMassConstant
  positivity

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
