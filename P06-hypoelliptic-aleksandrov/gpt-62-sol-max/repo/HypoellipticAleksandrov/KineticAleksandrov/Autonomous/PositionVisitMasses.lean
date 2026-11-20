module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionTerminalDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitMassesStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCells
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCanonical
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreStartBandVisits

/-! # The source position-resolved mass package

Finiteness, support, the uniform count, the cell sum, and occupation domination
are proved internally. Only the precise full-space terminal domination conclusion
is taken as a hypothesis.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The corrected mass conditions, assuming the terminal domination estimate. -/
theorem positionVisitMassesStatement_holds :
    PositionVisitMassesStatement := by
  intro lam Lam hlam hLam
  refine ⟨enlargedVisitMassConstant lam Lam, enlargedVisitMassConstant_pos hlam hLam, ?_⟩
  intro A c J R T P hR hT hTR hbar hJ hvel
  dsimp only
  have hPT : P.time < P.time + T := by linarith
  have : IsFiniteMeasure (visitsFromZero A c J T P) :=
    enlargedVisitStarts_isFiniteMeasure A c J R T P
      hR hT hTR hbar hJ hvel
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · exact enlargedVisitStarts_ae_support A c J P.time (P.time + T)
      P le_rfl hPT
  · exact enlargedVisitStarts_mass_le A c J R T P hR hT hTR hbar hJ hvel
  · intro j
    exact enlargedPositionVisitMass_sum _ c P.time 0 j
  · intro N
    exact enlarged_active_occupation_le_fullspace A c J T hT P
      (hJ (subset_closure (_root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.enlargedEntrance_subset_active c hvel))) N
  exact enlarged_active_terminal_le_fullspace A c J P.time (P.time + T) P le_rfl hPT hJ

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
