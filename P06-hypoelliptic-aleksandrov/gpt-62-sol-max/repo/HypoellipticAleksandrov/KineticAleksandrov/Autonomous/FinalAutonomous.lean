module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitMasses
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourBand
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.LocalisedAutonomous
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousHolder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimedCoreDomination

/-! # Assembly of the improved autonomous cylinder density

The four autonomous density steps combine into the coefficient-uniform estimate.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set Autonomous Holder
open scoped ENNReal

namespace Autonomous

/-- The improved cylinder density for smooth autonomous coefficients. -/
theorem belowFourDensityStatement_holds : BelowFourDensityStatement :=
  below_four_density_of_band
    (below_four_band_of_predecessors pushforwardStatement_holds restartTailStatement_holds
      positionVisitsStatement_holds positionVisitMassesStatement_holds coreDominationStatement_holds)
    pushforwardStatement_holds

end Autonomous

end HypoellipticAleksandrov.KineticAleksandrov
