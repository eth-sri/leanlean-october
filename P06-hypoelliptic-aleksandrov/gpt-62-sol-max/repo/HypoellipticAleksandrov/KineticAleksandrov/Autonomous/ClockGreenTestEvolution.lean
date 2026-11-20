module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockCalculusAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockExtensionsSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance

/-! # The unique actual normalized case-I killed evolution of the position clock -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- The fixed normalized active interval, with the source's exact endpoints. -/
def clockNormalizedInterval : Interval := ⟨-3 / 4, 3 / 4, by norm_num⟩

/-- Realization of the literal globally extended normalized coefficient and drift. -/
def IsClockEvolution {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (E : StripEvolution clockNormalizedInterval) : Prop :=
  RealizesTerminalEvolution (intervalDomain clockNormalizedInterval) (fun _ => 0)
    (intervalDomain_measurable clockNormalizedInterval)
    (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) c.extendedVectorDrift E.1 E.2

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)

/-- Existence and uniqueness precede the canonical normalized family. -/
theorem existsUnique_clockEvolution :
    ∃! E : StripEvolution clockNormalizedInterval, IsClockEvolution A c e E := by
  have hs := c.extended_sourceSetting A e
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds (3 * lam / 5) (3 * Lam)
    (c.extendedCoefficient lam A.a e) hs.1
  exact (exists_terminalEvolution_of_classical 1 (by omega) (3 * lam / 5) (3 * Lam)
      (9 / 25) 9 (by linarith [A.positive]) (by linarith [A.positive, A.ordered]) (by norm_num) (by norm_num)
      (intervalDomain clockNormalizedInterval) (fun _ => 0)
      (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) c.extendedVectorDrift
      (intervalDomain_admissible clockNormalizedInterval) (zeroCurve_piecewiseC1 1)
      hBs hBsym hBell hs.2.1 hs.2.2.2.2.1.1 hs.2.2.2.2.1.2).existsUnique_realization

/-- The actual normalized clock evolution, selected only from its proved unique characterization. -/
def clockEvolution :
    StripEvolution clockNormalizedInterval :=
  (existsUnique_clockEvolution A c e).exists.choose

/-- The selected clock pair realizes exactly the extended case-I coefficient and drift. -/
theorem clockEvolution_spec :
    IsClockEvolution A c e (clockEvolution A c e) :=
  (existsUnique_clockEvolution A c e).exists.choose_spec

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
