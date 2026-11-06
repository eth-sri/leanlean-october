module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceRestriction
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorWeak
import all HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorWeak

open private HypoellipticAleksandrov.KineticAleksandrov.LocalA.corrector_integrable_mul_test from HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorWeak


/-! # Classical residuals and cancellation of genuine signed weak sources -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Evolution SectionTwo Occupation

/-- Integration by parts for the classical residual of a smooth coefficient. -/
alias localRepresentation_classical_weak := _root_.HypoellipticAleksandrov.KineticAleksandrov.LocalA.borelCorrector_classical_weak





/-- Opposite genuine weak sources cancel; this is internal weak-equation calculus. -/
alias localRepresentation_weak_cancel := _root_.HypoellipticAleksandrov.KineticAleksandrov.LocalA.borelCorrector_weak_cancel


end HypoellipticAleksandrov.KineticAleksandrov.LocalA
