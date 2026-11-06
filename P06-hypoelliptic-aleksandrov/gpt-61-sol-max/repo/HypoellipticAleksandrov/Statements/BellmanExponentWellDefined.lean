module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.ExponentWellDefined
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.ExponentSetting
import Batteries.Tactic.Alias



/-!
# Well-definedness of the homogeneous adjoint exponent

Companion paper, Appendix B: the supremum of the admissible degrees is a unique real least
upper bound.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Well-definedness: the supremum is a unique real least upper bound.
Nonemptiness and boundedness are proof steps, never additional hypotheses. -/
alias existsUnique_bellmanAdjointExponent := _root_.HypoellipticAleksandrov.KineticAleksandrov.existsUnique_bellmanAdjointExponent_aux

end HypoellipticAleksandrov.KineticAleksandrov
