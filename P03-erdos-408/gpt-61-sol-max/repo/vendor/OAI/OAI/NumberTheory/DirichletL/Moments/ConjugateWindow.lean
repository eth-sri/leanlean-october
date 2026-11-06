module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.CubicSieve.ConjugateProfiles

public import OAI.NumberTheory.DirichletL.Moments.HeckeColumnWindow

@[expose] public section

namespace OAI


open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentConjugateWindow
open FourierBridge CenteredMomentSmooth

theorem star_logPhase  t u  : star (logPhase t u)=logPhase (-t) u := by solve_by_elim [_root_.OAI.SecondPassIntegration.logPhase_conjugate]

theorem star_columnPhase  V   u t  :
    star (columnPhase V u t)=columnPhase (fun x => star (V x)) u (-t) := by
  simp_all [columnPhase, star_logPhase, rootWindow]

end SevenEighths.CenteredMomentConjugateWindow



end OAI
