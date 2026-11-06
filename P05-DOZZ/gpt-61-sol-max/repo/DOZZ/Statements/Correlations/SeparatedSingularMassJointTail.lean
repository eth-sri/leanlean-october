/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.OneInsertionTailCoefficient
import DOZZ.Correlations.SeparatedTail.JointTail
import Batteries.Tactic.Alias

/-! The statement `DOZZ.separatedSingularMass_joint_tail`,
proved by `DOZZ.Proofs.separatedSingularMass_joint_tail`. -/

public section


namespace DOZZ

/-- The separated-mass near-independence inequality, with the compact geometry, charge slack, and
multiplier bounds needed for one uniform constant. -/
alias separatedSingularMass_joint_tail := DOZZ.Proofs.separatedSingularMass_joint_tail

end DOZZ
