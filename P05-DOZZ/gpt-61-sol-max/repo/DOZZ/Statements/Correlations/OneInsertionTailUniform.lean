/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.OneInsertionTailCoefficient
import DOZZ.Correlations.Tails.OneInsertionTail
import Batteries.Tactic.Alias

/-! The statement `DOZZ.oneInsertion_tail_uniform`,
proved by `DOZZ.Proofs.oneInsertion_tail_uniform`. -/

public section


namespace DOZZ

/-- Uniform one-insertion tail asymptotic [KRV, Lemma 7.1] for nonnegative tail multipliers. One
source representation serves every admissible error exponent, and the constant is chosen after that
exponent. -/
alias oneInsertion_tail_uniform := DOZZ.Proofs.oneInsertion_tail_uniform

end DOZZ
