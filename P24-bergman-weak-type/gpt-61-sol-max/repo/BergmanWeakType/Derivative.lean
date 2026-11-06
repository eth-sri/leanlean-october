module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

public section

attribute [fun_prop] HasDerivAt hasDerivAt_id hasDerivAt_const
  HasDerivAt.fun_add HasDerivAt.fun_mul HasDerivAt.fun_sub
  HasDerivAt.fun_div HasDerivAt.comp HasDerivAt.fun_pow
  Real.hasDerivAt_cos Real.hasDerivAt_sin Real.hasDerivAt_sqrt HasDerivAt.rpow_const

/-- Apply the calculus rules and normalize the resulting scalar identity. -/
macro "differentiate" : tactic => `(tactic| (
  eapply HasDerivAt.congr_deriv
  case h => fun_prop (disch := first | positivity | aesop)
  (try dsimp) <;> (try simp only [sub_sub, one_add_one_eq_two]) <;> field))
