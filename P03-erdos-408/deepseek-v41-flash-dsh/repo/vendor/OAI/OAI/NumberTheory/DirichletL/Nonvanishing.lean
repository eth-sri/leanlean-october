module

public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

@[expose] public section

namespace OAI

/-!
# Nonvanishing of Dirichlet L-functions to the right of seven eighths

The main result excludes zeros of Dirichlet L-functions in the half-plane
`7 / 8 < re s`, apart from the principal character's pole at `s = 1`.
The corresponding nonvanishing statement for the Riemann zeta function follows.
-/

namespace DirichletCharacter


/-- Dirichlet L-functions do not vanish to the right of `7 / 8`, away from the
principal character's pole at `1`. -/
theorem LFunction_ne_zero_of_seven_eighths_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  SevenEighths.ProbeFinalAssemblyUnconditional.dirichlet_nonzero
    q (NeZero.ne q) χ s hs hpole

end DirichletCharacter

end OAI
