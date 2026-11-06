module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DualityFromBound
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceBound

/-!
# The unit-time occupation duality

The whole-space source estimate is consumed at its complete form. The smooth-test
density theorem proves absolute continuity internally; one density works at every exponent.
The only analytic inputs are the explicit hypotheses of Hörmander's hypoellipticity theorem
and classical Dirichlet solvability (Lieberman, Theorem 5.14).
-/

 public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set SectionTwo
open HypoellipticAleksandrov.Parabolic


variable {d : ℕ}

/-- Unit-time occupation density with uniform constants and the full exponent range. -/
theorem occupation_duality
    (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) : type_of% (occupation_duality_of_whole_space_bound hH hd lam Lam hlam hLam
    (occupation_whole_space_bound hH hd lam Lam hlam hLam)) := occupation_duality_of_whole_space_bound hH hd lam Lam hlam hLam
    (occupation_whole_space_bound hH hd lam Lam hlam hLam)

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
