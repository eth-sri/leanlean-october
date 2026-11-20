module
public import GafniTao.WooleySourceTwist

@[expose] public section

/-!
# Wooley's Section 7 translated coefficient sequence

This file implements the literal coefficient family `c_y(alpha)` in
(7.14)--(7.16).  It is the affine pullback of the original coefficients to
`n = p^a y + xi`, twisted by the original polynomial phase.  The source's
normalization identities are proved exactly, including the zero-mass branch.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The exact sequence
`c_y(alpha) = gamma_{p^a y+xi} e(psi(p^a y+xi;alpha))`
from the line following (7.14). -/
def wooleySection7Coefficient {k : ℕ}
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (p a : ℕ) (hp : 0 < p) (xi : ℤ)
    {q : ℕ} [NeZero q] (alpha : Fin k → ZMod q) :
    WooleySourceSequence :=
  let pullback := wooleyAffinePullback gamma (p ^ a) (pow_pos hp a) xi
  let translated := wooleyAffinePolynomialSystem phi (p ^ a) xi
  wooleySourceTwist pullback
    (fun y => wooleySourcePolynomialPhase translated alpha y)

@[simp] theorem wooleySection7Coefficient_apply
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) (p a : ℕ) (hp : 0 < p) (xi : ℤ)
    {q : ℕ} [NeZero q] (alpha : Fin k → ZMod q) (y : ℤ) :
    wooleySection7Coefficient phi gamma p a hp xi alpha y =
      gamma ((p ^ a : ℕ) * y + xi) *
        wooleySourcePolynomialPhase phi alpha
          ((p ^ a : ℕ) * y + xi) := by
  simp [wooleySection7Coefficient, wooleySourcePolynomialPhase_affine]

/-- Admissibility is preserved by the Section 7 coefficient construction. -/
theorem WooleySourceSequence.Admissible.section7Coefficient
    {k : ℕ} {gamma : WooleySourceSequence}
    (hgamma : gamma.Admissible) (phi : WooleyPolynomialSystem k)
    (p a : ℕ) (hp : 0 < p) (xi : ℤ)
    {q : ℕ} [NeZero q] (alpha : Fin k → ZMod q) :
    (wooleySection7Coefficient phi gamma p a hp xi alpha).Admissible := by
  unfold wooleySection7Coefficient
  apply (hgamma.affinePullback (p ^ a) (pow_pos hp a) xi).twist
  intro y
  rw [wooleySourcePolynomialPhase_norm]

end

end GafniTao
