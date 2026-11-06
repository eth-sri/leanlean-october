module

public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex

/-!
# Bound coherence for parabolic derivative indices

This file records that enlarging the parabolic-weight bound preserves the
underlying index and commutes with the fixed-bound successor operations.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex



variable {d M L : ℕ} (hML : M ≤ L) (beta : ParabolicDerivativeIndex d M)



/-- Enlarging the parabolic bound commutes with a fixed-bound velocity
successor. -/
@[simp] theorem castLE_velocitySucc
     (i : Fin d)
    (h : beta.1.parabolicWeight + 1 ≤ M) :
    castLE hML (velocitySucc beta i h) =
      velocitySucc (castLE hML beta) i (h.trans hML) := by
  apply Subtype.ext
  rfl

end HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex
