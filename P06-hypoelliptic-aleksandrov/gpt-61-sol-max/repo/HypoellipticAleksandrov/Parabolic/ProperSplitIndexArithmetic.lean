module

public import HypoellipticAleksandrov.Parabolic.GenericParabolicIndexArithmetic
import Aesop



/-!
# Proper-split parabolic-index arithmetic

This file records the one-weight gain on the right side of a proper
time--velocity multi-index split and the bounded derivative indices used for
the resulting value, gradient, and Hessian factors.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic



namespace TimeVelocityMultiIndex

/-- A nonzero time--velocity multi-index has positive parabolic weight. -/
theorem parabolicWeight_pos_of_ne_zero
    {d : ℕ} {alpha : TimeVelocityMultiIndex d}
    (halpha : alpha ≠ 0) :
    0 < alpha.parabolicWeight := by
  by_contra hweight
  apply halpha
  have hweight_zero  :=
    Nat.eq_zero_of_not_pos hweight
  have htime : alpha.timeOrder = 0 := by
    unfold TimeVelocityMultiIndex.parabolicWeight at hweight_zero
    unfold VelocityMultiIndex.parabolicWeight at hweight_zero
    omega
  have hvelocity_order : alpha.velocity.order = 0 := by
    unfold TimeVelocityMultiIndex.parabolicWeight at hweight_zero
    unfold VelocityMultiIndex.parabolicWeight at hweight_zero
    omega
  funext c
  rcases c with _ | i
  · exact htime
  · simp_all [VelocityMultiIndex.order] <;> aesop

/-- A proper split loses at least one parabolic weight on its right side. -/
theorem Split.parabolicWeight_right_add_one_le
    {d : ℕ} {beta : TimeVelocityMultiIndex d}
    (gamma : TimeVelocityMultiIndex.Split beta)
    (hproper : gamma.left ≠ 0) :
    gamma.right.parabolicWeight + 1 ≤ beta.parabolicWeight := by
  have hleft := parabolicWeight_pos_of_ne_zero hproper
  have hsum := gamma.parabolicWeight_left_add_parabolicWeight_right
  omega

end TimeVelocityMultiIndex

namespace ParabolicDerivativeIndex

/-- The ordered two-velocity right factor in a proper commutator split. -/
def properSplitRightVelocityTwo
    {d M : ℕ}
    (beta : ParabolicDerivativeIndex d M)
    (gamma : TimeVelocityMultiIndex.Split beta.1)
    (hproper : gamma.left ≠ 0)
    (j i : Fin d) :
    ParabolicDerivativeIndex d (M + 1) :=
  ⟨gamma.right + Pi.single (velocityCoord j) 1 +
      Pi.single (velocityCoord i) 1, by
    simp only [TimeVelocityMultiIndex.parabolicWeight_add,
      TimeVelocityMultiIndex.parabolicWeight_single_velocity]
    have hloss := gamma.parabolicWeight_right_add_one_le hproper
    omega⟩

variable {d M : ℕ} (beta : ParabolicDerivativeIndex d M) (gamma : TimeVelocityMultiIndex.Split beta.1) (hproper : gamma.left ≠ 0)

/-- The one-velocity right factor in a proper commutator split. -/
def properSplitRightVelocity

    (j : Fin d) :
    ParabolicDerivativeIndex d (M + 1) :=
  ⟨gamma.right + Pi.single (velocityCoord j) 1, by
    simp only [TimeVelocityMultiIndex.parabolicWeight_add,
      TimeVelocityMultiIndex.parabolicWeight_single_velocity]
    have hloss := gamma.parabolicWeight_right_add_one_le hproper
    omega⟩

/-- The unshifted right factor in a proper zero-order commutator split. -/
def properSplitRightValue
     :
    ParabolicDerivativeIndex d (M + 1) :=
  ⟨gamma.right, by
    have hloss := gamma.parabolicWeight_right_add_one_le hproper
    omega⟩



/-- The proper one-velocity right factor has the prescribed underlying index. -/
@[simp] theorem coe_properSplitRightVelocity

    (j : Fin d) :
    (properSplitRightVelocity beta gamma hproper j).1 =
      gamma.right + Pi.single (velocityCoord j) 1 :=
  rfl



end ParabolicDerivativeIndex

end HypoellipticAleksandrov.Parabolic
