module

public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex
public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLeibniz
import Mathlib.Tactic.Bound



/-!
# Generic parabolic-index arithmetic

This file provides bounded parabolic indices for source derivatives and for the
two sides of a multi-index split. It also embeds total-order derivative indices
into parabolic-weight derivative indices.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic



namespace TimeVelocityMultiIndex



variable {d : ℕ} {beta : TimeVelocityMultiIndex d} (gamma : Split beta)

/-- The orders of the two sides of a split add to the order of the original index. -/
@[simp] theorem Split.order_left_add_order_right  :
    gamma.left.order + gamma.right.order = beta.order := by
  rw [← order_add, gamma.left_add_right]

/-- The parabolic weights of the two sides of a split add to the original weight. -/
@[simp] theorem Split.parabolicWeight_left_add_parabolicWeight_right  :
    gamma.left.parabolicWeight + gamma.right.parabolicWeight =
      beta.parabolicWeight := by
  rw [← parabolicWeight_add, gamma.left_add_right]

/-- The order of the left side of a split is bounded by the original order. -/
theorem Split.order_left_le  : gamma.left.order ≤ beta.order := by
  calc
    gamma.left.order ≤ gamma.left.order + gamma.right.order := Nat.le_add_right _ _
    _ = beta.order := gamma.order_left_add_order_right

/-- The parabolic weight of the left side is bounded by the original weight. -/
theorem Split.parabolicWeight_left_le  :
    gamma.left.parabolicWeight ≤ beta.parabolicWeight := by
  calc
    gamma.left.parabolicWeight ≤
        gamma.left.parabolicWeight + gamma.right.parabolicWeight := Nat.le_add_right _ _
    _ = beta.parabolicWeight := gamma.parabolicWeight_left_add_parabolicWeight_right

/-- The parabolic weight of the right side is bounded by the original weight. -/
theorem Split.parabolicWeight_right_le  :
    gamma.right.parabolicWeight ≤ beta.parabolicWeight := by
  calc
    gamma.right.parabolicWeight ≤
        gamma.left.parabolicWeight + gamma.right.parabolicWeight := Nat.le_add_left _ _
    _ = beta.parabolicWeight := gamma.parabolicWeight_left_add_parabolicWeight_right

end TimeVelocityMultiIndex

namespace ParabolicDerivativeIndex

/-- Lower the ambient weight bound using a proof of the sharper actual bound. -/
def restrictLE {d L M : ℕ} (beta : ParabolicDerivativeIndex d L)
    (hbeta : beta.1.parabolicWeight ≤ M) : ParabolicDerivativeIndex d M :=
  ⟨beta.1, hbeta⟩

variable {d L M : ℕ}

/-- Restricting the ambient bound does not change the underlying multi-index. -/
@[simp] theorem coe_restrictLE
    (beta : ParabolicDerivativeIndex d L)
    (hbeta : beta.1.parabolicWeight ≤ M) :
    (restrictLE beta hbeta).1 = beta.1 := rfl



variable {d L : ℕ}

/-- Include a source index of bound `L - 2` into the target bound `L`. -/
def sourceCast  (beta : ParabolicDerivativeIndex d (L - 2)) :
    ParabolicDerivativeIndex d L := castLE (Nat.sub_le L 2) beta

variable (hL : 2 ≤ L) (beta : ParabolicDerivativeIndex d (L - 2))

/-- Add one time derivative to a source index. -/
def sourceTime   : ParabolicDerivativeIndex d L :=
  timeSucc (sourceCast beta) (by
    change beta.1.parabolicWeight + 2 ≤ L
    omega)



/-- Add the ordered pair of velocity derivatives `j`, then `i`, to a source index. -/
def sourceVelocityTwo   (j i : Fin d) :
    ParabolicDerivativeIndex d L :=
  ⟨beta.1 + Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1, by
    simp only [TimeVelocityMultiIndex.parabolicWeight_add,
      TimeVelocityMultiIndex.parabolicWeight_single_velocity]
    omega⟩



section
variable (hL : 2 ≤ L) (beta : ParabolicDerivativeIndex d (L - 2))





/-- The underlying index of `sourceVelocityTwo` has the fixed ordered pair of additions. -/
@[simp] theorem coe_sourceVelocityTwo   (j i : Fin d) :
    (sourceVelocityTwo hL beta j i).1 =
      beta.1 + Pi.single (velocityCoord j) 1 +
        Pi.single (velocityCoord i) 1 := rfl
end


variable (beta : ParabolicDerivativeIndex d L) (gamma : TimeVelocityMultiIndex.Split beta.1)

/-- Regard the left side of a split as a bounded parabolic derivative index. -/
def splitLeft   :
    ParabolicDerivativeIndex d L :=
  ⟨gamma.left, gamma.parabolicWeight_left_le.trans beta.2⟩

/-- Regard the right side of a split as a bounded parabolic derivative index. -/
def splitRight   :
    ParabolicDerivativeIndex d L :=
  ⟨gamma.right, gamma.parabolicWeight_right_le.trans beta.2⟩

/-- `splitLeft` has the left split index as its underlying multi-index. -/
@[simp] theorem coe_splitLeft   :
    (splitLeft beta gamma).1 = gamma.left := rfl

/-- `splitRight` has the right split index as its underlying multi-index. -/
@[simp] theorem coe_splitRight   :
    (splitRight beta gamma).1 = gamma.right := rfl

end ParabolicDerivativeIndex

namespace TimeVelocityDerivativeIndex

/-- Embed a total-order index of bound `m` into parabolic-weight bound `2 * m`. -/
def toParabolic {d m : ℕ} (beta : TimeVelocityDerivativeIndex d m) :
    ParabolicDerivativeIndex d (2 * m) :=
  ⟨beta.1, beta.1.parabolicWeight_le_two_mul beta.2⟩

/-- `toParabolic` preserves the underlying multi-index. -/
@[simp] theorem coe_toParabolic {d m : ℕ}
    (beta : TimeVelocityDerivativeIndex d m) :
    (toParabolic beta).1 = beta.1 := rfl





end TimeVelocityDerivativeIndex

end HypoellipticAleksandrov.Parabolic
