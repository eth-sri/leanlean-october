module

public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex
public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLeibniz

/-!
# Generic parabolic-index arithmetic

This file provides bounded parabolic indices for source derivatives and for the
two sides of a multi-index split. It also embeds total-order derivative indices
into parabolic-weight derivative indices.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators

namespace TimeVelocityMultiIndex

/- The right side of a split is coordinatewise bounded by the original index. -/
@[simp] theorem Split.order_left_add_order_right {d }
    {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    gamma.left.order + gamma.right.order = beta.order := by
  rw [← order_add, gamma.left_add_right]

/- The parabolic weights of the two sides of a split add to the original weight. -/
@[simp] theorem Split.parabolicWeight_left_add_parabolicWeight_right {d }
    {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    gamma.left.parabolicWeight + gamma.right.parabolicWeight =
      beta.parabolicWeight := by
  rw [← parabolicWeight_add, gamma.left_add_right]

/- The order of the left side of a split is bounded by the original order. -/
theorem Split.order_left_le {d } {beta : TimeVelocityMultiIndex d}
    (gamma : Split beta) : gamma.left.order ≤ beta.order := by
  calc
    gamma.left.order ≤ gamma.left.order + gamma.right.order := Nat.le_add_right _ _
    _ = beta.order := gamma.order_left_add_order_right

/- The parabolic weight of the left side is bounded by the original weight. -/
theorem Split.parabolicWeight_left_le {d }
    {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    gamma.left.parabolicWeight ≤ beta.parabolicWeight := by
  calc
    gamma.left.parabolicWeight ≤
        gamma.left.parabolicWeight + gamma.right.parabolicWeight := Nat.le_add_right _ _
    _ = beta.parabolicWeight := gamma.parabolicWeight_left_add_parabolicWeight_right

/- The parabolic weight of the right side is bounded by the original weight. -/
theorem Split.parabolicWeight_right_le {d }
    {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    gamma.right.parabolicWeight ≤ beta.parabolicWeight := by
  calc
    gamma.right.parabolicWeight ≤
        gamma.left.parabolicWeight + gamma.right.parabolicWeight := Nat.le_add_left _ _
    _ = beta.parabolicWeight := gamma.parabolicWeight_left_add_parabolicWeight_right

end TimeVelocityMultiIndex

namespace ParabolicDerivativeIndex

/- Lower the ambient weight bound using a proof of the sharper actual bound. -/
def restrictLE {d L M } (beta : ParabolicDerivativeIndex d L)
    (hbeta : beta.1.parabolicWeight ≤ M) : ParabolicDerivativeIndex d M :=
  ⟨beta.1, hbeta⟩

/- Restricting the ambient bound does not change the underlying multi-index. -/
@[simp] theorem coe_restrictLE {d L M }
    (beta : ParabolicDerivativeIndex d L)
    (hbeta : beta.1.parabolicWeight ≤ M) :
    (restrictLE beta hbeta).1 = beta.1 := rfl

/- Restriction followed by inclusion recovers the original bounded index. -/
def sourceCast {d L } (beta : ParabolicDerivativeIndex d (L - 2)) :
    ParabolicDerivativeIndex d L := castLE (Nat.sub_le L 2) beta

/- Add one time derivative to a source index. -/
def sourceTime {d L } (hL : 2 ≤ L)
    (beta : ParabolicDerivativeIndex d (L - 2)) : ParabolicDerivativeIndex d L :=
  timeSucc (sourceCast beta) (by
    change beta.1.parabolicWeight + 2 ≤ L
    omega)

/- Add one velocity derivative to a source index. -/
def sourceVelocityTwo {d L } (hL : 2 ≤ L)
    (beta : ParabolicDerivativeIndex d (L - 2)) (j i : Fin d) :
    ParabolicDerivativeIndex d L :=
  ⟨beta.1 + Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1, by
    simp only [TimeVelocityMultiIndex.parabolicWeight_add,
      TimeVelocityMultiIndex.parabolicWeight_single_velocity]
    omega⟩

/- `sourceCast` preserves the underlying multi-index. -/
@[simp] theorem coe_sourceVelocityTwo {d L } (hL : 2 ≤ L)
    (beta : ParabolicDerivativeIndex d (L - 2)) (j i : Fin d) :
    (sourceVelocityTwo hL beta j i).1 =
      beta.1 + Pi.single (velocityCoord j) 1 +
        Pi.single (velocityCoord i) 1 := rfl

/- Regard the left side of a split as a bounded parabolic derivative index. -/
def splitLeft {d L } (beta : ParabolicDerivativeIndex d L)
    (gamma : TimeVelocityMultiIndex.Split beta.1) :
    ParabolicDerivativeIndex d L :=
  ⟨gamma.left, gamma.parabolicWeight_left_le.trans beta.2⟩

/- Regard the right side of a split as a bounded parabolic derivative index. -/
def splitRight {d L } (beta : ParabolicDerivativeIndex d L)
    (gamma : TimeVelocityMultiIndex.Split beta.1) :
    ParabolicDerivativeIndex d L :=
  ⟨gamma.right, gamma.parabolicWeight_right_le.trans beta.2⟩

@[simp] theorem coe_splitLeft {d L } (beta : ParabolicDerivativeIndex d L)
    (gamma : TimeVelocityMultiIndex.Split beta.1) :
    (splitLeft beta gamma).1 = gamma.left := rfl

@[simp] theorem coe_splitRight {d L } (beta : ParabolicDerivativeIndex d L)
    (gamma : TimeVelocityMultiIndex.Split beta.1) :
    (splitRight beta gamma).1 = gamma.right := rfl

end ParabolicDerivativeIndex

namespace TimeVelocityDerivativeIndex

/- Embed a total-order index of bound `m` into parabolic-weight bound `2 * m`. -/
def toParabolic {d m } (beta : TimeVelocityDerivativeIndex d m) :
    ParabolicDerivativeIndex d (2 * m) :=
  ⟨beta.1, beta.1.parabolicWeight_le_two_mul beta.2⟩

/- `toParabolic` preserves the underlying multi-index. -/
end TimeVelocityDerivativeIndex

end HypoellipticAleksandrov.Parabolic
