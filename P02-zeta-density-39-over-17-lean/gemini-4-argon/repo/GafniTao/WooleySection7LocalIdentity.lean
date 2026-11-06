module
public import GafniTao.WooleySection7ShiftedMoment
public import GafniTao.WooleySection7Coefficient
public import GafniTao.WooleyPadicSeparation
public import GafniTao.WooleySourceMixed

@[expose] public section

/-!
# The local source mixed moment in Wooley Section 7

This file applies the arbitrary-residue equation-(7.17) identity to the
literal residue-class pullbacks occurring in `K^r_{a,b}`.  It is the bridge
from the congruence calculation to equation (7.18).
-/

namespace GafniTao

noncomputable section

/-- The local mixed residue moment is exactly the normalized mixed average
of the two affine pullbacks. -/
theorem wooleySourcePolynomialMixedResidueMoment_eq_pullbackAverage
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (s r p B a b : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : WooleySourceSequence) (xi : ZMod (p ^ a))
    (eta : ZMod (p ^ b)) :
    wooleySourcePolynomialMixedResidueMoment
        phi s r p B a b gamma xi eta =
      wooleySourceNormalizedMixedRealAverage
        (wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
        (wooleyAffinePolynomialSystem phi (p ^ b) (eta.val : ℤ))
        (p ^ B) (wooleyTriangular r) (s - wooleyTriangular r)
        (wooleyAffinePullback gamma (p ^ a)
          (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) a) (xi.val : ℤ))
        (wooleyAffinePullback gamma (p ^ b)
          (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) b) (eta.val : ℤ)) := by
  unfold wooleySourcePolynomialMixedResidueMoment
    wooleySourceNormalizedMixedRealAverage
  simp_rw [wooleySourceNormalizedPolynomialSum_affinePullback]
  simp

/-- The exact outer average left after substituting Corollary 3.2 into
equation (7.18).  It retains the conditioned lower-degree mean and the
right-hand source factor pointwise in `alpha`. -/
def wooleySection7ConditionedInsertedAverage {k r : ℕ}
    (leftPhi rightPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (q qPrime qH R S : ℕ) [NeZero q] [NeZero qPrime] [NeZero qH]
    (left right : WooleySourceSequence) : ℝ :=
  ((((q ^ k : ℕ) : ℝ))⁻¹) *
    ∑ alpha : Fin k → ZMod q,
      wooleySourcePolynomialConditionedMean R qPrime qH Psi
          (wooleySourceTwist left
            (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
        ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^ (2 * S)

/-- Equation (7.19) after integration in the outer frequency: any uniform
pointwise lower-degree concentration estimate yields the corresponding
bound for the literal inserted average. -/
theorem wooley_equation_7_19_outer_native
    {k r q qPrime qH R S : ℕ}
    [NeZero q] [NeZero qPrime] [NeZero qH]
    (leftPhi rightPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (left right : WooleySourceSequence)
    (C loss : ℝ)
    (hpoint : ∀ alpha : Fin k → ZMod q,
      wooleySourcePolynomialMean R qPrime Psi
          (wooleySourceTwist left
            (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) ≤
        C * loss *
          wooleySourcePolynomialConditionedMean R qPrime qH Psi
            (wooleySourceTwist left
              (fun n => wooleySourcePolynomialPhase leftPhi alpha n))) :
    wooleySourceInsertedNormalizedRealAverage
        leftPhi rightPhi Psi q qPrime R S left right ≤
      C * loss * wooleySection7ConditionedInsertedAverage
        leftPhi rightPhi Psi q qPrime qH R S left right := by
  unfold wooleySourceInsertedNormalizedRealAverage
    wooleySection7ConditionedInsertedAverage
  have hscale : 0 ≤ ((((q ^ k : ℕ) : ℝ))⁻¹) := by positivity
  calc
    ((((q ^ k : ℕ) : ℝ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          wooleySourcePolynomialMean R qPrime Psi
              (wooleySourceTwist left
                (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
            ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^ (2 * S) ≤
      ((((q ^ k : ℕ) : ℝ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          (C * loss *
            wooleySourcePolynomialConditionedMean R qPrime qH Psi
              (wooleySourceTwist left
                (fun n => wooleySourcePolynomialPhase leftPhi alpha n))) *
            ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^ (2 * S) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      apply Finset.sum_le_sum
      intro alpha halpha
      exact mul_le_mul_of_nonneg_right (hpoint alpha) (by positivity)
    _ = ((((q ^ k : ℕ) : ℝ))⁻¹) * (C * loss) *
        (∑ alpha : Fin k → ZMod q,
          wooleySourcePolynomialConditionedMean R qPrime qH Psi
              (wooleySourceTwist left
              (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
            ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^
              (2 * S)) := by
      have hsum :
          (∑ alpha : Fin k → ZMod q,
            (C * loss *
              wooleySourcePolynomialConditionedMean R qPrime qH Psi
                (wooleySourceTwist left
                  (fun n => wooleySourcePolynomialPhase leftPhi alpha n))) *
              ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^
                (2 * S)) =
            (C * loss) *
              ∑ alpha : Fin k → ZMod q,
                wooleySourcePolynomialConditionedMean R qPrime qH Psi
                    (wooleySourceTwist left
                      (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
                  ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^
                    (2 * S) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro alpha halpha
        ring
      rw [hsum]
      ring
    _ = C * loss *
        (((((q ^ k : ℕ) : ℝ))⁻¹) *
          ∑ alpha : Fin k → ZMod q,
            wooleySourcePolynomialConditionedMean R qPrime qH Psi
                (wooleySourceTwist left
                  (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
              ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^
                (2 * S)) := by ring


