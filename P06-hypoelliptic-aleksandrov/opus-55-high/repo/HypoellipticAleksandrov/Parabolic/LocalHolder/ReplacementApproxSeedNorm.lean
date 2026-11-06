module

public import HypoellipticAleksandrov.Parabolic.ParabolicW12WeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2Norm
import Mathlib.Tactic.Ring

/-! # Finite-family energy from the actual selected weak jet

The estimate accounts for every low-order representative, including time and all ordered
spatial Hessian entries.
-/

@[expose] public section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory
open scoped BigOperators

/-- Uniform bounds on the literal selected jet bound its complete weight-two family. -/
theorem squaredL2Norm_classical_seed_le {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (J : ParabolicW12Function d U 2) (B : ℝ)
    (hq : (eLpNorm J.toFun 2 (timeVelocityVolumeOn U)).toReal ^ 2 ≤ B)
    (ht : (eLpNorm J.timeDeriv 2 (timeVelocityVolumeOn U)).toReal ^ 2 ≤ B)
    (hg : ∀ i, (eLpNorm (fun z => J.velocityGrad z i) 2
      (timeVelocityVolumeOn U)).toReal ^ 2 ≤ B)
    (hh : ∀ i j, (eLpNorm (fun z => J.velocityHessian z i j) 2
      (timeVelocityVolumeOn U)).toReal ^ 2 ≤ B) :
    (J.toWeakDerivativeFamily hU).squaredL2Norm ≤
      (Fintype.card (ParabolicDerivativeIndex d 2) : ℝ) * B := by
  calc
    _ ≤ ∑ _beta : ParabolicDerivativeIndex d 2, B := by
      apply Finset.sum_le_sum
      intro beta _
      change (eLpNorm
        (match ParabolicDerivativeIndex.equivLowOrderClass d beta with
          | .zero => J.toFun
          | .time => J.timeDeriv
          | .velocity i => fun z => J.velocityGrad z i
          | .velocity₂ i j _ => fun z => J.velocityHessian z i j)
        2 _).toReal ^ 2 ≤ B
      aesop
    _ = _ := by simp

end HypoellipticAleksandrov.Parabolic.LocalHolder
