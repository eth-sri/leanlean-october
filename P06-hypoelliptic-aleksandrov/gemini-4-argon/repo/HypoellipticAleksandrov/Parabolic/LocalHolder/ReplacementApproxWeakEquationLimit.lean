module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxWeakLimit
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxWeakTestingTools
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Parabolic.ParabolicLowOrderIndex
import Mathlib.Tactic.Ring

/-! # Passing homogeneous equations through the common weak subsequence

Coefficient-weighted compact tests preserve the actual time and Hessian equation. All
selected derivatives use the same subsequence.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped BigOperators Topology Matrix.Norms.Elementwise

/- The literal homogeneous residual of a coherent family through at least weight two. -/
def homogeneousWeakFamilyResidual {d L U u} (hL : 2 ≤ L) (A : CoefficientField d)
    (D : ParabolicWeakDerivativeFamily d L U u) (z : TimeVelocity d) : ℝ :=
  D.representative (ParabolicDerivativeIndex.castLE hL
    (ParabolicDerivativeIndex.timeOne d)) z +
  ∑ i, ∑ j, A z.1 z.2 i j * D.representative
    (ParabolicDerivativeIndex.castLE hL (ParabolicDerivativeIndex.velocityTwo j i)) z

/- Testing the literal residual equals the sum of its selected derivative pairings. -/
theorem integral_homogeneousWeakFamilyResidual_mul {d L U u}
    (hL : 2 ≤ L) (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (D : ParabolicWeakDerivativeFamily d L U u)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    (∫ z in U, homogeneousWeakFamilyResidual hL A D z * φ z) =
      (∫ z in U, D.representative (ParabolicDerivativeIndex.castLE hL
        (ParabolicDerivativeIndex.timeOne d)) z * φ z) +
      ∑ i, ∑ j, ∫ z in U, D.representative
        (ParabolicDerivativeIndex.castLE hL (ParabolicDerivativeIndex.velocityTwo j i)) z *
        (A z.1 z.2 i j * φ z) := by
  classical
  have ht := integrableOn_weak_pairing _ φ (D.memLp
    (ParabolicDerivativeIndex.castLE hL (ParabolicDerivativeIndex.timeOne d))) hφ hc
  have hij (i j : Fin d) : IntegrableOn (fun z => D.representative
      (ParabolicDerivativeIndex.castLE hL (ParabolicDerivativeIndex.velocityTwo j i)) z *
      (A z.1 z.2 i j * φ z)) U := by
    exact integrableOn_weak_pairing _ _ (D.memLp _) (((contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)).mul hφ)
      (HasCompactSupport.mul_left hc)
  have heq : (fun z => homogeneousWeakFamilyResidual hL A D z * φ z) =
      (fun z => D.representative (ParabolicDerivativeIndex.castLE hL
        (ParabolicDerivativeIndex.timeOne d)) z * φ z + ∑ i, ∑ j,
        D.representative (ParabolicDerivativeIndex.castLE hL
          (ParabolicDerivativeIndex.velocityTwo j i)) z * (A z.1 z.2 i j * φ z)) := by
    funext z
    simp only [homogeneousWeakFamilyResidual, add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, integral_add ht (integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hij i j))),
    integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hij i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hij _ j)]

/- A common weak testing limit preserves the homogeneous equation almost everywhere. -/
end HypoellipticAleksandrov.Parabolic.LocalHolder
