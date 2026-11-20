module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.ClassicalTests
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Tactic

/-! # Admissibility from the localized Aleksandrov estimate

The reduction does not use the dependence of the coefficient on its variables.
Apply the estimate to the difference between a smooth test and a solution;
its positive set is exactly the set in the admissibility inequality.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Parabolic Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {O : Set (KineticPoint d)} {u v : KineticPoint d → ℝ}

section
variable (hu : IsKineticC112On u O) (hv : IsKineticC112On v O) (A : FullKineticCoefficient d)

include hu hv in
private theorem operator_add {P} (hP : P ∈ O) :
    backwardOperator A (fun Q => u Q + v Q) P = backwardOperator A u P + backwardOperator A v P := by
  rw [backwardOperator_apply, comparison_time_add (hu.timeSlice_differentiableAt hP)
    (hv.timeSlice_differentiableAt hP), show kineticPositionGradient (fun Q => u Q + v Q) P =
      kineticPositionGradient u P + kineticPositionGradient v P from classicalGradient_add
        ((hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num))
        ((hv.positionSlice_contDiffAt hP).differentiableAt (by norm_num)),
    comparison_hessian_add (hu.velocitySlice_contDiffAt hP) (hv.velocitySlice_contDiffAt hP)]
  simp only [backwardOperator, PDE.vecDot, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    matrixContraction_add_right]
  ring

include hu in
private theorem operator_neg
    {P} (hP : P ∈ O) : backwardOperator A (fun Q => -u Q) P = -backwardOperator A u P := by
  have h (Q) : -u Q = (-1 : ℝ) * u Q := by simp
  rw [show (fun Q => -u Q) = (fun Q => -1 * u Q) from funext h, backwardOperator_apply,
    show kineticTimeDerivative (fun Q => -1 * u Q) P = -1 * kineticTimeDerivative u P from
      deriv_const_mul _ (hu.timeSlice_differentiableAt hP),
    show kineticPositionGradient (fun Q => -1 * u Q) P = (-1 : ℝ) • kineticPositionGradient u P from
      classicalGradient_const_mul _ ((hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num)),
    kineticVelocityHessian_eq_sliceHessian, sliceHessian_const_mul _ (hu.velocitySlice_contDiffAt hP),
    matrixContraction_smul_right]
  simp [backwardOperator, kineticVelocityHessian_eq_sliceHessian, PDE.vecDot, sub_eq_add_neg]
  abel

include A in
/-- The localized estimate for one coefficient field, exponent and constant. -/
def HasLocalizedEstimate (p C : ℝ) : Prop :=
  ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
    let Q := backwardCylinder P₀ R
    ∀ (f u : KineticPoint d → ℝ), Measurable (fun P : Q => f P) →
      ContinuousOn u (closure Q) → IsKineticC112On u Q →
      (∀ᵐ P ∂(volume.restrict Q), backwardOperator A u P ≤ f P) →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p) (volume.restrict Q) →
      ∀ P ∈ closure Q, u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
        C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
          (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
            (volume.restrict Q)).toReal

end

theorem admissible_of_localized_estimate {A : FullKineticCoefficient d} {lam Lam p C : ℝ}
    (hA : FullElliptic lam Lam A) (hest : HasLocalizedEstimate A p C) (hO : IsOpen O)
    (hu : IsKineticC112On u O) (heq : ∀ᵐ P ∂volume.restrict O, backwardOperator A u P = 0) :
    IsAdmissibleSolution A O p C u := by
  have negReg {S} {w : KineticPoint d → ℝ} (hw : IsKineticC112On w S) : IsKineticC112On (fun Q => -w Q) S := by
    simpa only [neg_one_mul] using comparison_regular_const_mul hw (-1)
  have supersol (w) (hw : IsKineticC112On w O)
      (he : ∀ᵐ P ∂volume.restrict O, backwardOperator A w P = 0) :
      IsAdmissibleSupersolution A O p C w := by
    refine ⟨hw.continuousOn, ?_⟩
    intro P₀ R hR hQ ψ hψ
    have hs := hψ.regular
    have hsub := subset_closure.trans hQ
    have hΨ := comparison_regular_mono hs subset_closure
    have hwQ := comparison_regular_mono hw hsub
    have hn := negReg hwQ
    obtain ⟨hm, hLp⟩ := classical_test_source hA P₀ hR hs (ENNReal.ofReal p)
    have hb := hest P₀ R hR (backwardOperator A ψ) (fun Q => ψ Q + -w Q) hm
      (hs.continuousOn.add (hw.continuousOn.mono hQ).neg) (comparison_regular_add hΨ hn) ?_ hLp
    · apply csSup_le ((backwardCylinder_nonempty P₀ hR).closure.image _)
      rintro _ ⟨P, hP, rfl⟩
      simpa only [Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg, sub_pos, localizedSource] using hb P hP
    · filter_upwards [ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet,
        ae_restrict_of_ae_restrict_of_subset hsub he] with P hP h0
      rw [operator_add hΨ hn A hP, operator_neg hwQ A hP, h0, neg_zero, add_zero]
  refine ⟨supersol u hu heq, supersol (fun Q => -u Q) (negReg hu) ?_⟩
  filter_upwards [ae_restrict_mem hO.measurableSet, heq] with P hP h0
  rw [operator_neg hu A hP, h0, neg_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
