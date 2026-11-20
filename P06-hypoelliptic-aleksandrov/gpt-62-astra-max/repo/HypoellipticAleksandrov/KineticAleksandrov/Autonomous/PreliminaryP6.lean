module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PreliminaryP6Reflection
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothAutonomousP6Statement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibilityGeometry
import Mathlib.Tactic

/-! # Preliminary autonomous admissibility without return-time estimates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Holder Set MeasureTheory
open scoped ENNReal

/-- Smooth autonomous homogeneous solutions satisfy the preliminary exponent-six comparison. -/
theorem smoothAutonomousP6_of_entrance (hentrance : EntranceStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    SmoothAutonomousP6Statement lam Lam := by
  obtain ⟨C_A, hC, hestimate⟩ := preliminary_backward_abp_of_entrance hentrance
    lam Lam hlam hLam
  refine ⟨C_A, hC, ?_⟩
  intro A O hO u hu heq
  refine admissible_of_localized_estimate (fullElliptic_of_bounds A.smooth.continuous.measurable A.bounds) ?_ hO hu ?_
  · dsimp only [HasLocalizedEstimate]
    intro P R hR f w _ hc hw hsub hLp
    simp only [backwardOperator_autonomous] at hsub
    simpa only [Nat.cast_one, mul_one, show (4 : ℝ) + 2 = 6 by norm_num] using
      hestimate A P R hR w f hc hw hLp hsub
  · simpa only [backwardOperator_autonomous] using heq

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
