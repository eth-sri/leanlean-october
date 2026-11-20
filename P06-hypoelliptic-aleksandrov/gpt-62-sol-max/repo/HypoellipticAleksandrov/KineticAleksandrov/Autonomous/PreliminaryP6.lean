module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Entrance
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PreliminaryP6Reflection
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothAutonomousP6Statement
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibilitySource
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
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
  apply autonomous_admissible_of_localised hlam A.smooth.continuous.measurable A.bounds _ hO hu heq
  intro P₀ R hR f w _ hf hw hsub hLp
  exact hestimate A P₀ R hR w f hf hw hLp hsub

/-- Smooth autonomous solutions are admissible at exponent six. -/
theorem smoothAutonomousP6_holds (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    SmoothAutonomousP6Statement lam Lam :=
  smoothAutonomousP6_of_entrance entranceStatement_holds lam Lam hlam hLam

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
