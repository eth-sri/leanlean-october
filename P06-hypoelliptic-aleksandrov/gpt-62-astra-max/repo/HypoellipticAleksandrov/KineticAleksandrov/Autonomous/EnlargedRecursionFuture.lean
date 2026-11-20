module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionPoles
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsBoundary

/-! # Strict future support of the actual enlarged exit kernels -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Every actual enlarged exit occurs strictly after its pole time. -/
theorem enlargedVisitExitKernel_ae_time_gt
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ) (p : Point) :
    ∀ᵐ q ∂enlargedVisitExitKernel hH hLE hlam hLam A H T p, p.time < q.time := by
  classical
  change ∀ᵐ q ∂(if hp : p ∈ enlargedVisitPoleSet H T then
    finiteUnionExit hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, hp⟩) else 0), _
  split
  · rename_i hp
    have h : ∀ᵐ q ∂finiteUnionExit hH hLE hlam hLam A H T
        (enlargedVisitPole H T ⟨p, hp⟩), q ∈ finiteUnionExitSet H p.time T := by
      rw [ae_iff]
      exact finiteUnionExit_compl_exit hH hLE hlam hLam A H p.time T
        (enlargedVisitPole H T ⟨p, hp⟩) le_rfl
    apply h.mono
    intro q hq
    rcases hq with hq | hq
    · exact hq.1 ▸ hp.1
    · exact hq.1
  · simp only [ae_zero, Filter.eventually_bot]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
