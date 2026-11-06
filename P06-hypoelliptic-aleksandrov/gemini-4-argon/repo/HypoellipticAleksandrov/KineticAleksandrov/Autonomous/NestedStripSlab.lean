module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripExitIdentity

/-! # Closed-slab measurability and actual exit integrability -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- The literal finite physical slab is closed. -/
theorem nested_exit_ae_larger_slab
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus ≤ e.1.time) :
    ∀ᵐ p ∂stripExit hH hLE hlam hLam A H1 T e,
      p ∈ reconstructionClosedSlab H2 sMinus T := by
  have hcl : Icc H1.lo H1.hi ⊆ Icc H2.lo H2.hi := by
    have h := closure_mono hsub
    change closure (Ioo H1.lo H1.hi) ⊆ closure (Ioo H2.lo H2.hi) at h
    rwa [closure_Ioo H1.ordered.ne, closure_Ioo H2.ordered.ne] at h
  filter_upwards [stripExitOfRealization_ae_closed_future hH hlam hLam A H1 _
    (stripEvolution_spec hH hLE hlam hLam A H1) T e] with p hp
  exact ⟨he.trans hp.1, hp.2.1, hcl hp.2.2⟩

/- Continuity and a proved uniform bound on the actual supporting slab imply integrability. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
