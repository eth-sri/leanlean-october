module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalPoleMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStrip

/-! # Physical nested-strip identities for the actual visit kernels -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Actual physical Green and exit kernels satisfy the nested-strip decomposition. -/
theorem visitUnion_nested
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (s T : ℝ) (hT : s < T)
    (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H1 s T) :
    let rho := (visitUnionExitKernel A H1 s T ∘ₘ mu).restrict
      (finiteUnionInternalExit H1 H2 s T)
    visitUnionGreenKernel A H2 s T ∘ₘ mu =
      visitUnionGreenKernel A H1 s T ∘ₘ mu +
        visitUnionGreenKernel A H2 s T ∘ₘ rho ∧
    visitUnionExitKernel A H2 s T ∘ₘ mu =
      (visitUnionExitKernel A H1 s T ∘ₘ mu).restrict
        (finiteUnionExitSet H2 s T) +
        visitUnionExitKernel A H2 s T ∘ₘ rho := by
  let nu := visitUnionPoleMeasure H1 T mu
  let rho := (visitUnionExitKernel A H1 s T ∘ₘ mu).restrict
    (finiteUnionInternalExit H1 H2 s T)
  have hlarge : ∀ᵐ p ∂mu, p ∈ visitPoleSet H2 s T :=
    hmu.mono (fun p hp => ⟨hp.1, hp.2.1, hsub hp.2.2⟩)
  have hrestart : finiteUnionRestartMeasure A H1 H2 s T nu = rho := by
    unfold finiteUnionRestartMeasure rho nu
    rw [visitUnionExitKernel_comp_poles A H1 s T mu hmu]
  have hrho : ∀ᵐ p ∂rho, p ∈ visitPoleSet H2 s T := by
    rw [← hrestart]
    exact finiteUnionRestartMeasure_ae_valid A H1 H2 s T nu
  have htau : finiteUnionRestartPoleMeasure A H1 H2 s T nu =
      visitUnionPoleMeasure H2 T rho := by
    unfold finiteUnionRestartPoleMeasure visitUnionPoleMeasure
    rw [hrestart]
  have h := strip_nested A H1 H2 hsub s T hT nu
    (visitUnionPoleMeasure_ae_time_gt H1 s T mu hmu)
  dsimp only at h
  change _ ∧ _
  rw [visitUnionPoleMeasure_nested_eq H1 H2 hsub s T mu hmu, htau] at h
  rw [← visitUnionGreenKernel_comp_poles A H2 s T mu hlarge,
    ← visitUnionGreenKernel_comp_poles A H1 s T mu hmu,
    ← visitUnionGreenKernel_comp_poles A H2 s T rho hrho,
    ← visitUnionExitKernel_comp_poles A H2 s T mu hlarge,
    ← visitUnionExitKernel_comp_poles A H1 s T mu hmu,
    ← visitUnionExitKernel_comp_poles A H2 s T rho hrho] at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
