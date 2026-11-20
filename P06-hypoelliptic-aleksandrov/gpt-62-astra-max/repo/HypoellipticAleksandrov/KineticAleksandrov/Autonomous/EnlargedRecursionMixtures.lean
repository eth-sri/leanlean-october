module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionPoles
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionNested

/-! # Physical nested-strip identities for the actual visit kernels -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

variable (H : FiniteIntervalUnion) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (hsub : H1.carrier ⊆ H2.carrier)
    (s T : ℝ) (hT : s < T) (mu : Measure Point)

/-- A lower-time bound on a physical source survives its subtype pullback. -/
theorem enlargedUnionPoleMeasure_ae_time_ge (hmu : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H T)
    (htime : ∀ᵐ p ∂mu, s ≤ p.time) :
    ∀ᵐ e ∂visitUnionPoleMeasure H T mu, s ≤ e.1.time := by
  have ht : ∀ᵐ p ∂(visitUnionPoleMeasure H T mu).map Subtype.val, s ≤ p.time := by
    rw [enlargedUnionPoleMeasure_map H T mu hmu]
    exact htime
  exact ((MeasurableEmbedding.subtype_coe (measurableSet_finiteUnionPole H T)).ae_map_iff).mp ht

include hsub hT in
/-- Actual physical Green and exit kernels satisfy the nested-strip decomposition. -/
theorem enlargedUnion_nested [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H1 T)
    (htime : ∀ᵐ p ∂mu, s ≤ p.time) :
    let rho := (enlargedVisitExitKernel hlam hLam A H1 T ∘ₘ mu).restrict
      (finiteUnionInternalExit H1 H2 s T)
    enlargedVisitGreenKernel hlam hLam A H2 T ∘ₘ mu =
      enlargedVisitGreenKernel hlam hLam A H1 T ∘ₘ mu +
        enlargedVisitGreenKernel hlam hLam A H2 T ∘ₘ rho ∧
    enlargedVisitExitKernel hlam hLam A H2 T ∘ₘ mu =
      (enlargedVisitExitKernel hlam hLam A H1 T ∘ₘ mu).restrict
        (finiteUnionExitSet H2 s T) +
        enlargedVisitExitKernel hlam hLam A H2 T ∘ₘ rho := by
  let nu := visitUnionPoleMeasure H1 T mu
  let rho := (enlargedVisitExitKernel hlam hLam A H1 T ∘ₘ mu).restrict
    (finiteUnionInternalExit H1 H2 s T)
  have hlarge : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H2 T :=
    hmu.mono (fun p hp => ⟨hp.1, hsub hp.2⟩)
  have hrestart : finiteUnionRestartMeasure hlam hLam A H1 H2 s T nu = rho := by
    unfold finiteUnionRestartMeasure rho nu
    rw [enlargedExitKernel_comp_poles hlam hLam A H1 T mu hmu]
  have hrho : ∀ᵐ p ∂rho, p ∈ enlargedVisitPoleSet H2 T := by
    rw [← hrestart]
    exact (finiteUnionRestartMeasure_ae_valid hlam hLam A H1 H2 s T nu).mono
      (fun p hp => ⟨hp.2.1, hp.2.2⟩)
  have htau : finiteUnionRestartPoleMeasure hlam hLam A H1 H2 s T nu =
      visitUnionPoleMeasure H2 T rho := by
    unfold finiteUnionRestartPoleMeasure visitUnionPoleMeasure
    rw [hrestart]
  have h := enlarged_strip_nested hlam hLam A H1 H2 hsub s T hT nu
    (enlargedUnionPoleMeasure_ae_time_ge H1 s T mu hmu htime)
  dsimp only at h
  rw [enlargedUnionPoleMeasure_nested_eq H1 H2 hsub T mu hmu, htau] at h
  rw [← enlargedGreenKernel_comp_poles hlam hLam A H2 T mu hlarge,
    ← enlargedGreenKernel_comp_poles hlam hLam A H1 T mu hmu,
    ← enlargedGreenKernel_comp_poles hlam hLam A H2 T rho hrho,
    ← enlargedExitKernel_comp_poles hlam hLam A H2 T mu hlarge,
    ← enlargedExitKernel_comp_poles hlam hLam A H1 T mu hmu,
    ← enlargedExitKernel_comp_poles hlam hLam A H2 T rho hrho] at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
