module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksContract

/-! # Transfer of the evolution clauses to an arbitrary realizing kernel -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- The authorized evolution premise supplies all structural clauses on the given kernel. -/
theorem iteration_evolution_clauses (hEvol : IterationEvolutionStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) stationary)
    (K : MovingFiberKernel (wholeSpace d) stationary)
    (hreal : RealizesTerminalEvolution (wholeSpace d) stationary MeasurableSet.univ
      (zIndependentCoefficient B) (identityDrift d) S K) :
    IsDomainMonotoneEvolution (wholeSpace d) stationary
      (zIndependentCoefficient B) (identityDrift d) K ∧
    HasParabolicMarginalBundle (wholeSpace d) stationary MeasurableSet.univ
      (zIndependentCoefficient B) K ∧
    IsTranslationCovariantEvolution (wholeSpace d) stationary MeasurableSet.univ K := by
  obtain ⟨hcov, hmono, hmargin⟩ := TerminalEvolutionResult.clauses
    (TerminalEvolutionConclusion.timeVelocity hEvol hd (wholeSpace_admissible d) B hB) hreal
  exact ⟨hmono, hmargin, hcov (fun _ _ _ _ => rfl)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Decay
