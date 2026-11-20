module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsTranslation
import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlock
import HypoellipticAleksandrov.KineticAleksandrov.Decay.FourierDecay
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly

/-! # Full-space Fourier decay and domination of the canonical ball evolution

The evolution and unit-block estimates are proved here; only the two analytic hypotheses
(Hörmander and Lieberman) remain explicit.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open HypoellipticAleksandrov Parabolic SectionTwo Decay Set MeasureTheory

/-- Full-space decay retains every physical starting position, with structural constants
chosen before the coefficient and the supplied realizing kernel. -/
theorem ballExit_full_fourier_decay
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => 0)),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ τ : ℝ) (hστ : σ < τ), ∀ v ξ z : PDE.Vec d,
        ((fourierProjection K (wholeSpaceQuery σ τ hστ.le v z) ξ).variation
          univ).toReal ≤ C * Real.exp (-c * (τ - σ) *
            PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
  have hEvol : IterationEvolutionStatement := exists_terminalEvolution_of_classical
  obtain ⟨C, c, hC, hc, hdecay⟩ := fourier_decay_whole_space_of_unitBlock
    d hd lam Lam hlam hLam hEvol (unit_frequency_block_W hEvol d hd lam Lam hlam hLam)
  refine ⟨C, c, hC, hc, ?_⟩
  intro B hB S K hreal σ τ hστ v ξ z
  have hcov := (iteration_evolution_clauses hEvol hd hlam hLam B hB S K hreal).2.2
  rw [fourierKernel_eq_startingPosition K hcov]
  exact hdecay B hB S K hreal σ τ hστ v ξ (wholeSpaceQuery σ τ hστ.le v 0)
    rfl _ (fourierKernel_spec K σ τ hστ.le ξ v)

/-- A full-space evolution dominates the same canonical ball kernel, by the proved
source domain-monotonicity clause and uniqueness of the realizing ball pair. -/
theorem ballExit_exists_full_evolution
    {d : ℕ} (hd : 1 ≤ d)
    {lam Lam : ℝ} (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R) :
    ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
      (K : MovingFiberKernel (wholeSpace d) (fun _ => 0)),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K ∧
      ∀ q : EvolutionQuery (PDE.euclideanBall v₀ R) (fun _ => 0),
        (localBallKernel hd B hB v₀ hR).master q ≤
          K.master (wholeSpaceQuery q.1.1 q.1.2.1 q.2.1 q.1.2.2.1 q.1.2.2.2) := by
  obtain ⟨S, K, hr, -, hmono, -⟩ :=
    (exists_terminalEvolution_of_classical.timeVelocity hd (wholeSpace_admissible d) B hB).realizes
  refine ⟨S, K, hr, ?_⟩
  have hsub : ∀ σ, movingDomain (PDE.euclideanBall v₀ R) (fun _ => 0) σ ⊆
      movingDomain (wholeSpace d) (fun _ => 0) σ := by
    intro σ
    simp only [movingDomain, PDE.translateSet_zero]
    exact subset_univ _
  have hdom := domainMonotone_of_realizes (zIndependentCoefficient B) (identityDrift d)
    K hmono (PDE.euclideanBall v₀ R) (fun _ => 0) (localBall_admissible v₀ hR)
    (zeroCurve_piecewiseC1 d) hsub (localBallEvolution hd B hB v₀ hR).1
    (localBallKernel hd B hB v₀ hR)
    (localBallEvolution_realizes hd B hB v₀ hR)
  intro q
  exact hdom q

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
