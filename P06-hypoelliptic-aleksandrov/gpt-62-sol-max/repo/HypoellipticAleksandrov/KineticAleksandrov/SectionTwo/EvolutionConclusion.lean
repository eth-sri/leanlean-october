module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization

/-! # The shared terminal evolution conclusion

This proposition preserves every binder and every shared-witness clause of the
terminal evolution statement (companion paper, Proposition 2.1).  The final three clauses use
the definitionally equal realization predicates.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ProbabilityTheory MatrixOrder

/-- The complete terminal evolution package for fixed coefficients and a moving domain. -/
def TerminalEvolutionResult {n : ℕ} (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω) : Prop :=
    ∃ P : TerminalOperatorFamily Ω γ,
      ∃ K : MovingFiberKernel Ω γ,
        (∀ (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)),
          IsSmoothCompactTerminalDatum Ω γ τ F →
            ∃ u : KineticPoint n → ℝ,
              IsClassicalTerminalSolution Ω γ B b τ F u ∧
              (∀ (σ : ℝ) (hστ : σ ≤ τ)
                  (p : EvolutionState Ω γ σ),
                u ⟨σ, p.1.1, p.1.2⟩ =
                  P σ τ hστ (terminalStateDatum F) p) ∧
              (∀ v : KineticPoint n → ℝ,
                IsClassicalTerminalSolution Ω γ B b τ F v →
                  EqOn v u (evolutionPastClosedCylinder Ω γ τ))) ∧
        (∀ (σ : ℝ),
          P σ σ le_rfl =
            (LinearMap.id :
              BoundedBorel (EvolutionState Ω γ σ) →ₗ[ℝ]
                BoundedBorel (EvolutionState Ω γ σ))) ∧
        (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
            (f : BoundedBorel (EvolutionState Ω γ τ)),
          0 ≤ f → 0 ≤ P σ τ hστ f) ∧
        (∀ (σ τ : ℝ) (hστ : σ ≤ τ),
          P σ τ hστ (1 : BoundedBorel (EvolutionState Ω γ τ)) ≤
            (1 : BoundedBorel (EvolutionState Ω γ σ))) ∧
        (∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
          P σ τ (hσr.trans hrτ) =
            (P σ r hσr).comp (P r τ hrτ)) ∧
        (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
            (p : EvolutionState Ω γ σ)
            (f : BoundedBorel (EvolutionState Ω γ τ)),
          P σ τ hστ f p =
            ∫ q, f q ∂(K.fiberKernel
              (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
              σ τ hστ p)) ∧
        (∀ q : EvolutionQuery Ω γ,
          (K.master q).restrict (evolutionStateSet Ω γ q.1.2.1) =
            K.master q) ∧
        (∀ q : EvolutionQuery Ω γ, K.master q Set.univ ≤ 1) ∧
        (∀ (E : Set (EvolutionAmbientState n))
            (hE : MeasurableSet E),
          let _ := hE
          Measurable (fun q : EvolutionQuery Ω γ => K.master q E)) ∧
        (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
            (p : EvolutionState Ω γ σ),
          K.fiberKernel
            (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
            σ τ hστ p Set.univ ≤ 1) ∧
        MovingFiberKernel.HasEndpoint K
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) ∧
        MovingFiberKernel.HasComposition K
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) ∧
        (∀ (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z'),
          let _ := hBz
          IsTranslationCovariantEvolution Ω γ
            (measurableSet_of_isAdmissibleEvolutionDomain hΩ) K) ∧
        IsDomainMonotoneEvolution Ω γ B b K ∧
        HasParabolicMarginalBundle Ω γ
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B K

/-- The extra structural clauses carried by a realizing terminal kernel. -/
abbrev TerminalKernelClauses {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (K : MovingFiberKernel Ω γ) : Prop :=
  (∀ _hBz : ∀ σ y z z', B σ y z = B σ y z',
    IsTranslationCovariantEvolution Ω γ (measurableSet_of_isAdmissibleEvolutionDomain hΩ) K) ∧
  IsDomainMonotoneEvolution Ω γ B b K ∧
  HasParabolicMarginalBundle Ω γ (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B K

/-- Extract realization and the structural clauses from the full evolution result. -/
theorem TerminalEvolutionResult.realizes {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    {hΩ : IsAdmissibleEvolutionDomain Ω} (H : TerminalEvolutionResult Ω γ B b hΩ) :
    ∃ (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ),
      RealizesTerminalEvolution Ω γ (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B b S K ∧
      TerminalKernelClauses B b hΩ K := by
  obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, hcov, hmono, hpar⟩ := H
  exact ⟨S, K, ⟨hc, hi, he, hcomp⟩, hcov, hmono, hpar⟩

/-- The terminal evolution theorem for all admissible problems. -/
def TerminalEvolutionConclusion : Prop :=
∀ (n : ℕ) (hn : 1 ≤ n)
    (lam Lam m L_b : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ L_b)
    (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω)
    (hγ : IsContinuousPiecewiseC1 γ)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (hb_smooth : IsSmoothDrift b)
    (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b),
    let _ := hn
    let _ := hlam
    let _ := hlamLam
    let _ := hm
    let _ := hmLb
    let _ := hγ
    let _ := hB_smooth
    let _ := hB_symm
    let _ := hB_ell
    let _ := hb_smooth
    let _ := hb_lipschitz
    let _ := hb_coercive
    TerminalEvolutionResult Ω γ B b hΩ

/-- Specialize the terminal evolution to a stationary domain with identity drift. -/
theorem TerminalEvolutionConclusion.stationary (H : TerminalEvolutionConclusion)
    {n : ℕ} (hn : 1 ≤ n) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    {Ω : Set (PDE.Vec n)} (hΩ : IsAdmissibleEvolutionDomain Ω) {B : FullKineticCoefficient n}
    (hs : IsSmoothFullKineticCoefficient B) (hy : IsSymmetricFullKineticCoefficient B)
    (he : HasEverywhereLoewnerBounds lam Lam B) :
    TerminalEvolutionResult Ω (fun _ => 0) B (identityDrift n) hΩ :=
  H n hn lam Lam 1 1 hlam hLam one_pos le_rfl Ω (fun _ => 0) B (identityDrift n) hΩ
    (zeroCurve_piecewiseC1 n) hs hy he (identityDrift_smooth n)
    (identityDrift_bounds n).1 (identityDrift_bounds n).2

/-- The stationary-domain evolution for time–velocity coefficients. -/
theorem TerminalEvolutionConclusion.timeVelocity (H : TerminalEvolutionConclusion)
    {n : ℕ} (hn : 1 ≤ n) {lam Lam : ℝ} {Ω : Set (PDE.Vec n)}
    (hΩ : IsAdmissibleEvolutionDomain Ω) (B : CoefficientField n)
    (hB : IsSectionTwoCoefficient lam Lam B) :
    TerminalEvolutionResult Ω (fun _ => 0) (zIndependentCoefficient B) (identityDrift n) hΩ := by
  obtain ⟨hs, hy, he⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  exact H.stationary hn hB.1 hB.2.1 hΩ hs hy he

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
