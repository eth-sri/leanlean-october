module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Fourier

/-! # Exact authorized conditional inputs for Section 3 iteration

The evolution input is the terminal evolution statement with its structural predicates.
The unit-block input is the unit-block estimate of the companion paper, Proposition 3.9,
including all binder data.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ProbabilityTheory MatrixOrder

/-- The terminal evolution conclusion (companion paper, Proposition 2.1). -/
def IterationEvolutionStatement : Prop := TerminalEvolutionConclusion

/-- The unit-frequency block statement in case W (`D = ℝ^d`), Proposition 3.9.
It is `UnitBlockStatement` restricted to the whole-space domain. -/
def UnitBlockStatementW (d : ℕ) (hd : 1 ≤ d)
    (lam Lam m Lb : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) : Prop :=
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (D : Set (PDE.Vec d)) (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d),
        SourceSetting lam Lam m Lb D B b → D = univ →
      ∀ (hD : MeasurableSet D) (S : TerminalOperatorFamily D stationary)
        (K : MovingFiberKernel D stationary),
        RealizesTerminalEvolution D stationary hD (zIndependentCoefficient B) b S K →
        IsDomainMonotoneEvolution D stationary (zIndependentCoefficient B) b K →
        HasParabolicMarginalBundle D stationary hD (zIndependentCoefficient B) K →
        IsTranslationCovariantEvolution D stationary hD K →
      ∀ (ξ : PDE.Vec d), PDE.vecNormSq ξ = 1 →
      ∀ (σ : ℝ) (v : PDE.Vec d) (hv : v ∈ movingDomain D stationary σ)
        (hL : σ ≤ σ + L) (ν : ComplexMeasure (PDE.Vec d)),
        IsFourierProjection K (movingQuery σ (σ + L) hL v 0 hv) ξ ν → TV ν ≤ 1 - δ

end HypoellipticAleksandrov.KineticAleksandrov.Decay
