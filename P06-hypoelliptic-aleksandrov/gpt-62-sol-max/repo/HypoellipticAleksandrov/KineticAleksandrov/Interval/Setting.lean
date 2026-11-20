module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly

/-! # The bounded-interval source setting and its supplied evolution

Bounded intervals are already admissible in the terminal evolution theorem.
This specialization retains the shared kernel, composition, covariance and marginal witnesses.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- A bounded interval with coefficients and a realizing stationary evolution. -/
structure IntervalEvolution (lam Lam m Lb : ℝ) where
  left : ℝ
  right : ℝ
  lt : left < right
  coefficient : CoefficientField 1
  drift : PDE.Vec 1 → PDE.Vec 1
  setting : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox left right) coefficient drift
  measurableSet : MeasurableSet (PDE.oneDimensionalAxisBox left right)
  operator : TerminalOperatorFamily (PDE.oneDimensionalAxisBox left right) stationary
  kernel : MovingFiberKernel (PDE.oneDimensionalAxisBox left right) stationary
  realizes : RealizesTerminalEvolution (PDE.oneDimensionalAxisBox left right) stationary measurableSet
    (zIndependentCoefficient coefficient) drift operator kernel

abbrev IntervalEvolution.domain {lam Lam m Lb : ℝ} (E : IntervalEvolution lam Lam m Lb) :=
  PDE.oneDimensionalAxisBox E.left E.right

abbrev IntervalEvolution.length {lam Lam m Lb : ℝ} (E : IntervalEvolution lam Lam m Lb) :=
  E.right - E.left

section
variable {a c : ℝ} (hac : a < c)
include hac

/-- Every nonempty bounded open interval is an admissible evolution domain. -/
theorem interval_admissible :
    IsAdmissibleEvolutionDomain (PDE.oneDimensionalAxisBox a c) :=
  Or.inr (Or.inr ⟨rfl, a, c, hac, rfl⟩)

/-- Literal case-I geometry; the transport conditions are in `SourceSetting`. -/
theorem sourceCase_interval
    (b : PDE.Vec 1 → PDE.Vec 1) (m Lb : ℝ) :
    SourceCase (PDE.oneDimensionalAxisBox a c) b m Lb :=
  Or.inr ⟨rfl, a, c, hac, rfl⟩

end

/-- Assemble the source interval setting from exactly its coefficient and transport data. -/
theorem sourceSetting_interval {a c lam Lam m Lb : ℝ} (hac : a < c)
    (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (hB : IsSectionTwoCoefficient lam Lam B) (hb : IsSmoothDrift b)
    (hm : 0 < m) (hmLb : m ≤ Lb) (htransport : HasTransportBounds m Lb b) :
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b :=
  ⟨hB, hb, hm, hmLb, htransport, sourceCase_interval hac b m Lb⟩

section
variable (lam Lam m Lb a c : ℝ)

/-- The interval source coefficients supply evolution on every admitted moving domain.
Only Hörmander's theorem and Lieberman's Theorem 5.14 are assumed; no evolution theorem is. -/
theorem exists_interval_setting_evolution (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (hs : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b)
    (Ω : Set (PDE.Vec 1)) (γ : ℝ → PDE.Vec 1)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ) :
    ∃ (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ),
      RealizesTerminalEvolution Ω γ (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
        (zIndependentCoefficient B) b S K ∧
      IsDomainMonotoneEvolution Ω γ (zIndependentCoefficient B) b K ∧
      HasParabolicMarginalBundle Ω γ (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
        (zIndependentCoefficient B) K ∧
      IsTranslationCovariantEvolution Ω γ
        (measurableSet_of_isAdmissibleEvolutionDomain hΩ) K := by
  exact exists_unitBlock_evolution (exists_terminalEvolution_of_classical )
    (by norm_num) lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b hs Ω γ hΩ hγ

/-- Stationary interval evolution with all its structural clauses on the same kernel. -/
theorem exists_interval_evolution (hac : a < c)
    (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (hs : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b) :
    ∃ (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary
        (measurableSet_of_isAdmissibleEvolutionDomain (interval_admissible hac))
        (zIndependentCoefficient B) b S K ∧
      IsDomainMonotoneEvolution (PDE.oneDimensionalAxisBox a c) stationary
        (zIndependentCoefficient B) b K ∧
      HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary
        (measurableSet_of_isAdmissibleEvolutionDomain (interval_admissible hac))
        (zIndependentCoefficient B) K ∧
      IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c) stationary
        (measurableSet_of_isAdmissibleEvolutionDomain (interval_admissible hac)) K := by
  exact exists_interval_setting_evolution lam Lam m Lb a c B b hs
    (PDE.oneDimensionalAxisBox a c) stationary (interval_admissible hac)
    (zeroCurve_piecewiseC1 1)

end

end HypoellipticAleksandrov.KineticAleksandrov.Interval
