module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockEvolution
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly

/-! # Structural clauses for a supplied interval evolution

The existence theorem produces a second evolution. Uniqueness identifies its kernel with the
supplied realizing kernel, transferring all structural clauses without new premises.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.Parabolic

/- The clauses hold for every kernel realizing the same interval problem. -/
theorem interval_evolution_clauses
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam m Lb a c } (hac : a < c)
    (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (hs : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
    (K )
    (hr : RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K) :
    IsDomainMonotoneEvolution (PDE.oneDimensionalAxisBox a c) stationary
      (zIndependentCoefficient B) b K ∧
    HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K ∧
    IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ K := by
  obtain ⟨S₀, K₀, hr₀, hm, hp, hc⟩ : ∃ (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
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
    let Ω := (PDE.oneDimensionalAxisBox a c)
    have hΩ := (interval_admissible hac)
    have hγ := (zeroCurve_piecewiseC1 1)
    exact exists_unitBlock_evolution (exists_terminalEvolution_of_classical hLE hH)
      (by norm_num) lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b hs Ω stationary hΩ hγ
  have hK := (terminalEvolution_unique (PDE.oneDimensionalAxisBox a c) stationary
    (interval_admissible hac) (zIndependentCoefficient B) b S S₀ K K₀ hr hr₀).2
  subst K₀
  exact ⟨hm, hp, hc⟩

end HypoellipticAleksandrov.KineticAleksandrov.Interval
