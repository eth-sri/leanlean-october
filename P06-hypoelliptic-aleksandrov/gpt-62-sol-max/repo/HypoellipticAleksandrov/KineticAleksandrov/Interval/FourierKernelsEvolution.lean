module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Setting

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

/-- The clauses hold for every kernel realizing the same interval problem. -/
theorem IntervalEvolution.clauses
    {lam Lam m Lb : ℝ} (E : IntervalEvolution lam Lam m Lb) :
    IsDomainMonotoneEvolution (E.domain) stationary
      (zIndependentCoefficient E.coefficient) E.drift E.kernel ∧
    HasParabolicMarginalBundle (E.domain) stationary E.measurableSet
      (zIndependentCoefficient E.coefficient) E.kernel ∧
    IsTranslationCovariantEvolution (E.domain) stationary E.measurableSet E.kernel := by
  obtain ⟨S₀, K₀, hr₀, hm, hp, hc⟩ :=
    exists_interval_evolution lam Lam m Lb E.left E.right E.lt E.coefficient E.drift E.setting
  have hK := (terminalEvolution_unique (E.domain) stationary
    (interval_admissible E.lt) (zIndependentCoefficient E.coefficient) E.drift E.operator S₀ E.kernel K₀ E.realizes hr₀).2
  subst K₀
  exact ⟨hm, hp, hc⟩

end HypoellipticAleksandrov.KineticAleksandrov.Interval
