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

/- Every nonempty bounded open interval is an admissible evolution domain. -/
theorem interval_admissible {a c } (hac : a < c) :
    IsAdmissibleEvolutionDomain (PDE.oneDimensionalAxisBox a c) :=
  Or.inr (Or.inr ⟨rfl, a, c, hac, rfl⟩)

/- Literal case-I geometry; the transport conditions are in `SourceSetting`. -/
theorem sourceCase_interval {a c } (hac : a < c)
    (b : PDE.Vec 1 → PDE.Vec 1) (m Lb : ℝ) :
    SourceCase (PDE.oneDimensionalAxisBox a c) b m Lb :=
  Or.inr ⟨rfl, a, c, hac, rfl⟩

/- Assemble the source interval setting from exactly its coefficient and transport data. -/
theorem sourceSetting_interval {a c lam Lam m Lb } (hac : a < c)
    (B : CoefficientField 1) (b )
    (hB : IsSectionTwoCoefficient lam Lam B) (hb : IsSmoothDrift b)
    (hm : 0 < m) (hmLb : m ≤ Lb) (htransport : HasTransportBounds m Lb b) :
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b :=
  ⟨hB, hb, hm, hmLb, htransport, sourceCase_interval hac b m Lb⟩

/- The interval source coefficients supply evolution on every admitted moving domain.
Only Hörmander's theorem and Lieberman's Theorem 5.14 are assumed; no evolution theorem is. -/
end HypoellipticAleksandrov.KineticAleksandrov.Interval
