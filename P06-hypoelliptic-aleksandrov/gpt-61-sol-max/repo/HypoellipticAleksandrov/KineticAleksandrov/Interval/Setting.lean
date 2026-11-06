module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly

/-! # The bounded-interval source setting and its supplied evolution

Bounded intervals are already admissible in the terminal evolution theorem.
This specialization retains the shared kernel, composition, covariance and marginal witnesses.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

section
variable {a c : ℝ} (hac : a < c)

include hac
/-- Every nonempty bounded open interval is an admissible evolution domain. -/
theorem interval_admissible  :
    IsAdmissibleEvolutionDomain (PDE.oneDimensionalAxisBox a c) :=
  Or.inr (Or.inr ⟨rfl, a, c, hac, rfl⟩)

/-- Literal case-I geometry; the transport conditions are in `SourceSetting`. -/
theorem sourceCase_interval
    (b : PDE.VectorField 1) (m Lb : ℝ) :
    SourceCase (PDE.oneDimensionalAxisBox a c) b m Lb :=
  Or.inr ⟨rfl, a, c, hac, rfl⟩
end


/-- Assemble the source interval setting from exactly its coefficient and transport data. -/
theorem sourceSetting_interval {a c lam Lam m Lb : ℝ} (hac : a < c)
    (B : CoefficientField 1) (b : PDE.VectorField 1)
    (hB : IsSectionTwoCoefficient lam Lam B) (hb : IsSmoothDrift b)
    (hm : 0 < m) (hmLb : m ≤ Lb) (htransport : HasTransportBounds m Lb b) :
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b :=
  ⟨hB, hb, hm, hmLb, htransport, sourceCase_interval hac b m Lb⟩

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) (lam Lam m Lb a c : ℝ)

include hH hLE
/-- The interval source coefficients supply evolution on every admitted moving domain.
Only Hörmander's theorem and Lieberman's Theorem 5.14 are assumed; no evolution theorem is. -/
theorem exists_interval_setting_evolution
     (B : CoefficientField 1) (b : PDE.VectorField 1)
    (hs : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b)
    (Ω : PDE.VelocityRegion 1) (γ : ℝ → PDE.Vec 1)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ) : type_of% (exists_unitBlock_evolution (exists_terminalEvolution_of_classical hLE hH)
    (by norm_num) lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b hs Ω γ hΩ hγ) := exists_unitBlock_evolution (exists_terminalEvolution_of_classical hLE hH)
    (by norm_num) lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b hs Ω γ hΩ hγ

/-- Stationary interval evolution with all its structural clauses on the same kernel. -/
theorem exists_interval_evolution
     (hac : a < c)
    (B : CoefficientField 1) (b : PDE.VectorField 1)
    (hs : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b) : type_of% (exists_interval_setting_evolution hH hLE lam Lam m Lb a c B b hs
    (PDE.oneDimensionalAxisBox a c) stationary (interval_admissible hac)
    (zeroCurve_piecewiseC1 1)) := exists_interval_setting_evolution hH hLE lam Lam m Lb a c B b hs
    (PDE.oneDimensionalAxisBox a c) stationary (interval_admissible hac)
    (zeroCurve_piecewiseC1 1)

end HypoellipticAleksandrov.KineticAleksandrov.Interval
