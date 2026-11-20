module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.LocalisedAutonomous
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibilitySource
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import Mathlib.Tactic

/-! # Uniform autonomous admissibility at exponent six -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov Parabolic Autonomous Holder Set MeasureTheory
open scoped ENNReal

/-- The localized autonomous estimate gives a uniform admissibility constant before all
coefficient, domain and solution data, conditional on the exact density assertion. -/
theorem autonomous_admissibility_of_below_four_density
    (hdensity : Autonomous.BelowFourDensityStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C_A : ℝ,
      ∀ a : ℝ → ℝ → ℝ,
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ Omega : Set (KineticPoint 1), IsOpen Omega →
      ∀ u : KineticPoint 1 → ℝ,
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), autonomousScalarOperator a u P = 0) →
        IsAdmissibleSolution
          (fun _ x v => fun _ _ => a (x 0) (v 0)) Omega 6 C_A u := by
  have hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)) < 6 := by
    have hc := (criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)⟩).2
    change 1 + bellmanAdjointExponent _ _ < 4 at hc
    linarith only [hc]
  obtain ⟨C_A, _hC, hestimate⟩ :=
    kinetic_aleksandrov_autonomous_localised_relative_of_below_four_density
      hdensity lam Lam 6 hlam hLam hp
  refine ⟨C_A, ?_⟩
  intro a ha hb Omega hOmega u _hbounded hu heq
  exact autonomous_admissible_of_localised hlam ha hb
    (fun P₀ R hR => hestimate P₀ R hR a ha hb) hOmega hu heq

end HypoellipticAleksandrov.KineticAleksandrov
