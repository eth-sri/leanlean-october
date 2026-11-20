module

public import HypoellipticAleksandrov.Statements.KineticAleksandrovAutonomousLocalised
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import Mathlib.Tactic

/-!
# Kinetic Aleksandrov estimate for autonomous coefficients (d = 1)

Companion paper, Theorem 1.2: the Aleksandrov estimate for autonomous coefficients above
the exponent threshold. The Hörmander hypoellipticity theorem is supplied by the `hormander`
package and classical Dirichlet solvability (Lieberman, Theorem 5.14) is proved in this
library, so the statement carries no extra hypotheses.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set
open scoped ENNReal

/-- Companion paper, Theorem 1.2: the autonomous scalar Aleksandrov estimate above the threshold
`p_* = 1 + beta_*(Lam / lam)`. -/
theorem kinetic_aleksandrov_autonomous
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint 1) (R : ℝ), 0 < R →
      ∀ (a : ℝ → ℝ → ℝ),
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (f u : KineticPoint 1 → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          autonomousScalarOperator a u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - 6 / p) *
              (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, h⟩ := kinetic_aleksandrov_autonomous_localised lam Lam p hlam hLam hp
  refine ⟨C, hC, ?_⟩
  intro P₀ R hR a hm hb f u hf hc hu hsub hLp P hP
  apply (h P₀ R hR a hm hb f u hf hc hu hsub hLp P hP).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact unlocalize_source_norm (isOpen_backwardCylinder P₀ R hR) hu.continuousOn hLp

end HypoellipticAleksandrov.KineticAleksandrov
