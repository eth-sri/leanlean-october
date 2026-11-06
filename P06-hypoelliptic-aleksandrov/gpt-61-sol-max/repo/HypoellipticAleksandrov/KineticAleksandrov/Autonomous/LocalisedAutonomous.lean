module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BorelTransfer
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.LocalisedSource
public import PDEFoundation.Calculus.RegularityOrder


/-! # Localized autonomous estimate conditional on improved cylinder density

The conclusion and all binders are those of the localized autonomous estimate.
The density proposition remains an explicit unproved hypothesis.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Autonomous TheoremA Parabolic
open scoped ENNReal

/-- The scalar Borel passage applies with the coefficient-uniform smooth constant. -/
theorem autonomous_localised_borel_of_below_four_density
    (hdensity : BelowFourDensityStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (p : ℝ)
    (hp : criticalP ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa)⟩ < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℝ → ℝ),
      Measurable (Function.uncurry a) → (∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (P₀ : Point) (R : ℝ), 0 < R → ∀ (u f : Point → ℝ),
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        autonomousScalarOperator a u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C * R ^ (2 - 6 / p) *
            (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
              (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hsm⟩ := autonomous_smooth_localised_of_below_four_density hdensity
    hH hLE lam Lam hlam hLam p hp
  have hcritical := (criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2
    (by simpa)⟩).1


  refine ⟨C, hC, ?_⟩
  intro a ha hb P₀ R hR u f hcont hreg hf hLp hsub
  exact autonomous_abp_smooth_to_borel lam Lam hlam hLam p (by linarith only [hcritical, hp]) (2 - 6 / p) C true
    (by
        intro a ha hb P₀ R hR u f hcont hreg _hf hLp hsub P hP

        exact (hsm ⟨a, ha, hb⟩ P₀ R hR u f hcont hreg hLp hsub P hP)) a ha hb P₀ R hR u f hcont hreg hf hLp hsub


/-- Localized autonomous estimate relative to the density assertion and the
Hörmander and Lieberman theorems. -/
theorem kinetic_aleksandrov_autonomous_localised_relative_of_below_four_density
    (hdensity : Autonomous.BelowFourDensityStatement)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa)) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint 1) (R : ℝ), 0 < R →
      ∀ (a : ℝ → ℝ → ℝ),
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (f u : HypoellipticAleksandrov.KineticScalarField 1),
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
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hborel⟩ := autonomous_localised_borel_of_below_four_density hdensity
    hH hLE lam Lam hlam hLam p hp
  refine ⟨C, hC.le, ?_⟩
  intro P₀ R hR a ha hb f u hf hcont hreg hsub hLp P hP
  have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
  let f₀ := (backwardCylinder P₀ R).indicator f

  have hae := source_indicator_ae_eq hQ f

  have hLp₀ := hLp.ae_eq (by
      filter_upwards [hae] with P hP
      change max (f P) 0 = max ((backwardCylinder P₀ R).indicator f P) 0
      rw [hP])

  have hbound := hborel a ha hb P₀ R hR u f₀ hcont hreg (measurable_source_indicator hQ f hf) hLp₀ (by
      filter_upwards [hsub, hae] with P hsub hEq
      change autonomousScalarOperator a u P ≤ (backwardCylinder P₀ R).indicator f P
      rw [hEq]
      exact hsub) P hP
  simpa only [f₀, eLpNorm_localized_source_indicator hQ f u] using hbound

end HypoellipticAleksandrov.KineticAleksandrov
