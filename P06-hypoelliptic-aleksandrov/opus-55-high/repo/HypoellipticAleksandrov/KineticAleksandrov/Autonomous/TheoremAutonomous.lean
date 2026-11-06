module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BorelTransfer
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.AssemblySource

/-! # Autonomous Aleksandrov theorem conditional only on improved cylinder density

The conclusion and all binders are those of the autonomous Aleksandrov estimate.
The density proposition remains an explicit unproved hypothesis.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set Autonomous TheoremA
open scoped ENNReal

/-- Autonomous theorem relative to the improved density assertion and the
Hörmander and Lieberman theorems; this does not prove the density assertion. -/
theorem kinetic_aleksandrov_autonomous_relative_of_below_four_density
    (hdensity : Autonomous.BelowFourDensityStatement)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simp_all)) < p) :
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
  obtain ⟨C, hC, hborel⟩ := autonomous_borel_of_below_four_density hdensity
    hH hLE lam Lam hlam hLam p hp
  refine ⟨C, hC.le, ?_⟩
  intro P₀ R hR a ha hb f u hf hcont hreg hsub hLp P hP
  have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
  let f₀ := (backwardCylinder P₀ R).indicator f
  have hf₀ : Measurable f₀ := measurable_source_indicator hQ f hf
  have hae := source_indicator_ae_eq hQ f
  have hmax : (fun P => max (f P) 0) =ᵐ[volume.restrict (backwardCylinder P₀ R)]
      (fun P => max (f₀ P) 0) := by
    filter_upwards [hae] with P hP
    grind
  have hLp₀ := hLp.ae_eq hmax
  have hsub₀ : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      autonomousScalarOperator a u P ≤ f₀ P := by
    filter_upwards [hsub, hae] with P hsub hEq
    linarith
  have hbound := hborel a ha hb P₀ R hR u f₀ hcont hreg hf₀ hLp₀ hsub₀ P hP
  simpa only [f₀, eLpNorm_positive_source_indicator hQ] using hbound

end HypoellipticAleksandrov.KineticAleksandrov
