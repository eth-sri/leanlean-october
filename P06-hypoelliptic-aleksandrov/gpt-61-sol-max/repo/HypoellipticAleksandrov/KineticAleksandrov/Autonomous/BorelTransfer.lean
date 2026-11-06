module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousReflection
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarBorelPassage
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateSource
public import PDEFoundation.Calculus.RegularityOrder


/-! # Class-(b) Borel transfer of the conditional autonomous estimate -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Parabolic

/-- Removing source localisation only increases a finite source norm. -/
theorem autonomous_localised_norm_le (P₀ : Point) (R p : ℝ) (hR : 0 < R)
    (u f : Point → ℝ) (hu : ContinuousOn u (backwardCylinder P₀ R))
    (hLp : MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R))) :
    (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R))).toReal ≤
    (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R))).toReal :=
  TheoremA.localized_positive_source_norm_le volume (isOpen_backwardCylinder P₀ R hR)
    u f hu _ hLp

/-- The scalar Borel passage applies with the coefficient-uniform smooth constant. -/
theorem autonomous_borel_of_below_four_density
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
            (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
              (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hsm⟩ := autonomous_smooth_localised_of_below_four_density hdensity
    hH hLE lam Lam hlam hLam p hp
  have hcritical := (criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2
    (by simpa)⟩).1


  refine ⟨C, hC, ?_⟩
  intro a ha hb P₀ R hR u f hcont hreg hf hLp hsub
  exact autonomous_abp_smooth_to_borel lam Lam hlam hLam p (by linarith only [hcritical, hp]) (2 - 6 / p) C false
    (by
        intro a ha hb P₀ R hR u f hcont hreg _hf hLp hsub P hP

        apply (hsm ⟨a, ha, hb⟩ P₀ R hR u f hcont hreg hLp hsub P hP).trans
        apply add_le_add_right
        exact mul_le_mul_of_nonneg_left
          (autonomous_localised_norm_le P₀ R p hR u f hreg.continuousOn hLp)
          (mul_nonneg hC.le (Real.rpow_nonneg hR.le _))) a ha hb P₀ R hR u f hcont hreg hf hLp hsub

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
