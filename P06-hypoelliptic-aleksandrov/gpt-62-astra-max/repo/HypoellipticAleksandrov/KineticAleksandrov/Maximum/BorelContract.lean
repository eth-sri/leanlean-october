module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelExhaustionNorm

/-! # The exact uniform smooth estimate and the two source norm choices -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic MeasureTheory Set

variable {d : ℕ} (lam Lam p alpha C₀ : ℝ) (localised : Bool) (u f : KineticPoint d → ℝ)
    {e : KineticPoint d → ℝ} (P : KineticPoint d)

include localised u f in
/-- The source permits either the full positive part or its positive-solution localisation. -/
abbrev borelSource :
    KineticPoint d → ℝ :=
  if localised then {P | 0 < u P}.indicator (fun P => max (f P) 0)
  else fun P => max (f P) 0

include d lam Lam p alpha C₀ localised in
/-- The source smooth estimate, with its constant fixed before coefficient and cylinder. -/
abbrev BorelSmoothEstimate : Prop :=
  ∀ A : CoefficientField d,
    IsSmoothCoefficient A → IsSymmetricCoefficient A →
    HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
    ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
    ∀ u f : KineticPoint d → ℝ,
    ContinuousOn u (closure (backwardCylinder P₀ R)) →
    IsKineticC112On u (backwardCylinder P₀ R) →
    Measurable f → MemLp (fun P => max (f P) 0)
      (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) →
    (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
      backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
    ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
      C₀ * R ^ alpha * (eLpNorm (borelSource localised u f)
        (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R))).toReal

/-- Both source variants are nonnegative pointwise. -/
theorem borelSource_nonneg : 0 ≤ borelSource localised u f P := by
  cases localised
  · exact le_max_right _ _
  · by_cases h : 0 < u P
    · simpa [borelSource, indicator_of_mem (show P ∈ {z | 0 < u z} from h)] using
        (le_max_right (f P) 0)
    · simp [borelSource, indicator_of_notMem (show P ∉ {z | 0 < u z} from h), le_refl]

/-- A nonnegative additive error changes either source variant by at most that error. -/
theorem borelSource_error_le (he : 0 ≤ e P) :
    |borelSource localised u (f + e) P - borelSource localised u f P| ≤ e P := by
  have hscalar : |max (f P + e P) 0 - max (f P) 0| ≤ e P := by
    grind
  cases localised
  · exact hscalar
  · by_cases h : 0 < u P
    · simpa [borelSource, indicator_of_mem (show P ∈ {z | 0 < u z} from h)] using
        hscalar
    · simp [borelSource, indicator_of_notMem (show P ∉ {z | 0 < u z} from h), he]

end HypoellipticAleksandrov.KineticAleksandrov
