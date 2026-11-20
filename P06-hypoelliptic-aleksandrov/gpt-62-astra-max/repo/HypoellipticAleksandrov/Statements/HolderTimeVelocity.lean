module

public import HypoellipticAleksandrov.Statements.KineticAleksandrovTimeVelocityLocalised
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.ClassicalAdmissibility
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelPhaseMeasure
public import Mathlib.Tactic

/-!
# Hölder continuity for time–velocity coefficients

Companion paper, Corollary 9.9. The Hörmander hypoellipticity theorem is supplied by the
`hormander` package and classical Dirichlet solvability (Lieberman, Theorem 5.14) is proved
in this library, so the statement carries no extra hypotheses.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Holder
open scoped MatrixOrder

/-- Companion paper, Corollary 9.9. -/
theorem kinetic_holder_timeVelocity
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : CoefficientField d,
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega),
          backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  let p : ℝ := 2 * (d : ℝ) + 2
  obtain ⟨C₀, _, hest⟩ := kinetic_aleksandrov_timeVelocity_localised d hd lam Lam p hlam hLam (by dsimp [p]; linarith)
  obtain ⟨α, C, hα, hα1, h⟩ := kinetic_holder_of_aleksandrov_aux d hd lam Lam p C₀ hlam hLam (by dsimp [p]; linarith)
  refine ⟨α, C, hα, hα1, ?_⟩
  intro A hA hs hL hU Ω hΩ u hb hu he
  have hE : FullElliptic lam Lam (ofTimeVelocityCoefficient A) :=
    ⟨hA.comp (continuous_time.prodMk continuous_velocity).measurable, fun P => hs P.time P.velocity,
      borel_timeVelocity_ae_lift hL, borel_timeVelocity_ae_lift hU⟩
  exact h _ hE.1 hE.2.1 hE.2.2.1 hE.2.2.2 Ω hΩ u hb
    (admissible_of_localized_estimate hE (fun P R hR => hest P R hR A hA hs hL hU) hΩ hu he)

end HypoellipticAleksandrov.KineticAleksandrov
