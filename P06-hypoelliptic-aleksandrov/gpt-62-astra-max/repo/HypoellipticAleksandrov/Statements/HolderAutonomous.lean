module

public import HypoellipticAleksandrov.Statements.KineticAleksandrovAutonomousLocalised
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibilityGeometry
public import Mathlib.Tactic

/-!
# Hölder continuity for autonomous coefficients (d = 1)

Companion paper, Corollary 9.10. The Hörmander hypoellipticity theorem is supplied by the
`hormander` package and classical Dirichlet solvability (Lieberman, Theorem 5.14) is proved
in this library, so the statement carries no extra hypotheses.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Holder
open scoped MatrixOrder

/-- Companion paper, Corollary 9.10. -/
theorem kinetic_holder_autonomous
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ a : ℝ → ℝ → ℝ,
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (Omega : Set (KineticPoint 1)), IsOpen Omega →
      ∀ (u : KineticPoint 1 → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), autonomousScalarOperator a u P = 0) →
      ∀ (K : Set (KineticPoint 1)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  have hp := (Autonomous.criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2 (by simpa using hLam)⟩).2
  change 1 + bellmanAdjointExponent _ _ < 4 at hp
  obtain ⟨C₀, _, hest⟩ := kinetic_aleksandrov_autonomous_localised lam Lam 6 hlam hLam (hp.trans (by norm_num))
  obtain ⟨α, C, hα, hα1, h⟩ := kinetic_holder_of_aleksandrov_aux 1 le_rfl lam Lam 6 C₀ hlam hLam (by norm_num)
  refine ⟨α, C, hα, hα1, ?_⟩
  intro a hm hb Ω hΩ u hbounded hu he
  have hE := Autonomous.fullElliptic_of_bounds hm hb
  apply h _ hE.1 hE.2.1 hE.2.2.1 hE.2.2.2 Ω hΩ u hbounded
  refine admissible_of_localized_estimate hE ?_ hΩ hu ?_
  · dsimp only [HasLocalizedEstimate]
    intro P R hR f w hf hc hw hsub hLp
    simp only [Nat.cast_one, mul_one, show (4 : ℝ) + 2 = 6 by norm_num] 
    simp only [Autonomous.backwardOperator_autonomous] at hsub
    exact hest P R hR a hm hb f w hf hc hw hsub hLp
  · simpa only [Autonomous.backwardOperator_autonomous] using he

end HypoellipticAleksandrov.KineticAleksandrov
