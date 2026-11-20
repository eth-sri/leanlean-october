module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ConservationBoundedCutoff

/-! # Classical regularity of the bounded full-space cutoff limit -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set MeasureTheory Evolution
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology MatrixOrder

/-- The cutoff limit for arbitrary bounded full-space terminal data is an actual classical
solution. Its compact approximating solutions are supplied by the realization. -/
theorem exists_bounded_fullspace_classical_limit
    {lam Lam : ℝ} (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState 1)) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |F x| ≤ C)
    (u : ℕ → KineticPoint 1 → ℝ)
    (hu : ∀ N, IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient A.a) (identityDrift 1) τ (boundedConservationDatum F N) (u N))
    (hbd : ∀ N, ∀ p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ, |u N p| ≤
      C) :
    ∃ V : KineticPoint 1 → ℝ,
      (∀ p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ, Tendsto (fun N => u
        N p) atTop (𝓝 (V p))) ∧
      IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0) (evolutionCoefficient A.a)
        (identityDrift 1) τ F V := by
  apply classical_limit_of_quadratic_tails (isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible) continuous_const hlam
    (evolutionCoefficient_smooth A) (evolutionCoefficient_bounds A) (identityDrift_smooth 1) one_pos (identityDrift_bounds 1).2 (identityDrift_bounds 1).1
    hC0 (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)) hC0) (boundedConservationDatum_sub F hC0 hC) _ u hu hbd
  intro x
  obtain ⟨k,hk⟩ := exists_nat_ge (max ‖x.1‖ ‖x.2‖)
  filter_upwards [eventually_ge_atTop k] with i hi
  have : (k : ℝ) ≤ i := by exact_mod_cast hi
  change F x * (zCutoffN 1 i x.1 * zCutoffN 1 i x.2) = F x
  rw [zCutoffN_eq_one (show ‖x.1‖ ≤ (i : ℝ)+1 by linarith [le_max_left ‖x.1‖ ‖x.2‖]),
    zCutoffN_eq_one (show ‖x.2‖ ≤ (i : ℝ)+1 by linarith [le_max_right ‖x.1‖ ‖x.2‖]),mul_one,mul_one]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
