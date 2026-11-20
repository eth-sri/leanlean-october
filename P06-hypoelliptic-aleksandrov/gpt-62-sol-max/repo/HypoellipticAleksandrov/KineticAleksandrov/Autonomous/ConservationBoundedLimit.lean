module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ConservationBoundedCutoff
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity

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
    {lam Lam : ℝ} 
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
  refine exists_classical_limit_of_quadratic_data_tail A.positive one_pos
    autonomousWholeDomain (fun _ => 0) (evolutionCoefficient A.a) (identityDrift 1)
    autonomousWholeDomain_admissible (zeroCurve_piecewiseC1 1) (evolutionCoefficient_smooth A)
    (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A) (identityDrift_smooth 1)
    (identityDrift_bounds 1).1 (identityDrift_bounds 1).2 τ (boundedConservationDatum F) F
    C (2 * C) hC0 (by positivity) (fun _ _ hNM => boundedConservationDatum_sub F hC0 hC hNM) ?_ u hu hbd
  intro x
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max ‖x.1‖ ‖x.2‖)
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hn : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  have hy := (le_max_left ‖x.1‖ ‖x.2‖).trans hN₀
  have hz := (le_max_right ‖x.1‖ ‖x.2‖).trans hN₀
  change F x = F x * (zCutoffN 1 N x.1 * zCutoffN 1 N x.2)
  rw [zCutoffN_eq_one (by linarith [hy]), zCutoffN_eq_one (by linarith [hz]), mul_one, mul_one]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
