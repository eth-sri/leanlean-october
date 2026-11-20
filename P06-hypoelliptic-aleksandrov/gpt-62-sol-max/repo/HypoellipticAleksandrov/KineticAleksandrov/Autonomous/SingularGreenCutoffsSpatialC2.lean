module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsSpatialOperator
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Derived Green identity for actual compact C² spatial tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic SectionTwo Evolution Occupation Set MeasureTheory

/-- Compact C² spatial tests obey the actual full-space Green identity.
Size and operator bounds are derived, and no Green identity is assumed. -/
theorem fullspace_green_spatial_compact_c2
    {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (T : ℝ)
    (F : BoundedBorel (EvolutionAmbientState 1)) (hF : ContDiff ℝ 2 F)
    (hc : HasCompactSupport F) (p : Point) (hp : p.time < T) :
    duhamelPotential E.2 T
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
          (identityDrift 1) (fun q => F (q.position, q.velocity)) q)) p =
      F (p.position, p.velocity) - ∫ x, F x ∂E.2.master
        (wholeSpaceQuery p.time T hp.le p.position p.velocity) := by
  let f := fun q : Point => F (q.position, q.velocity)
  have hf : ContDiff ℝ 2 (f ∘ evolutionHomeomorph 1) := by
    simpa only [f, Function.comp_def, position_evolutionHomeomorph, velocity_evolutionHomeomorph]
      using hF.comp ((diffusedCoord 1).contDiff.prodMk (transportedCoord 1).contDiff)
  let H := fun x : EvolutionAmbientState 1 =>
    transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) f ⟨0, x.1, x.2⟩
  obtain ⟨hHc, hHk⟩ := compact_spatial_generator A F hF hc
  have hstation (q : Point) :
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) f q =
        H (q.position, q.velocity) := by
    have ht (z : Point) : kineticTimeDerivative f z = 0 := by
      exact deriv_const z.time (F (z.position, z.velocity))
    dsimp only [H]
    rw [transportedForwardOperator_apply, transportedForwardOperator_apply, ht, ht]
    rfl
  obtain ⟨M, hMb⟩ := hHc.bounded_above_of_compact_support hHk
  obtain ⟨C, -, hCb⟩ := F.exists_bound
  exact fullspace_green_terminal_c2 A E hE T f
    hf C (max M 0) (le_max_right _ _) (fun q => hCb _)
    (fun q => by
      rw [hstation]
      simpa only [Real.norm_eq_abs] using (hMb (q.position, q.velocity)).trans
        (le_max_left M 0)) F (hc.uniformContinuous_of_continuous hF.continuous)
    (fun _ _ => rfl) p hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
