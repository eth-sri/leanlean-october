module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionTerminalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitCanonical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierCollar

/-! # Identifying genuine terminal probes in the actual local boundary measure -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo TheoremA

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- Terminal interior probes see exactly the actual valid-state transition measure. -/
theorem ballExit_terminal_probe_identity
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (F : BoundedBorel (EvolutionAmbientState d))
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall v₀ R) (fun _ => 0) T.1 F) :
    (∫ Q, F (Q.velocity, Q.position)
      ∂(ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T).restrict
        {Q | Q.velocity ∈ PDE.euclideanBall v₀ R}) =
      ∫ w, F w.1 ∂(localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
        (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time T.1 T.2.le
        (ballStartState P) := by
  have hreal := localBallEvolution_realizes hH hLE hd hlam hLam B hB v₀ hR
  obtain ⟨u, hu, hval, _⟩ := hreal.1 T.1 F hF
  have hur := exit_terminal_physical_regular (a := P.1.time) B F u hu
  have hi := ballExit_represents hH hLE hd hlam hLam B hB v₀ hR P T
    (u ∘ sectionTwoPoint) hur.2.1
    (isKineticC112On_of_contDiffOn (isOpen_localStrip _ _ _ _)
      (boundary_physical_smooth_to_native hur.1)) hur.2.2.1 hur.2.2.2
  have hside : MeasurableSet {Q : KineticPoint d | Q.velocity ∈ PDE.euclideanBall v₀ R} :=
    (PDE.isOpen_euclideanBall v₀ R).measurableSet.preimage
      continuous_velocity.measurable
  have heq : (u ∘ sectionTwoPoint) =ᵐ[ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T]
      ({Q | Q.velocity ∈ PDE.euclideanBall v₀ R}.indicator
        (fun Q => F (Q.velocity, Q.position))) := by
    filter_upwards [ballExitRaw_ae_trace hH hLE hd hlam hLam B hB v₀ hR P T] with Q hQ
    by_cases hv : Q.velocity ∈ PDE.euclideanBall v₀ R
    · rw [indicator_of_mem (show Q ∈ {Q | Q.velocity ∈ PDE.euclideanBall v₀ R} from hv)]
      rcases hQ with hQ | hQ
      · exact hu.2.2.2.2.1 _ ⟨hQ.1, by
          simpa only [sectionTwoPoint, movingDomain_ball_zero] using hQ.2⟩
      · exact False.elim ((mem_interior_iff_notMem_frontier hv).mp
          ((PDE.isOpen_euclideanBall v₀ R).interior_eq.symm ▸ hv) hQ.2.2)
    · rw [indicator_of_notMem
        (show Q ∉ {Q | Q.velocity ∈ PDE.euclideanBall v₀ R} from hv)]
      have hl : Q.velocity ∈ frontier (PDE.euclideanBall v₀ R) := by
        rcases hQ with hQ | hQ
        · exact ⟨hQ.2, by
            simpa only [(PDE.isOpen_euclideanBall v₀ R).interior_eq] using hv⟩
        · exact hQ.2.2
      have ht : Q.time ≤ T.1 := by rcases hQ with hQ | hQ <;> grind
      exact hu.2.2.2.2.2 _ ⟨ht, by
        simpa only [sectionTwoPoint, movingDomain_ball_zero] using hl⟩
  rw [← integral_indicator hside]
  rw [← integral_congr_ae heq, ← hi]
  exact (hval P.1.time T.2.le (ballStartState P)).trans
    (hreal.2.1 P.1.time T.1 T.2.le _ _)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
