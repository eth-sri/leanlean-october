module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionTerminalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitCanonical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierCollar
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionComparison
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.CaseW

/-! # Identifying genuine terminal probes in the actual local boundary measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic TheoremA

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/- Terminal interior probes see exactly the actual valid-state transition measure. -/
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
  have hur : ContDiffOn ℝ (⊤ : ℕ∞)
      ((u ∘ sectionTwoPoint) ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' localStrip (P.1.time) T v₀ R) ∧
    ContinuousOn (u ∘ sectionTwoPoint) (localClosedStrip (P.1.time) T v₀ R) ∧
    (∃ M : ℝ, ∀ Q ∈ localClosedStrip (P.1.time) T v₀ R, |u (sectionTwoPoint Q)| ≤ M) ∧
    ∀ Q ∈ localStrip (P.1.time) T v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) (u ∘ sectionTwoPoint) Q = 0 := by
    let a := (P.1.time)
    have hswap : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : ℝ × PDE.Vec d × PDE.Vec d => (q.1, q.2.2, q.2.1)) :=
      contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst)
    have hm : MapsTo (fun q : ℝ × PDE.Vec d × PDE.Vec d => (q.1, q.2.2, q.2.1))
        ((KineticPoint.equivProd d) '' localStrip a T v₀ R)
        (evolutionPastInteriorRaw (PDE.euclideanBall v₀ R) (fun _ => 0) T) := by
      rintro q ⟨Q, hQ, rfl⟩
      change Q.time < T ∧ Q.velocity ∈ movingDomain (PDE.euclideanBall v₀ R)
        (fun _ => 0) Q.time
      exact ⟨hQ.2.1, by simpa only [movingDomain_ball_zero] using hQ.2.2⟩
    refine ⟨hu.2.2.1.comp hswap.contDiffOn hm, ?_, ?_, ?_⟩
    · exact hu.2.1.comp (continuous_sectionTwoPoint d).continuousOn
        (fun Q hQ => exit_closed_into_past hQ)
    · obtain ⟨M, _, hM⟩ := hu.1
      exact ⟨M, fun Q hQ => hM _ (exit_closed_into_past hQ)⟩
    · intro Q hQ
      rw [forwardKineticOperator_eq_lop_identity]
      change transportedForwardOperator (zIndependentCoefficient B) (identityDrift d)
        ((u ∘ sectionTwoPoint) ∘ sectionTwoPoint) (sectionTwoPoint Q) = 0
      have heq : (u ∘ sectionTwoPoint) ∘ sectionTwoPoint = u := by
        funext p
        rfl
      rw [heq]
      have _h_inl_8 : sectionTwoPoint Q ∈ evolutionPastOpenCylinder (PDE.euclideanBall v₀ R)
        (fun _ => 0) T := by
          exact ⟨hQ.2.1, by simpa only [sectionTwoPoint, movingDomain_ball_zero] using hQ.2.2⟩

        /- A genuine classical terminal solution retains all local physical regularity and bounds. -/
      exact hu.2.2.2.1 _ _h_inl_8
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
    (hreal.2.1 P.1.time T.1 T.2.le (ballStartState P) (terminalStateDatum F))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
